module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0397
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0396
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverTypePrimeChosenAndConj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlacesOverG

theorem isConjPl_cP {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Formalism.BasicNotions.IsConjPl D.host P (GlobalTheory.IdemSupport.cP (D := D) P) := by
  intro x y hxy
  have hy : y = GlobalTheory.IdemSupport.cO D x := by
    apply RingOfIntegers.ext
    rw [hxy, GlobalTheory.IdemSupport.cO_coe]
    exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
  rw [GlobalTheory.IdemSupport.mem_cP, hy, GlobalTheory.IdemSupport.cO_cO]

theorem conjPrime_conjPrime₂ {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) :
    GlobalTheory.IdemSupport.cP (D := D) (GlobalTheory.IdemSupport.cP (D := D) P) = P := by
  apply HeightOneSpectrum.ext
  ext x
  rw [GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.mem_cP, GlobalTheory.IdemSupport.cO_cO]

theorem finrank_E' (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  have h1 : Module.finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h5 : D.R.f = 2 * D.R.ord := rfl
  rw [h1, h5]; ring

theorem places_over_g_k : ∀ (D : D7) (k : Fin 2), Function.Injective (Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v))) ∧ (∀ W : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal ↔ ∃ i, Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)) i = W) ∧ Fintype.card (D.nd.PlG k ⊕ D.nd.PlG k) = Module.finrank ℚ D.host.E := by
  intro D k
  set f := Sum.elim (D.naut.plGw k) (fun v => GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)) with hf
  have hne : ∀ v v', D.naut.plGw k v ≠ GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v') := fun v v' e =>
    D.naut.plGw_nconj k v' v (e ▸ isConjPl_cP _)
  have hinj : Function.Injective f := by
    rintro (a | a) (b | b) e
    · simp only [hf, Sum.elim_inl] at e; rw [D.naut.plGw_inj k e]
    · simp only [hf, Sum.elim_inl, Sum.elim_inr] at e; exact absurd e (hne a b)
    · simp only [hf, Sum.elim_inl, Sum.elim_inr] at e; exact absurd e.symm (hne b a)
    · simp only [hf, Sum.elim_inr] at e
      have := congrArg (GlobalTheory.IdemSupport.cP (D := D)) e
      rw [conjPrime_conjPrime₂, conjPrime_conjPrime₂] at this
      rw [D.naut.plGw_inj k this]
  have hmem : ∀ i, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ (f i).asIdeal := by
    rintro (v | v)
    · exact D.naut.plGw_over k v
    · show _ ∈ (GlobalTheory.IdemSupport.cP (D := D) (D.naut.plGw k v)).asIdeal
      rw [GlobalTheory.IdemSupport.mem_cP, map_natCast]
      exact D.naut.plGw_over k v
  have hcard : Fintype.card (D.nd.PlG k ⊕ D.nd.PlG k) = Module.finrank ℚ D.host.E := by
    rw [Fintype.card_sum, D.nd.card_PlG k, finrank_E', two_mul]
  refine ⟨hinj, fun W => ⟨fun hW => ?_, ?_⟩, hcard⟩
  · have hfin : (Formalism.BasicNotions.placesOver D.host.E (D.host.g k)).Finite := by
      apply Set.finite_of_ncard_ne_zero
      rw [D.nd.g_split k]; exact Module.finrank_pos.ne'
    have hsub : Set.range f ⊆ Formalism.BasicNotions.placesOver D.host.E (D.host.g k) := by
      rintro _ ⟨i, rfl⟩; exact hmem i
    have hle : (Formalism.BasicNotions.placesOver D.host.E (D.host.g k)).ncard ≤ (Set.range f).ncard := by
      rw [D.nd.g_split k, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, hcard]
    have heq := Set.eq_of_subset_of_ncard_le hsub hle hfin
    have : W ∈ Set.range f := by rw [heq]; exact hW
    exact this
  · rintro ⟨i, rfl⟩; exact hmem i

end GlobalTheory.PlacesOverG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceHeckeOperatorEigenvalueConjSpherical
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeEigConj
open GlobalTheory.HeckeEigConj

theorem tN_eig : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ J : Subgroup (GAf L n),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) →
    ∀ (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L))) (α : Fin n → ℂˣ),
    GlobalTheory.SmGL.HasSatake σ.ρ α →
    ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L), Continuous i →
    (∀ x : L, i ((GlobalTheory.HeckeFrob.conjSplit s).i x) = algebraMap L ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) x) →
    ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (T : σ.V →ₗ[ℂ] (GAf L n → W)),
    GlobalTheory.HeckeFrob.IsLocMap (GlobalTheory.HeckeFrob.conjSplit s) σ i T →
    ∀ e ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.SplitWeil.KO ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) (Fin n)),
    ∀ k, 1 ≤ k → k ≤ n →
      ((normV (GlobalTheory.HeckeFrob.conjSplit s).w : ℕ) : ℂ) ^ (k * (k - 1) / 2) • NG.tN J s ϖ k (T e) =
        (GlobalTheory.HeckeFrob.twEig (GlobalTheory.HeckeFrob.conjSplit s).w α).esymm k • T e := by
  intro L _ _ _ n s ϖ hϖ J hJ σ α hα i hi hiL W _ _ T hT e he k hk1 hkn
  classical
  have hK : ∀ a, i a ∈ Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w ↔
      a ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := fun a =>
    GlobalTheory.IsoInteg.valued_le_one_iff_of_continuous (maximalRealSubfield L) L s.v _ i hi a
  have heK : e ∈ GlobalTheory.PRep.fixed σ.ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n) := by
    rw [← GlobalTheory.HeckeEigConj.KO_eq_KGL L (GlobalTheory.HeckeFrob.conjSplit s).w n]; exact he
  have hφK : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ →
      Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n κ) ∈
        GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n := fun κ hκ ht => by
    rw [GlobalTheory.HeckeEigConj.map_loc_conjSplit L n s i κ]
    exact (GlobalTheory.LFun.ConjPlace.mem_iff_invT i hK _).1 ((GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s ht).2 hκ)
  obtain ⟨α0, -, hT0⟩ := GlobalTheory.HeckeScalarSph.exists_tSet_eq (n := n) s ϖ k hϖ
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.HeckeScalarSph.exists_repsU (n := n) s.v α0
  have hR1' : ∀ γ ∈ R, γ ∈ tSet L n s ϖ k := fun γ hγ => (hT0 γ).2 (hR1 γ hγ)
  have hR2' : ∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n := fun x hx => hR2 x ((hT0 x).1 hx)
  have hD : ∀ x ∈ tSet L n s ϖ k, TrivOutside {s.v} x := fun x hx => hx.1
  have hrt : ∀ x, TrivOutside {s.v} x → NG.rt L n x (T e) =
      T (σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n x)) e) :=
    fun x hx => (hT x hx e).symm
  have hfix : ∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ (T e) = T e := fun κ hκ ht => by
    rw [hrt κ ht, GlobalTheory.LGrp.mem_fixed.1 heK _ (hφK κ hκ ht)]
  have hsum := heckeD_eq_sum_of_agree J hJ hD hR1' hR2' hfix
  have hloc := _root_.GlobalTheory.HeckeEigCoset.heckeVec_Tj_inv_conj_eq_sum L n s ϖ hϖ k hkn i hi σ.ρ R hR1' hR2' e heK
  have key : NG.heckeD J (tSet L n s ϖ k) (T e) = T (GlobalTheory.LFun.heckeVec σ.ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)
      (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) e) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, hloc, map_sum]
    exact Finset.sum_congr rfl fun γ hγ => hrt γ (hD γ (hR1' γ hγ))
  obtain ⟨hq1, hq2⟩ := norms_eq s
  by_cases he0 : e = 0
  · subst he0
    simp only [map_zero, smul_zero]
    funext g
    simp [NG.tN, NG.heckeD]
  have hSat := (GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake L (GlobalTheory.HeckeFrob.conjSplit s).w n σ.V σ.ρ α hα).2 e heK he0
  have hU : Formalism.UG.IsUnifV L (GlobalTheory.HeckeFrob.conjSplit s).w (i ϖ) :=
    _root_.GlobalTheory.UnifMap.unif_to_unif (maximalRealSubfield L) L s.v _ i hi ϖ hϖ
  have hinv := (GlobalTheory.ChainOnto.SatInv.satVec_iff_inv L (GlobalTheory.HeckeFrob.conjSplit s).w n σ.V σ.ρ e _ he0 heK
    (by simp)).1 hSat (i ϖ) hU k hkn
  rw [NG.tN, key, hinv, map_smul, smul_smul, smul_smul, hq1, hq2]
  congr 1
  rw [mul_assoc]
  exact _root_.GlobalTheory.SatEigArith.satEig_inv_normalised (normV (GlobalTheory.HeckeFrob.conjSplit s).w) n k
    (Nat.pos_of_ne_zero (hq1 ▸ GlobalTheory.LFun.qV_ne_zero (GlobalTheory.HeckeFrob.conjSplit s).w)) hkn α

end GlobalTheory.HeckeEigConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceResidueMapUnitCharacter
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn.UniMem

open ReciprocityTheory.Aut

theorem mem_GLint_of_entries {K : Type} [Field K] {n : ℕ} (O : Subring K) (g : GL (Fin n) K)
    (h1 : ∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ O)
    (h2 : ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ O) :
    g ∈ Formalism.UG.GLint (Fin n) O := by
  first
  | exact @_root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries
  | exact _root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries
  | (apply _root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries <;> assumption)
  | (intros; apply _root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MemGlintOfEntries.mem_glint_of_entries ..)

theorem blkOf_lt_iff {n r t : ℕ} (hn : n = r + t) (i j : Fin n) :
    blkOf r t j < blkOf r t i ↔ j.val < r ∧ r ≤ i.val := by
  have hi := i.2
  have hj := j.2
  unfold blkOf
  by_cases hj' : j.val < r <;> by_cases hi' : i.val < r
  · simp [hj', hi']
  · simp [hj', hi']; omega
  · simp [hj', hi']
  · have e1 : (j.val - r) / t = 0 := Nat.div_eq_of_lt (by omega)
    have e2 : (i.val - r) / t = 0 := Nat.div_eq_of_lt (by omega)
    simp [hj', hi', e1, e2]

theorem redFn_eq_one (D : D7) (s : SplitPlace D.host.E) (κ : Formalism.AUTREP.GAf D.host.E D.R.nV)
    (hU : κ ∈ Umax D.host.E D.R.nV) (hκ : TrivOutside {s.v} κ) (PP : Pl D.host.E) (hP : ¬ NG.OverPl PP s.v) :
    redFn (1 : GL (Fin D.R.nV) (EAf D)) PP (km D D.R.nV κ) = 1 := by
  refine (_root_.GlobalTheory.MtRed.km_reduction D D.R.nV).2.2.1 κ hU {s.v} (PP.under (𝓞 (maximalRealSubfield D.host.E))) PP hκ rfl ?_
  intro h
  apply hP
  rw [Set.mem_singleton_iff] at h
  rw [← h]
  rfl

theorem mem_iff : ∀ (D : D7) (hr : D.R.r ≤ D.R.nV) (Pg Q : Finset (Pl D.host.E)) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* kP s.w), (∀ x, φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1) → (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, ∀ a b, ∃ h : (s.loc D.R.nV κ).val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E), (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = φ ⟨_, h⟩) → s.w ∈ Pg → (∀ PP ∈ Pg, PP ≠ s.w → ¬ NG.OverPl PP s.v) → (∀ PP ∈ Q, ¬ NG.OverPl PP s.v) → ∀ κ, ReciprocityTheory.Aut.TrivOutside {s.v} κ → (κ ∈ stdJ (datV D D.R.nV hr Pg Q (P0 Pg D.R.r ψ) chi xi) ↔ NG.UniRT s D.R.r (s.loc D.R.nV κ)) := by
  intro D hr Pg Q ψ chi xi s φ hφ0 hred hsw hPg hQ κ hκ
  have hUA := (_root_.GlobalTheory.MtRed.km_reduction D D.R.nV).1
  have hSt := (_root_.GlobalTheory.MtRed.km_reduction D D.R.nV).2.1
  have hn : D.R.nV = D.R.r + D.R.t := rfl

  have hent : ∀ κ' ∈ Umax D.host.E D.R.nV, ∀ a b (x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)),
      (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) = (s.loc D.R.nV κ').val a b →
      (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ')).val a b = φ x := by
    intro κ' hU' a b x hx
    obtain ⟨h, e⟩ := hred κ' hU' a b
    rw [e]
    congr 1
    exact Subtype.ext hx.symm
  have hint : ∀ κ' ∈ Umax D.host.E D.R.nV, ∀ a b,
      (s.loc D.R.nV κ').val a b ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) :=
    fun κ' hU' a b => (hred κ' hU' a b).1
  have hzero : ∀ x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      φ x = 0 ↔ Valued.v (x : s.v.adicCompletion (maximalRealSubfield D.host.E)) < 1 := hφ0
  have hone : ∀ x : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E),
      φ x = 1 ↔ Valued.v ((x : s.v.adicCompletion (maximalRealSubfield D.host.E)) - 1) < 1 := by
    intro x
    rw [← sub_eq_zero, ← map_one φ, ← map_sub, hφ0]
    rfl
  constructor
  · intro hJ
    rw [stdJ, Subgroup.mem_comap, mem_lev, mem_parLev] at hJ
    obtain ⟨⟨-, hS, hg, -⟩, hT⟩ := hJ
    have hU : κ ∈ Umax D.host.E D.R.nV := (hSt κ).1 hS
    have hgw : redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ) ∈ blockTri (blkOf D.R.r D.R.t) := hg s.w hsw
    have hT' : upperLeftBlock hr (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)) ∈ unip (kP s.w) D.R.r :=
      hT ⟨s.w, hsw⟩ (Set.mem_univ _)
    have hb2 : redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ) ∈ blockTri (blk2 D.R.r) :=
      blockTri_blkOf_le _ _ hgw
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · refine mem_GLint_of_entries _ _ (fun a b => hint κ hU a b) (fun a b => ?_)
      rw [← map_inv]
      exact hint κ⁻¹ (inv_mem hU) a b
    · intro a b ha hb
      have e : (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = φ ⟨_, hint κ hU a b⟩ :=
        hent κ hU a b ⟨_, hint κ hU a b⟩ rfl
      have h0 : (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = 0 :=
        (mem_blockTri.1 hgw) a b ((blkOf_lt_iff hn a b).2 ⟨hb, ha⟩)
      rw [h0] at e
      exact (hzero ⟨_, hint κ hU a b⟩).1 e.symm
    · intro a b ha hb
      have hR := upper_block_val_submatrix hr hb2
      have key : ∀ i j : Fin D.R.r, ((upperLeftBlock hr (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)) : GL (Fin D.R.r) (kP s.w)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP s.w)) i j = (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val (Fin.castLE hr i) (Fin.castLE hr j) := by
        intro i j; rw [hR]; rfl
      have ea : Fin.castLE hr (⟨a.val, ha⟩ : Fin D.R.r) = a := Fin.ext rfl
      have eb : Fin.castLE hr (⟨b.val, hb⟩ : Fin D.R.r) = b := Fin.ext rfl
      refine ⟨fun hba => ?_, fun hab => ?_⟩
      · have h0 := unip_lower hT' (i := ⟨a.val, ha⟩) (j := ⟨b.val, hb⟩) hba
        rw [key, ea, eb, hent κ hU a b ⟨_, hint κ hU a b⟩ rfl] at h0
        exact (hzero ⟨_, hint κ hU a b⟩).1 h0
      · subst hab
        have h1 := unip_diag hT' ⟨a.val, ha⟩
        rw [key, ea, hent κ hU a a ⟨_, hint κ hU a a⟩ rfl] at h1
        exact (hone ⟨_, hint κ hU a a⟩).1 h1
  · intro hu
    have hgl := hu.1.1
    have hU : κ ∈ Umax D.host.E D.R.nV := GlobalTheory.SplitHeckeComm.mem_Umax_of_loc s κ hκ hgl
    have hw : ∀ a b, (redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ)).val a b = φ ⟨_, hint κ hU a b⟩ :=
      fun a b => hent κ hU a b _ rfl
    have hgw : redFn (1 : GL (Fin D.R.nV) (EAf D)) s.w (km D D.R.nV κ) ∈ blockTri (blkOf D.R.r D.R.t) := by
      rw [mem_blockTri]
      intro i j hij
      obtain ⟨hj, hi⟩ := (blkOf_lt_iff hn i j).1 hij
      rw [hw]
      exact (hzero ⟨_, hint κ hU i j⟩).2 (hu.1.2 i j hi hj)
    rw [stdJ, Subgroup.mem_comap, mem_lev, mem_parLev]
    refine ⟨⟨hUA κ, (hSt κ).2 hU, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩
    · by_cases hPw : PP = s.w
      · rw [hPw]; exact hgw
      · rw [redFn_eq_one D s κ hU hκ PP (hPg PP hP hPw)]; exact Subgroup.one_mem _
    · rw [redFn_eq_one D s κ hU hκ PP (hQ PP hP)]; exact Subgroup.one_mem _
    · intro PP _
      show upperLeftBlock hr (redFn (1 : GL (Fin D.R.nV) (EAf D)) PP.1 (km D D.R.nV κ)) ∈ unip (kP PP.1) D.R.r
      by_cases hPw : PP.1 = s.w
      · obtain ⟨PP, hPP⟩ := PP
        simp only at hPw
        subst hPw
        have hR := upper_block_val_submatrix hr (blockTri_blkOf_le _ _ hgw)
        refine ⟨fun i j (hij : j.val < i.val) => ?_, fun i => ?_⟩
        · rw [hR, Matrix.submatrix_apply, hw]
          exact (hzero ⟨_, hint κ hU (Fin.castLE hr i) (Fin.castLE hr j)⟩).2 ((hu.2 (Fin.castLE hr i) (Fin.castLE hr j) i.2 j.2).1 hij)
        · rw [hR, Matrix.submatrix_apply, hw]
          exact (hone ⟨_, hint κ hU (Fin.castLE hr i) (Fin.castLE hr i)⟩).2 ((hu.2 (Fin.castLE hr i) (Fin.castLE hr i) i.2 i.2).2 rfl)
      · rw [redFn_eq_one D s κ hU hκ PP.1 (hPg PP.1 PP.2 hPw)]
        have e1 : upperLeftBlock hr (1 : GL (Fin D.R.nV) (kP PP.1)) = 1 := blockDiagonalExtendByOnePrimeField_one _ (blkR hr)
        rw [e1]
        exact Subgroup.one_mem _

end GlobalTheory.MtIn.UniMem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarFiniteAddCharDivNatEqExpTrace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.CharRat

theorem star_psiEf_divN_inclE : ∀ (D : D7) (X : HidaSetting D) (α : 𝓞 D.host.E), star (X.psiEf (divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (X.ιE.symm (α : D.host.E))))) = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.intTrace ℤ (𝓞 D.host.E) α : ℤ) : ℂ) / ((X.B.g : ℕ) : ℂ)) := by
  intro D X α
  set y : X.B.I.E := X.ιE.symm (α : D.host.E) with hy
  set q : X.B.I.E := algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) * y with hq
  have hdiv : divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) y) =
      Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) q := by
    unfold divN
    rw [hq, map_mul, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hgq : algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) = algebraMap ℚ X.B.I.E ((X.B.g : ℚ)⁻¹) := by
    rw [map_inv₀, map_inv₀, map_natCast, map_natCast]
  have htrq : Algebra.trace ℚ X.B.I.E q = (X.B.g : ℚ)⁻¹ * Algebra.trace ℚ X.B.I.E y := by
    rw [hq, hgq, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have htr : Algebra.trace ℚ X.B.I.E y = Algebra.trace ℚ D.host.E (α : D.host.E) := by
    conv_rhs => rw [← X.ιE.apply_symm_apply (α : D.host.E)]
    exact (Algebra.trace_eq_of_algEquiv X.ιE.toRatAlgEquiv y).symm
  have hint : ((Algebra.intTrace ℤ (𝓞 D.host.E) α : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (α : D.host.E) :=
    Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.E) (B := 𝓞 D.host.E) α
  rw [hdiv, eq_inv_of_mul_eq_one_left (X.psiEf_rat q), GlobalTheory.St.G.psiEinf_eq_exp_trace, htrq, htr, ← hint,
    ← Complex.exp_neg]
  change (starRingEnd ℂ) _ = _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, map_ratCast]
  push_cast
  ring

end GlobalTheory.Mem.CharRat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymEdgeConjWeightedSumEqFlagAndUnipotentPairs
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SymChar.Comb

def cw (ρ k : ℕ) (s : Bool) (i : ℕ) : ℤ :=
  if ρ ≤ i ∧ i + 1 ≠ ρ + k then (if i + 1 < ρ + k then (if s then 0 else -1) else if i = ρ + k then 1 else -1) else 0

theorem term_eq {R : Type} [CommRing R] (ρ k : ℕ) (s : Bool) {r : ℕ} (M : Matrix (Fin r) (Fin r) R) (i j : Fin r) :
    (if symEdge ρ k i j then ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) =
      if j.val = i.val + 1 then ((cw ρ k s i.val : ℤ) : R) * M i j else 0 := by
  unfold symEdge GlobalTheory.Mem.SymChar.wtB cw
  simp only [Int.cast_ite, Int.cast_zero, Int.cast_one, Int.cast_neg]
  split_ifs <;> first | rfl | omega | (simp_all; done) | simp

theorem row_sum {R : Type} [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) (c : R) (i : Fin r) :
    (∑ j : Fin r, if j.val = i.val + 1 then c * M i j else 0) =
      c * (if h : i.val + 1 < r then M i ⟨i.val + 1, h⟩ else 0) := by
  by_cases h : i.val + 1 < r
  · rw [dite_eq_left h]
    have : ∀ j : Fin r, (j.val = i.val + 1) ↔ j = ⟨i.val + 1, h⟩ := fun j => by simp [Fin.ext_iff]
    simp only [this]
    rw [Finset.sum_ite_eq']
    simp
  · rw [dif_neg h, mul_zero]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]; omega

theorem nat_id {R : Type} [CommRing R] (ρ k : ℕ) (s : Bool) (F : ℕ → R) :
    (∑ i ∈ Finset.range (2 * ρ + k), ((cw ρ k s i : ℤ) : R) * F i) =
      (∑ a ∈ Finset.range ρ, if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k)) +
        (if s then 0 else ∑ i ∈ Finset.range k, if i + 1 < k then -F (ρ + k - 2 - i) else 0) := by
  rw [← Finset.sum_range_add_sum_Ico _ (show ρ + k ≤ 2 * ρ + k by omega),
    ← Finset.sum_range_add_sum_Ico _ (show ρ ≤ ρ + k by omega),
    Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  have h0 : (∑ i ∈ Finset.range ρ, ((cw ρ k s i : ℤ) : R) * F i) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      simp only [Finset.mem_range] at hi
      simp [cw, show ¬ ρ ≤ i by omega]
  have h1 : (∑ t ∈ Finset.range (2 * ρ + k - (ρ + k)), ((cw ρ k s (ρ + k + t) : ℤ) : R) * F (ρ + k + t)) =
      ∑ a ∈ Finset.range ρ, if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k) := by
    rw [show 2 * ρ + k - (ρ + k) = ρ by omega, ← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun t ht => ?_
    simp only [Finset.mem_range] at ht
    unfold cw
    by_cases h : t + 1 < ρ
    · rw [if_pos h, if_pos (show ρ ≤ ρ + k + (ρ - 1 - t) ∧ ρ + k + (ρ - 1 - t) + 1 ≠ ρ + k by omega),
        if_neg (show ¬ (ρ + k + (ρ - 1 - t) + 1 < ρ + k) by omega),
        if_neg (show ¬ (ρ + k + (ρ - 1 - t) = ρ + k) by omega),
        show ρ + k + (ρ - 1 - t) = 2 * ρ + k - t - 1 by omega]
      simp
    · rw [if_neg h, if_pos (show ρ ≤ ρ + k + (ρ - 1 - t) ∧ ρ + k + (ρ - 1 - t) + 1 ≠ ρ + k by omega),
        if_neg (show ¬ (ρ + k + (ρ - 1 - t) + 1 < ρ + k) by omega),
        if_pos (show ρ + k + (ρ - 1 - t) = ρ + k by omega),
        show ρ + k + (ρ - 1 - t) = ρ + k by omega]
      simp
  have h2 : (∑ t ∈ Finset.range (ρ + k - ρ), ((cw ρ k s (ρ + t) : ℤ) : R) * F (ρ + t)) =
      if s then 0 else ∑ i ∈ Finset.range k, if i + 1 < k then -F (ρ + k - 2 - i) else 0 := by
    rw [show ρ + k - ρ = k by omega]
    cases s
    · simp only [Bool.false_eq_true, if_false]
      rw [← Finset.sum_range_reflect (fun i => if i + 1 < k then -F (ρ + k - 2 - i) else 0) k]
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        rw [Finset.sum_range_succ, Finset.sum_range_succ']
        have e1 : ((cw ρ (k' + 1) false (ρ + k') : ℤ) : R) * F (ρ + k') = 0 := by
          unfold cw; rw [if_neg (by omega)]; simp
        have e2 : (if k' + 1 - 1 - 0 + 1 < k' + 1 then -F (ρ + (k' + 1) - 2 - (k' + 1 - 1 - 0)) else 0) = (0 : R) := by
          rw [if_neg (by omega)]
        rw [e1, e2, add_zero, add_zero]
        refine Finset.sum_congr rfl fun t ht => ?_
        simp only [Finset.mem_range] at ht
        rw [if_pos (show k' + 1 - 1 - (t + 1) + 1 < k' + 1 by omega),
          show ρ + (k' + 1) - 2 - (k' + 1 - 1 - (t + 1)) = ρ + t by omega]
        simp [cw, show ρ ≤ ρ + t ∧ ρ + t + 1 ≠ ρ + (k' + 1) by omega, show ρ + t + 1 < ρ + (k' + 1) by omega]
    · simp only [if_true]
      refine Finset.sum_eq_zero fun t ht => ?_
      simp only [Finset.mem_range] at ht
      unfold cw
      split_ifs <;> first | omega | simp_all
  rw [h0, h1, h2, zero_add, add_comm]

theorem weighted_sum_eq : ∀ {R : Type} [CommRing R] (ρ k r : ℕ) (hr : r = 2 * ρ + k + 1) (s : Bool) (M : Matrix (Fin r) (Fin r) R), (∑ i, ∑ j, if symEdge ρ k i j then ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) = (∑ a : Fin ρ, if h : a.val + 1 < ρ then -M ⟨2 * ρ + k - a.val - 1, by omega⟩ ⟨2 * ρ + k - a.val, by omega⟩ else M ⟨ρ + k, by omega⟩ ⟨ρ + k + 1, by omega⟩) + (if s then 0 else ∑ i : Fin k, if h : i.val + 1 < k then -M ⟨ρ + k - 2 - i.val, by omega⟩ ⟨ρ + k - 1 - i.val, by omega⟩ else 0) := by
  intro R _ ρ k r hr s M
  subst hr
  let F : ℕ → R := fun i => if h : i + 1 < 2 * ρ + k + 1 then M ⟨i, by omega⟩ ⟨i + 1, h⟩ else 0
  have hFv : ∀ i j (hi : i < 2 * ρ + k + 1) (hj : j < 2 * ρ + k + 1), j = i + 1 → F i = M ⟨i, hi⟩ ⟨j, hj⟩ := by
    intro i j hi hj e; subst e; simp only [F]; rw [dite_eq_left hj]
  have hL : (∑ i : Fin (2 * ρ + k + 1), ∑ j : Fin (2 * ρ + k + 1), if symEdge ρ k i j then
      ((GlobalTheory.Mem.SymChar.wtB ρ k s i j : ℤ) : R) * M i j else 0) =
      ∑ i : Fin (2 * ρ + k + 1), ((cw ρ k s i.val : ℤ) : R) * F i.val := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [term_eq]
    rw [row_sum]
  rw [hL, Fin.sum_univ_eq_sum_range (fun i => ((cw ρ k s i : ℤ) : R) * F i), Finset.sum_range_succ,
    show F (2 * ρ + k) = 0 from dif_neg (by omega), mul_zero, add_zero, nat_id]
  congr 1
  · refine (Fin.sum_univ_eq_sum_range (fun a => if a + 1 < ρ then -F (2 * ρ + k - a - 1) else F (ρ + k)) ρ).symm.trans
      (Finset.sum_congr rfl fun a _ => ?_)
    beta_reduce
    split_ifs with h
    · rw [hFv _ (2 * ρ + k - a.val) (by omega) (by omega) (by omega)]
    · rw [hFv _ (ρ + k + 1) (by omega) (by omega) (by omega)]
  · cases s
    · simp only [Bool.false_eq_true, if_false]
      refine (Fin.sum_univ_eq_sum_range (fun i => if i + 1 < k then -F (ρ + k - 2 - i) else 0) k).symm.trans
        (Finset.sum_congr rfl fun i _ => ?_)
      beta_reduce
      split_ifs with h
      · rw [hFv _ (ρ + k - 1 - i.val) (by omega) (by omega) (by omega)]
      · rfl
    · rfl

end GlobalTheory.Mem.SymChar.Comb
end

