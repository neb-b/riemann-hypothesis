module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0613
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocyclePolesFrobeniusQCrystalline
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0615
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefectTorsionSecondCohomologyKernel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0608
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelCrystallineSurjectionKilledByXPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComparisonHolds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0663

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharacters
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.TransportGL

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem map_map_symm (i : k ≃+* k') {n : ℕ} (g : GL (Fin n) k') :
    GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom g) = g :=
  Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)

theorem det_map (i : k ≃+* k') {n : ℕ} (g : GL (Fin n) k) :
    GeneralLinearGroup.det (GeneralLinearGroup.map i.toRingHom g) =
      Units.map i.toRingHom.toMonoidHom (GeneralLinearGroup.det g) := by
  ext
  simp [GeneralLinearGroup.val_det_apply, RingHom.map_det]

theorem isCusp_cls {n : ℕ} (π : IrrRep (GL (Fin n) k)) : (cls π).IsCusp ↔ 0 < n ∧ IsCuspidal π.ρ :=
  and_congr Iff.rfl ⟨isCuspidal_of_equiv (equivRep π).symm, isCuspidal_of_equiv (equivRep π)⟩

def transEquiv (i : k ≃+* k') {n : ℕ} (π : IrrRep (GL (Fin n) k)) (π' : IrrRep (GL (Fin n) k'))
    (e : π.V ≃ₗ[ℂ] π'.V) (he : ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)) :
    Representation.Equiv (π.ρ.comp (GeneralLinearGroup.map (n := Fin n) i.symm.toRingHom)) π'.ρ :=
  .mk e fun g => LinearMap.ext fun v => by
    show e (π.ρ (GeneralLinearGroup.map i.symm.toRingHom g) v) = π'.ρ g (e v)
    rw [he, map_map_symm]

theorem symm_rel (i : k ≃+* k') {n : ℕ} (π : IrrRep (GL (Fin n) k)) (π' : IrrRep (GL (Fin n) k'))
    (e : π.V ≃ₗ[ℂ] π'.V) (he : ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v)) :
    ∀ g w, e.symm (π'.ρ g w) = π.ρ (GeneralLinearGroup.map i.symm.toRingHom g) (e.symm w) := fun g w => by
  apply e.injective
  rw [e.apply_symm_apply, he, e.apply_symm_apply, map_map_symm]

theorem repRel_tw (i : k ≃+* k') {n : ℕ} (π : IrrRep (GL (Fin n) k)) (π' : IrrRep (GL (Fin n) k'))
    (e : π.V ≃ₗ[ℂ] π'.V) (he : ∀ g v, e (π.ρ g v) = π'.ρ (GeneralLinearGroup.map i.toRingHom g) (e v))
    (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (χ' : k'ˣ →* ℂˣ) (hχ' : IsSmoothChar χ')
    (hc : ∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) :
    RepRel i ((cls π).tw χ hχ) ((cls π').tw χ' hχ') := by
  refine ⟨n, irrTwist π _ hχ.detChar, irrTwist π' _ hχ'.detChar, e, congrArg (Sigma.mk n) (clTwist_cl π _ hχ.detChar),
    congrArg (Sigma.mk n) (clTwist_cl π' _ hχ'.detChar), fun g (v : π.V) => ?_⟩
  show e (twist π.ρ (detChar _ χ) g v) = twist π'.ρ (detChar _ χ') (GeneralLinearGroup.map i.toRingHom g) (e v)
  rw [twist_apply, twist_apply, map_smul, he, detChar_apply, detChar_apply, det_map, hc]

end GlobalTheory.LocLanglands.TransportGL


open GlobalTheory.LocLanglands.TransportGL in
theorem GlobalTheory.LocLanglands.repRel_isCusp_nu_ofChar : ∀ (k k' : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [CharZero k'] (i : k ≃+* k'), Continuous i → (∀ (x : IrrGL (k := k)) (x' : IrrGL (k := k')), RepRel i x x' → (x.IsCusp ↔ x'.IsCusp) ∧ ∀ s : ℂ, RepRel i (x.nu s) (x'.nu s)) ∧ ∀ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ) (χ' : k'ˣ →* ℂˣ) (hχ' : IsSmoothChar χ'), (∀ x, χ' (Units.map i.toRingHom.toMonoidHom x) = χ x) → RepRel i (IrrGL.ofChar χ hχ) (IrrGL.ofChar χ' hχ') := by
  intro k k' _ _ _ _ _ _ _ _ _ _ i hi
  have hs := _root_.GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation k k' i hi
  refine ⟨fun x x' ⟨n, π, π', e, hx, hx', he⟩ => ?_, fun χ hχ χ' hχ' hc => ?_⟩
  · subst hx hx'
    refine ⟨?_, fun s => repRel_tw i π π' e he _ _ _ _ (hs.2.2.2.2 s)⟩
    rw [isCusp_cls, isCusp_cls]
    refine and_congr Iff.rfl ⟨fun h => isCuspidal_of_equiv (transEquiv i π π' e he)
      (isCuspidal_comp_generalLinearGroupMap i hs.1 _ h), fun h => isCuspidal_of_equiv
      (transEquiv i.symm π' π e.symm (symm_rel i π π' e he)) (isCuspidal_comp_generalLinearGroupMap i.symm hi _ h)⟩
  · refine ⟨1, IrrRep.det (Fin 1) χ hχ, IrrRep.det (Fin 1) χ' hχ', LinearEquiv.refl ℂ ℂ, rfl, rfl, fun g (v : ℂ) => ?_⟩
    show twist (Representation.trivial ℂ (GL (Fin 1) k) ℂ) (detChar (Fin 1) χ) g v =
      twist (Representation.trivial ℂ (GL (Fin 1) k') ℂ) (detChar (Fin 1) χ') (GeneralLinearGroup.map i.toRingHom g) v
    rw [twist_apply, twist_apply, detChar_apply, detChar_apply, TransportGL.det_map, hc]
    rfl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistRecCompatible
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands

section Sums

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem segSum_append_lpSum (rc : IrrGL (k := w.adicCompletion E) → WD h) (l l' : List (Segment (w.adicCompletion E))) :
    segSum rc (l ++ l') = (segSum rc l).lpSum (segSum rc l') := by
  induction l with
  | nil => exact ((WD.lpSum_comm _ _).trans (WD.lpSum_zero _)).symm
  | cons a l ih =>
    have key : ∀ m : List (Segment (w.adicCompletion E)), segSum rc (a :: m) =
        (((rc a.first).lpTw (((a.len : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) a.len)).lpSum (segSum rc m) := fun _ => rfl
    rw [List.cons_append, key, key, ih, WD.lpSum_assoc]

end Sums

theorem lawsLit_prod : LanglandsExhaustionGL → LanglandsMultisegments → StandardCosocleGL → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (e : AddChar (w.adicCompletion E) Circle → WD h → ℂˣ) (rc : IrrGL (k := w.adicCompletion E) → WD h), LawsLit a ha e rc → ∀ (r t : ℕ) (σ : IrrRep (GL (Fin r) (w.adicCompletion E))) (τ : IrrRep (GL (Fin t) (w.adicCompletion E))) (π : IrrRep (GL (Fin (r + t)) (w.adicCompletion E))), Nonempty (π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) → rc (cls π) = (rc (cls σ)).lpSum (rc (cls τ)) := by
  intro hX hM hS E Ω _ _ _ _ _ A w h a ha e rc H r t σ τ π hπ
  have : CharZero (w.adicCompletion E) := algebraRat.charZero _
  obtain ⟨𝔪, h𝔪⟩ := hX _ (cls σ)
  obtain ⟨𝔫, h𝔫⟩ := hX _ (cls τ)
  have hp := _root_.GlobalTheory.LocGL.SumProd.isL_add_of_equiv_prod₂ hM hS _ r t σ τ π 𝔪 𝔫 (h𝔪.of_equiv (equivRep σ).symm) (h𝔫.of_equiv (equivRep τ).symm) hπ
  rw [H.langlands 𝔪.toList (cls σ) (by rwa [Multiset.coe_toList]),
    H.langlands 𝔫.toList (cls τ) (by rwa [Multiset.coe_toList]),
    H.langlands (𝔪.toList ++ 𝔫.toList) (cls π) (by
      rw [← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList]
      exact hp.of_equiv (equivRep π)), segSum_append_lpSum]

end GlobalTheory.LocLanglands

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLtOneIffNorm
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.BridgeInertia

variable {l : ℕ} [Fact l.Prime]

theorem valuation_lt_one_iff_norm {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {j : Ω →+* Loc.Om l}
    (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (x : Ω) : A.valuation x < 1 ↔ ‖j x‖ < 1 := by
  rw [valuation_lt_one_iff', hj, hj, map_inv₀, norm_inv]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < ‖j x‖ := norm_pos_iff.mpr ((_root_.map_ne_zero _).mpr hx)
    simp only [hx, false_or, not_le, one_lt_inv₀ h0]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem residue_trivial_of_image {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* Loc.Om l) (σ : GQ l)
    (h : ∀ y : Ω, ‖j y‖ ≤ 1 → ‖σ (j y) - j y‖ < 1) (x : Loc.Om l) (hx : ‖x‖ ≤ 1) : ‖σ x - x‖ < 1 := by
  obtain ⟨y, hy⟩ := (GlobalTheory.PlaceBridge.denseRange_embedding j).exists_dist_lt x one_pos
  rw [dist_eq_norm] at hy
  have hn : ∀ z, ‖σ z‖ = ‖z‖ := fun z => (spectralNorm_eq_of_equiv σ z).symm
  have hadd : ∀ a b : Loc.Om l, ‖a + b‖ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max
  have hjy : ‖j y‖ ≤ 1 := by
    have e : j y = x + -(x - j y) := by ring
    rw [e]
    exact (hadd _ _).trans (max_le hx (by rw [norm_neg]; exact hy.le))
  have e : σ x - x = σ (x - j y) + ((σ (j y) - j y) + -(x - j y)) := by
    rw [map_sub]; ring
  rw [e]
  refine (hadd _ _).trans_lt (max_lt (by rw [hn]; exact hy) ((hadd _ _).trans_lt (max_lt (h y hjy) ?_)))
  rw [norm_neg]; exact hy

theorem mem_Ine_iff {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosed Ω] {A : ValuationSubring Ω}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : ∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1) (σ : ↥(GK Bw.Kw)) :
    ((Bw.e.symm σ : ↥(Dec (F := E) A)) : Ω ≃ₐ[E] Ω) ∈ Ine (F := E) A ↔
      ∀ x : Loc.Om l, ‖x‖ ≤ 1 → ‖(σ : GQ l) x - x‖ < 1 := by
  have hc : ∀ y, (σ : GQ l) (Bw.j y) = Bw.j (((Bw.e.symm σ : ↥(Dec (F := E) A)) : Ω ≃ₐ[E] Ω) y) := fun y => by
    rw [← Bw.e_comm, MulEquiv.apply_symm_apply]
  constructor
  · intro h
    refine residue_trivial_of_image Bw.j _ fun y hy => ?_
    rw [hc, ← map_sub, ← valuation_lt_one_iff_norm hj]
    exact h.2 y ((A.valuation_le_one_iff y).2 ((hj y).2 hy))
  · intro h
    refine ⟨(Bw.e.symm σ).2, fun y hy => ?_⟩
    rw [valuation_lt_one_iff_norm hj, map_sub, ← hc]
    exact h _ ((hj y).1 ((A.valuation_le_one_iff y).1 hy))

theorem inertEq : ∀ D : D7, InertEq D := by
  intro D i w hw
  have : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  have key : ∀ σ : Br.G D.nbr i w hw, σ ∈ Br.inert D.nbr i w hw ↔
      ∀ x : Loc.Om (D.nd.l i), ‖x‖ ≤ 1 → ‖(σ : GQ (D.nd.l i)) x - x‖ < 1 := fun σ =>
    mem_Ine_iff (D.nbr i w hw) (D.nbr_ind i w hw) σ
  refine le_antisymm (fun σ hσ => Subgroup.subset_closure ?_) ?_
  · exact (key σ).1 hσ
  · exact (Subgroup.closure_le _).2 fun σ hσ => (key σ).2 hσ

end GlobalTheory.BridgeInertia

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHold
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL

theorem wach_used_clauses (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) : DeltaInvariantNormBound D HW F Cm := by
  unfold DeltaInvariantNormBound
  refine ⟨GlobalTheory.NL.LetterFree.letters_free D HW F, GlobalTheory.NL.WachLatticeTrivialModUniformizer.wachLattice_galois_trivial_mod_uniformizer D HW F Cm,
    GlobalTheory.NL.CmpCris.wachLattice_comparison_dcris D HW F Cm, _root_.GlobalTheory.NL.LatLevel.lattice_at_level D HW F Cm, _root_.GlobalTheory.NL.Heights.heights_from_jumps D HW F Cm,
    _root_.GlobalTheory.NL.Exact.exactness_of_N D HW F Cm, _root_.GlobalTheory.NL.PoleCrys.main D HW F, _root_.GlobalTheory.NL.NygaardFrobeniusPower.crystalline_extension_integral_cocycle_all_places D HW F Cm, _root_.GlobalTheory.NL.p9_statement D HW F,
    _root_.GlobalTheory.NL.FrobeniusMatrixUniqueness.main D HW F, _root_.GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient D HW F Cm, GlobalTheory.NL.HerrComplexH1.herr_H1_description D HW F,
    GlobalTheory.NL.FiniteRestrictionH1f.mem_H1f_iff_res_mem D HW F, _root_.GlobalTheory.NL.IntComplex.main D HW F, _root_.GlobalTheory.NL.DefectTorsion.defect_torsion D HW F Cm,
    _root_.GlobalTheory.NL.CokerKill.X_pow_kills_coker D HW F Cm, ?_⟩
  unfold ConclusionE
  exact ⟨GlobalTheory.NL.NygaardExtension.main D HW F, _root_.GlobalTheory.NL.SandJumps.main D HW F Cm⟩

end GlobalTheory.NL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecialStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligne_charpoly_twist_special : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), (x.lpTw 0).lpChar (WD.lpSp (h := h) 1) = x ∧ ∀ (l : ℕ) (σ : Weil h), ((x.lpTw (((l : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) l)).charPol σ = ((Multiset.range l).map fun j : ℕ => (x.lpTw j).charPol σ).prod := by
  intro E Ω _ _ _ _ _ A w h x
  have hOne : (x.lpTw 0).lpChar (WD.lpSp (h := h) 1) = x := by
    rw [WD.lpTw_zero]
    induction x using WD.ind with
    | hP n a =>
      rw [WD.lpSp, WD.lpChar_mk]
      refine WD.sound (WDRep.Iso.symm ⟨(TensorProduct.rid ℂ (Fin n → ℂ)).symm ≪≫ₗ
        TensorProduct.congr (LinearEquiv.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ).symm,
        fun σ v => ?_, fun v => ?_⟩)
      · have : (WDRep.sp (h := h) 1).ρ σ = 1 := by
          refine LinearMap.ext fun v => funext fun i => ?_
          simp [WDRep.spEig]
        rw [WDRep.tensor_ρ, this]
        simp
      · have : (WDRep.sp (h := h) 1).N = 0 := by
          refine LinearMap.ext fun v => funext fun i => ?_
          simp [shiftEnd_apply]
        rw [WDRep.tensor_N, this]
        simp
  refine ⟨hOne, fun l σ => ?_⟩
  induction x using WD.ind with
  | hP n a =>
    have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
    rw [WD.lpSp, WD.lpTw_mk, WD.lpChar_mk, WD.charPol_mk, WDRep.tensor_ρ, WDRep.sp_ρ,
      GlobalTheory.WeilDeligne.SpCharpoly.charpoly_map_diagEnd]
    change _ = ∏ j ∈ Finset.range l, ((WD.mk a).lpTw (j : ℕ)).charPol σ
    rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => ((WD.mk a).lpTw (j : ℕ)).charPol σ)]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.tw_ρ, smul_smul, ← mul_zpow, WDRep.spEig,
      coe_qPow, ← Complex.cpow_add _ _ hq, ← Complex.ofReal_add, sub_add_cancel]
end

