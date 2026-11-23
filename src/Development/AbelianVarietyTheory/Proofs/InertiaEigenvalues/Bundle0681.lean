module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0669
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0647
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0628
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0026
public import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDataDualExact
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

open Formalism.MainNotions.N (twistRep coefRep)

namespace GlobalTheory.AdmLoc

theorem mk_mem_H1fX_iff_inHfX {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀]
    [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module O V]
    [IsScalarTower O LL V] {ρ : Representation LL G V} [TopologicalSpace V] [ContinuousAdd V]
    [ContinuousConstSMul LL V] (L : Lattice (O := O) ρ) (ρ' : Representation LL G V) (L' : Lattice (O := O) ρ')
    (X : Type) [AddCommGroup X] [Module O X] (χ : G →* Oˣ) :
    (∀ g, ρ' g = ((tableLineDegreeTwo.charL (LL := LL) χ g)⁻¹ : LLˣ).val • ρ g) → L'.T = L.T →
    ∀ (z : G → ↥L.T ⊗[O] X) (hz : z ∈ Z1 (twCoef (latRep L) χ X) ⊤),
      (Submodule.Quotient.mk ⟨z, hz⟩ ∈ finiteSelmer PD L χ X ↔ tableLineDegreeTwo.InHfX PD L L' X χ z) := by
  intro hρ hT z hz
  have e1 : ρ' = twistRep ρ (chiLL LL χ⁻¹) := by
    ext g v
    rw [hρ g, twistRep_apply]
    simp [chiLL, tableLineDegreeTwo.charL]
  subst e1
  have e2 : L' = twLattice L χ⁻¹ := by
    cases L'
    simp only at hT
    subst hT
    rfl
  subst e2
  have hact : ∀ g (m : ↥L.T ⊗[O] X), twCoef (latRep L) χ X g m = tableLineDegreeTwo.actTw L X χ g m := by
    intro g m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      rw [coefRep_tmul, twistRep_apply]
      simp only [tableLineDegreeTwo.actTw, LinearMap.smul_apply, LinearMap.rTensor_tmul, smul_tmul']
      rfl
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  have hA : toAmb (twCoef (latRep L) χ X) (Submodule.Quotient.mk ⟨z, hz⟩) = Submodule.Quotient.mk z := rfl
  rw [finiteSelmer, Submodule.mem_comap, hA, LinearMap.mem_range]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨S, rfl⟩ := TensorProduct.exists_finset u
    have hrep : ∀ p : ↥(latticeFiniteCohomology PD (twLattice L χ⁻¹)), ∃ c : ↥(latticeCocycles (twLattice L χ⁻¹)),
        (c : G → V) ∈ latticeFiniteCocycles PD (twLattice L χ⁻¹) ∧ Submodule.Quotient.mk c = (p : LatticeCohomology (twLattice L χ⁻¹)) := by
      rintro ⟨p, hp⟩
      obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hp
      exact ⟨c, hc, rfl⟩
    choose rep hrepf hrepmk using hrep
    let e := S.equivFin
    let cc : Fin S.card → ↥(latticeCocycles (twLattice L χ⁻¹)) := fun j => rep (e.symm j).1.1
    let xx : Fin S.card → X := fun j => (e.symm j).1.2
    have key : (tensAmb L χ X ∘ₗ (latticeFiniteCohomology PD (twLattice L χ⁻¹)).subtype.rTensor X)
        (∑ p ∈ S, p.1 ⊗ₜ[O] p.2) = Submodule.Quotient.mk (∑ j, tensCoc L χ X (cc j) (xx j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← Finset.sum_coe_sort S, ← e.symm.sum_comp]
      refine Eq.trans ?_ (map_sum (Submodule.mkQ _) _ _).symm
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [LinearMap.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply, ← hrepmk, tensAmb_tmul]
      rfl
    rw [key] at hu
    obtain ⟨m, -, hm⟩ := (Submodule.Quotient.eq _).mp hu
    refine ⟨S.card, fun j g => evT (twLattice L χ⁻¹) g (cc j), xx, -m, fun j => hrepf _, fun g => ?_⟩
    have h1 : twCoef (latRep L) χ X g m - m = (∑ j, tensCoc L χ X (cc j) (xx j)) g - z g := congrFun hm g
    simp only [Finset.sum_apply] at h1
    rw [hact] at h1
    simp only [map_neg]
    have h2 : ∀ j, tensCoc L χ X (cc j) (xx j) g = evT (twLattice L χ⁻¹) g (cc j) ⊗ₜ[O] xx j := fun j => rfl
    simp only [h2] at h1
    have h3 : z g = ∑ j, evT (twLattice L χ⁻¹) g (cc j) ⊗ₜ[O] xx j - (tableLineDegreeTwo.actTw L X χ g m - m) := by
      rw [h1]; abel
    rw [h3]
    abel
  · rintro ⟨k, c, x, m, hc, hzc⟩
    let cc : Fin k → ↥(latticeCocycles (twLattice L χ⁻¹)) := fun j => ⟨fun g => (c j g : V), (hc j).1⟩
    refine ⟨∑ j, (⟨Submodule.Quotient.mk (cc j), Submodule.mem_map_of_mem (hc j)⟩ :
      ↥(latticeFiniteCohomology PD (twLattice L χ⁻¹))) ⊗ₜ[O] x j, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have h1 : ∀ j, (tensAmb L χ X ∘ₗ (latticeFiniteCohomology PD (twLattice L χ⁻¹)).subtype.rTensor X)
        ((⟨Submodule.Quotient.mk (cc j), Submodule.mem_map_of_mem (hc j)⟩ :
          ↥(latticeFiniteCohomology PD (twLattice L χ⁻¹))) ⊗ₜ[O] x j) = Submodule.mkQ _ (tensCoc L χ X (cc j) (x j)) := fun j => rfl
    simp only [h1]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, Submodule.mkQ_apply]
    refine (Submodule.Quotient.eq _).mpr ?_
    refine Submodule.mem_map.mpr ⟨-m, Submodule.mem_top, ?_⟩
    funext g
    change twCoef (latRep L) χ X g (-m) - (-m) = (∑ j, tensCoc L χ X (cc j) (x j)) g - z g
    simp only [Finset.sum_apply, hact, map_neg, hzc g]
    have h2 : ∀ j, tensCoc L χ X (cc j) (x j) g = c j g ⊗ₜ[O] x j := fun j => rfl
    simp only [h2]
    abel

end GlobalTheory.AdmLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PermOfWeilDeligneSpecialDecompositionEqStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne.SpSummand GlobalTheory.WeilDeligne.SpUnique in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perm_of_weilDeligne_special_decomposition_eq :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
      (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
      (l l' : List (WD h × ℕ)),
      (∀ p ∈ l, IsIrrWD p.1) → (∀ p ∈ l', IsIrrWD p.1) →
      sumList (l.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp (h := h) (p.2 + 1)))) =
        sumList (l'.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp (h := h) (p.2 + 1)))) →
      l.Perm l' := by
  intro E Ω _ _ _ _ _ A w h l l'
  classical
  let F : WD h × ℕ → WD h := fun p => p.1.lpChar (WD.lpSp (h := h) (p.2 + 1))
  suffices H : ∀ n (l l' : List (WD h × ℕ)), l.length = n → (∀ p ∈ l, IsIrrWD p.1) →
      (∀ p ∈ l', IsIrrWD p.1) → sumList (l.map F) = sumList (l'.map F) → l.Perm l' from
    H _ l l' rfl
  intro n
  induction n with
  | zero =>
    intro l l' hn hl hl' heq
    obtain rfl := List.length_eq_zero_iff.1 hn
    cases l' with
    | nil => exact List.Perm.nil
    | cons q l'' =>
      exfalso
      have hd := congrArg WD.lpDim heq
      change WD.lpDim (WD.lpZero (h := h)) = WD.lpDim (WD.lpSum _ (sumList _)) at hd
      rw [WD.lpDim_zero, WD.lpDim_sum] at hd
      have hpos : 0 < WD.lpDim (F q) := by
        obtain ⟨m, a, ha, hirr⟩ := hl' q List.mem_cons_self
        dsimp only [F]
        rw [WD.lpDim_tensor, WD.lpDim_lpSp, ← ha, WD.lpDim_mk, Module.finrank_fin_fun]
        obtain ⟨v, hv⟩ := SpSummand.exists_ne_zero hirr
        have hm : m ≠ 0 := by
          rintro rfl
          exact hv (Subsingleton.elim _ _)
        exact Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.succ_pos _)
      omega
  | succ n ih =>
    intro l l' hn hl hl' heq
    have hne : l ≠ [] := by
      rintro rfl
      simp at hn
    obtain ⟨⟨y, k⟩, hp, hmax⟩ : ∃ p ∈ l, ∀ q ∈ l, q.2 ≤ p.2 := by
      obtain ⟨p, hp, hmax⟩ := l.toFinset.exists_max_image Prod.snd
        (by obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hne; exact ⟨x, List.mem_toFinset.2 hx⟩)
      exact ⟨p, List.mem_toFinset.1 hp, fun q hq => hmax q (List.mem_toFinset.2 hq)⟩
    obtain ⟨m, a, rfl, ha⟩ := hl _ hp

    have hQ : HasCopyW a.ρ k (lastEig h k) (sumList (l.map F)) := by
      refine hasCopyW_sumList F l _ hp ?_
      show HasCopyW a.ρ k (lastEig h k) ((WD.mk a).lpChar (WD.lpSp (h := h) (k + 1)))
      rw [WD.lpSp, WD.lpChar_mk, hasCopyW_mk]
      exact hasCopy_self a ha k
    have hZ : PowZeroW k (sumList (l.map F)) := by
      refine powZeroW_sumList F l fun q hq => ?_
      rcases q with ⟨y', k'⟩
      obtain ⟨m', a', rfl, ha'⟩ := hl _ hq
      show PowZeroW k ((WD.mk a').lpChar (WD.lpSp (h := h) (k' + 1)))
      rw [WD.lpSp, WD.lpChar_mk, powZeroW_mk]
      exact powZero_of_le a' ha' (hmax _ hq)
    rw [heq] at hQ hZ
    obtain ⟨⟨y', k'⟩, hq', hqQ, hqZ⟩ := exists_mem_of_sumList F l' hQ hZ
    obtain ⟨n', a', rfl, ha'⟩ := hl' _ hq'
    dsimp only [F] at hqQ hqZ
    rw [WD.lpSp, WD.lpChar_mk, hasCopyW_mk] at hqQ
    rw [WD.lpSp, WD.lpChar_mk, powZeroW_mk] at hqZ
    obtain ⟨hm, hiso⟩ := eq_of_hasCopy a ha a' ha' k' k hqQ hqZ
    have hp' : (WD.mk a, k) ∈ l' := by
      have : ((WD.mk a', k') : WD h × ℕ) = (WD.mk a, k) := Prod.ext (WD.sound hiso).symm hm
      rw [← this]
      exact hq'

    let p : WD h × ℕ := (WD.mk a, k)
    have e1 : sumList (l.map F) = (F p).lpSum (sumList ((l.erase p).map F)) :=
      sumList_perm ((List.perm_cons_erase hp).map F)
    have e2 : sumList (l'.map F) = (F p).lpSum (sumList ((l'.erase p).map F)) :=
      sumList_perm ((List.perm_cons_erase hp').map F)
    have hc : sumList ((l.erase p).map F) = sumList ((l'.erase p).map F) := by
      refine WD.lpSum_cancel_right E Ω A w h _ _ (F p) ?_
      rw [WD.lpSum_comm, ← e1, WD.lpSum_comm, ← e2]
      exact heq
    have hlen : (l.erase p).length = n := by
      rw [List.length_erase_of_mem hp, hn]
      rfl
    have := ih (l.erase p) (l'.erase p) hlen (fun q hq => hl q (List.mem_of_mem_erase hq))
      (fun q hq => hl' q (List.mem_of_mem_erase hq)) hc
    exact ((List.perm_cons_erase hp).trans (this.cons p)).trans (List.perm_cons_erase hp').symm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymm
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WDTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

theorem isIrreducible_comp {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (f : G →* H) (hf : Function.Surjective f) (hρ : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp f : Representation ℂ G V) := by
  let e : Subrepresentation (ρ.comp f : Representation ℂ G V) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        obtain ⟨x, rfl⟩ := hf g
        exact S.apply_mem_toSubmodule x hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  have : IsSimpleOrder (Subrepresentation ρ) := hρ
  exact e.isSimpleOrder

def pull (f : Weil h' →* Weil h) (hdeg : ∀ σ, deg (f σ) = deg σ) (hq : normV w = normV w')
    (hs : ∀ (M : Type) [Monoid M] (g : Weil h →* M), IsSmooth g → IsSmooth (g.comp f))
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) : WDRep h' V where
  ρ := a.ρ.comp f
  N := a.N
  smooth := hs _ a.ρ a.smooth
  semisimple σ := a.semisimple (f σ)
  nilpotent := a.nilpotent
  comm σ := by
    show a.ρ (f σ) * a.N = _
    rw [a.comm (f σ), hdeg, hq]
    rfl

section Pull

variable (f : Weil h' →* Weil h) (hdeg : ∀ σ, deg (f σ) = deg σ) (hq : normV w = normV w')
    (hs : ∀ (M : Type) [Monoid M] (g : Weil h →* M), IsSmooth g → IsSmooth (g.comp f))

theorem iso_pull {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] {a : WDRep h V} {b : WDRep h V'}
    (hab : a.Iso b) : (pull f hdeg hq hs a).Iso (pull f hdeg hq hs b) := by
  obtain ⟨e, h1, h2⟩ := hab
  exact ⟨e, fun σ v => h1 (f σ) v, h2⟩

def pullWD : WD h → WD h' :=
  Quotient.lift (s := isoSetoid h) (fun a => WD.mk (pull f hdeg hq hs a.2))
    (fun _ _ hab => WD.sound (iso_pull f hdeg hq hs hab))

theorem pullWD_mk {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) :
    pullWD f hdeg hq hs (WD.mk a) = WD.mk (pull f hdeg hq hs a) :=
  WD.sound (iso_pull f hdeg hq hs (WD.iso_std a).symm)

theorem pullWD_eq {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (a : WDRep h V) (b : WDRep h' V')
    (e : V ≃ₗ[ℂ] V') (h1 : ∀ σ v, e (a.ρ (f σ) v) = b.ρ σ (e v)) (h2 : ∀ v, e (a.N v) = b.N (e v)) :
    pullWD f hdeg hq hs (WD.mk a) = WD.mk b := by
  rw [pullWD_mk]; exact WD.sound ⟨e, h1, h2⟩

end Pull

end GlobalTheory.WDTransport

namespace GlobalTheory.WDTransport


open WDRep in
theorem exists_equiv_wd : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∃ S : WD h ≃ WD h', (∀ y y', WDRel φ y y' ↔ S y = y') ∧ (∀ y, (S y).lpDim = y.lpDim) ∧ S (WD.lpZero (h := h)) = WD.lpZero (h := h') ∧ (∀ y z, S (y.lpSum z) = (S y).lpSum (S z)) ∧ (∀ y z, S (y.lpChar z) = (S y).lpChar (S z)) ∧ (∀ y (s : ℝ), S (y.lpTw s) = (S y).lpTw s) ∧ (∀ n, S (WD.lpSp (h := h) n) = WD.lpSp (h := h') n) ∧ (∀ y, IsIrrWD (S y) ↔ IsIrrWD y) ∧ ∀ (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) (ξ' : Weil h' →* ℂˣ) (hξ' : GlobalTheory.WeilDeligne.IsSmooth ξ'), (∀ σ σ', WeilRel φ σ σ' → ξ σ = ξ' σ') → S (WD.lpOfChar h ξ hξ) = WD.lpOfChar h' ξ' hξ' := by
  intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j i hP
  obtain ⟨c, hc, hdegc, hq, hsm⟩ := _root_.GlobalTheory.WeilTransport.weil_equiv E Ω A w h E' Ω' A' w' h' φ j i hP
  have hd1 : ∀ σ, deg (c.symm.toMonoidHom σ) = deg σ := fun σ => by
    have := hdegc (c.symm σ); simp only [MulEquiv.apply_symm_apply] at this
    simpa using this.symm
  have hd1' : ∀ σ, deg (c.symm σ) = deg σ := hd1
  have hs1 : ∀ (M : Type) [Monoid M] (g : Weil h →* M), IsSmooth g →
      IsSmooth (g.comp c.symm.toMonoidHom) := fun M _ g hg => by
    have e : (g.comp c.symm.toMonoidHom).comp c.toMonoidHom = g := by ext σ; simp
    have hg' : IsSmooth ((g.comp c.symm.toMonoidHom).comp c.toMonoidHom) := by rwa [e]
    exact (hsm M _).mpr hg'
  have hs2 : ∀ (M : Type) [Monoid M] (g : Weil h' →* M), IsSmooth g →
      IsSmooth (g.comp c.toMonoidHom) := fun M _ g hg => (hsm M g).mp hg
  have hd2 : ∀ σ, deg (c.toMonoidHom σ) = deg σ := fun σ => hdegc σ
  let F := pullWD c.symm.toMonoidHom hd1 hq.symm hs1
  let B := pullWD c.toMonoidHom hd2 hq hs2
  have hF : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V),
      F (WD.mk a) = WD.mk (pull c.symm.toMonoidHom hd1 hq.symm hs1 a) := fun a => pullWD_mk _ _ _ _ a
  have hB : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h' V),
      B (WD.mk a) = WD.mk (pull c.toMonoidHom hd2 hq hs2 a) := fun a => pullWD_mk _ _ _ _ a
  let S : WD h ≃ WD h' :=
    { toFun := F
      invFun := B
      left_inv := fun y => by
        induction y using WD.ind with
        | hP n a =>
          rw [hF, hB]
          exact WD.sound ⟨.refl _ _, fun σ v => by simp [pull], fun v => rfl⟩
      right_inv := fun y => by
        induction y using WD.ind with
        | hP n a =>
          rw [hB, hF]
          exact WD.sound ⟨.refl _ _, fun σ v => by simp [pull], fun v => rfl⟩ }
  have hS : ∀ y, S y = F y := fun _ => rfl
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y y'
    constructor
    · rintro ⟨n, b, b', rfl, rfl, hN, hρ⟩
      rw [hS]
      refine pullWD_eq _ _ _ _ b b' (.refl _ _) (fun σ v => ?_) (fun v => by simp [hN])
      have := hρ (c.symm σ) σ ((hc _ _).mpr (by simp))
      simp [this]
    · rintro rfl
      obtain ⟨n, b, rfl⟩ := WD.exists_rep y
      refine ⟨n, b, pull c.symm.toMonoidHom hd1 hq.symm hs1 b, rfl, (hF b).symm, rfl, fun σ σ' hσ => ?_⟩
      rw [← (hc σ σ').mp hσ]
      simp [pull]
  · intro y
    induction y using WD.ind with
    | hP n a => rw [hS, hF, WD.lpDim_mk, WD.lpDim_mk]
  · rw [hS]
    exact pullWD_eq _ _ _ _ _ _ (.refl _ _) (fun σ v => Subsingleton.elim _ _) (fun v => Subsingleton.elim _ _)
  · intro y z
    induction y using WD.ind with
    | hP n a =>
    induction z using WD.ind with
    | hP m b =>
      rw [hS, hS, hS, WD.lpSum_mk, hF, hF, hF, WD.lpSum_mk]
      exact WD.sound ⟨.refl _ _, fun σ v => rfl, fun v => rfl⟩
  · intro y z
    induction y using WD.ind with
    | hP n a =>
    induction z using WD.ind with
    | hP m b =>
      rw [hS, hS, hS, WD.lpChar_mk, hF, hF, hF, WD.lpChar_mk]
      exact WD.sound ⟨.refl _ _, fun σ v => rfl, fun v => rfl⟩
  · intro y s
    induction y using WD.ind with
    | hP n a =>
      rw [hS, hS, WD.lpTw_mk, hF, hF, WD.lpTw_mk]
      exact WD.sound ⟨.refl _ _, fun σ v => by simp [pull, hd1', hq], fun v => rfl⟩
  · intro n
    rw [hS]
    exact pullWD_eq _ _ _ _ _ _ (.refl _ _) (fun σ v => by simp [WDRep.spEig, hd1', hq]) (fun v => rfl)
  · intro y
    constructor
    · rintro ⟨n, b, hb, hirr⟩
      refine ⟨n, pull c.toMonoidHom hd2 hq hs2 b, ?_, isIrreducible_comp b.ρ _ c.surjective hirr⟩
      rw [← hB, hb]
      exact S.left_inv y
    · rintro ⟨n, a, rfl, hirr⟩
      exact ⟨n, pull c.symm.toMonoidHom hd1 hq.symm hs1 a, (hF a).symm,
        isIrreducible_comp a.ρ _ c.symm.surjective hirr⟩
  · intro ξ hξ ξ' hξ' hξξ
    rw [hS]
    refine pullWD_eq _ _ _ _ _ _ (.refl _ _) (fun σ v => ?_) (fun v => rfl)
    have := hξξ (c.symm σ) σ ((hc _ _).mpr (by simp))
    simp [this]

end GlobalTheory.WDTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisConvOfSteps
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem rallisConv_of_steps : ∀ D : D7, SWPair D → EisAbs D → KerAbs D → TermMove D → TermInv D → CuspKill D → RallisConv D := by
  intro D hSW hEis hKer hMove hInv hKill θ ψ V W χV χW om hθ hω hsig hpos hbig νV 𝓗 νW 𝓖 μ 𝓕 hνV h𝓗 hνW h𝓖
    hμ h𝓕 h1 f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁ hφ₂ hc₂
  have hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 (lagFrame W) :=
    { weil := hω, sigOK := hsig, pos := hpos, big := hbig, haarV := hνV, fdV := h𝓗, haarW := hνW, fdW := h𝓖,
      covol := ⟨hμ, h𝓕, h1⟩, frame := lagFrame_isLagFrame W }
  obtain ⟨K1, K2, K3⟩ := _root_.GlobalTheory.RawLift.rallis_kernel_step D hKer hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁
    hφ₂ hc₂
  obtain ⟨-, E2, E3⟩ := _root_.GlobalTheory.RallisExch.eisAbs_exchange D hEis ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁ hφ₂ hc₂
  obtain ⟨G1, G2⟩ := _root_.GlobalTheory.RawLift.rallis_graphs D hEis hMove ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁
    hφ₂ hc₂
  have N := _root_.GlobalTheory.RallisCusp.nonGraph_sum_eq_zero D hEis hMove hInv hKill (GlobalTheory.RawLift.TermCont.continuous_lagTerm D) ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂
    hφ₁ hc₁ hφ₂ hc₂
  refine ⟨K1, K2, G1, ?_⟩
  rw [K3, E3, ← E2.tsum_subtype_add_tsum_subtype_compl {Y : Lag W | Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥}]
  erw [N, add_zero]
  rw [← G2]
  rfl

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTExistsIff
section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT

section Laws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lawsT_iff (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (rc : IrrGL (k := w.adicCompletion E) → WD h) : LawsT a ha rc ↔ UpperTheory.Zero.LLC.LawsT a ha rc :=
  ⟨fun H => ⟨H.1, H.2, H.3, H.4, H.5, H.6, H.7, H.8, H.9, H.10, H.11, H.12⟩,
   fun H => ⟨H.1, H.2, H.3, H.4, H.5, H.6, H.7, H.8, H.9, H.10, H.11, H.12⟩⟩

end Laws

end GlobalTheory.RecT
end

