module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0741
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0744
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0725
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0732
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0028
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0051
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0022

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace GlobalTheory.FormDict.RecTLaws

section Core

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (k := w.adicCompletion E) → WD h}

theorem locProd_eq (H : IsRec h rc) : ∀ {c n : ℕ} {d : Fin c → ℕ} (hd : ∑ i, d i = n)
    (σ : ∀ i, SmIrr (GL (Fin (d i)) (w.adicCompletion E))) (σ' : SmIrr (GL (Fin n) (w.adicCompletion E))),
    Nonempty (σ'.ρ.Equiv (GlobalTheory.UnitaryBC.locProd hd w σ)) →
      rc (cls (ParLaws.toRep σ')) = sumList (List.ofFn fun i => rc (cls (ParLaws.toRep (σ i)))) := by
  obtain ⟨a, ha, ε, -, L⟩ := H
  intro c
  induction c with
  | zero =>
    intro n d hd σ σ' e
    obtain rfl : n = 0 := by simpa using hd.symm
    obtain ⟨e⟩ := e
    obtain ⟨φ⟩ := GlobalTheory.LocGL.SupportRing.nonempty_equiv_unit (k := w.adicCompletion E) (stdBlocks d hd) fun i => (σ i).ρ
    have h1 := L.det 0 1 isSmoothChar_one
    simp only [List.range_zero, List.map_nil] at h1
    rw [List.ofFn_zero]
    refine ((L.eq_iff (ParLaws.toRep σ') (IrrRep.det (Fin 0) 1 isSmoothChar_one)).2 ⟨e.trans φ⟩).trans ?_
    exact h1
  | succ s ih =>
    intro n d hd σ σ' e
    obtain rfl : n = d 0 + ∑ i : Fin s, d i.succ := hd.symm.trans (Fin.sum_univ_succ d)
    obtain ⟨e⟩ := e
    obtain ⟨E₁⟩ := MultiIrr.nonempty_prod₂_equiv_multiProd_succ (k := w.adicCompletion E) d hd fun i => (σ i).ρ
    have hs : IsSmooth (multiProd (stdBlocks (fun i : Fin s => d i.succ) rfl) fun i : Fin s => (σ i.succ).ρ) :=
      isSmooth_parInd _ _
    have hi := _root_.GlobalTheory.SmGL.ProdIrr.isIrreducible_of_prod₂ _ _ _ _ _ _ (σ 0).ρ _ σ'.ρ (σ 0).smooth (σ 0).irred hs σ'.irred ⟨e.trans E₁.symm⟩
    let σ'' : SmIrr (GL (Fin (∑ i : Fin s, d i.succ)) (w.adicCompletion E)) := ⟨_, _, hs, hi⟩
    have h1 := L.prod (d 0) _ (ParLaws.toRep (σ 0)) (ParLaws.toRep σ'') (ParLaws.toRep σ') ⟨e.trans E₁.symm⟩
    have h2 := ih (d := fun i : Fin s => d i.succ) rfl (fun i => σ i.succ) σ'' ⟨.refl _⟩
    rw [List.ofFn_succ]
    exact h1.trans (congrArg _ h2)

end Core

section Record

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
  (T : GlobalTheory.RowTie.WDTie N A) (hL : GlobalTheory.Published.LocalLanglandsGL)

theorem e_lpSumList (w : PlE H) (L : List (A.LP w)) : T.e w (lpSumList L) = sumList (L.map (T.e w)) := by
  induction L with
  | nil => exact T.zero w
  | cons x L ih =>
    change T.e w (A.lpSum x (lpSumList L)) = (T.e w x).lpSum (sumList (L.map (T.e w)))
    rw [T.sum, ih]

end Record

end GlobalTheory.FormDict.RecTLaws
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLocalComponentConjEqInverseTranspose
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjLocComp

open GlobalTheory.TypeTame

theorem map_invTranspose {A B : Type} [CommRing A] [CommRing B] (n : ℕ) (f : A →+* B) (g : GL (Fin n) A) :
    Matrix.GeneralLinearGroup.map f (invTranspose n g) = invTranspose n (Matrix.GeneralLinearGroup.map f g) := by
  apply Units.ext
  rw [invTranspose_val, ← map_inv]
  rfl

theorem exists_conj {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (S : Submodule ℂ (GAf L n → W)) (s : SplitPlace L) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)))
    (hσ : IsLocS S s σ) :
    ∃ (κ : s.w.adicCompletion L ≃+* (conjSP s).w.adicCompletion L)
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((conjSP s).w.adicCompletion L))) (e : σ.V ≃ₗ[ℂ] σ'.V),
      Continuous κ ∧ (∀ x : L, κ (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) ∧
      IsLocS S (conjSP s) σ' ∧
      ∀ g a, e (σ.ρ (invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a) := by
  obtain ⟨i, T, hi, hiL, hTi, hTm, hTe⟩ := hσ
  obtain ⟨i₀, hi₀, hi₀', hi₀L⟩ := GlobalTheory.SplitComplHomeo.exists_complEquiv L s
  obtain rfl := GlobalTheory.splitPlace_completion_equiv_unique L s i₀ i hi₀ hi hi₀L hiL
  obtain ⟨i', hi', hi'', hi'L⟩ := GlobalTheory.SplitComplHomeo.exists_complEquiv L (conjSP s)
  let j : s.v.adicCompletion (maximalRealSubfield L) ≃+* (conjSP s).w.adicCompletion L := i'
  let κ : s.w.adicCompletion L ≃+* (conjSP s).w.adicCompletion L := i₀.symm.trans j
  have hκ : Continuous κ := hi'.comp hi₀'
  have hκ' : Continuous κ.symm := hi₀.comp hi''
  let ψ : GL (Fin n) ((conjSP s).w.adicCompletion L) →* GL (Fin n) (s.w.adicCompletion L) :=
    (invTranspose n).comp (Matrix.GeneralLinearGroup.map κ.symm.toRingHom)
  have hψc : Continuous ψ :=
    (continuous_invTranspose n).comp (Continuous.units_map _ (continuous_id.matrix_map hκ'))
  have hψκ : ∀ g, ψ (Matrix.GeneralLinearGroup.map κ.toRingHom g) = invTranspose n g := fun g =>
    congrArg (invTranspose n) (GlobalTheory.LocCompSplit.gl_map_symm_map κ g)
  have hψs : Function.Surjective ψ := fun g =>
    ⟨Matrix.GeneralLinearGroup.map κ.toRingHom (invTranspose n g), by rw [hψκ, invTranspose_invTranspose]⟩
  have hj : ∀ g : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L)),
      Matrix.GeneralLinearGroup.map j.toRingHom g =
        Matrix.GeneralLinearGroup.map κ.toRingHom (Matrix.GeneralLinearGroup.map i₀.toRingHom g) := fun g => by
    refine Units.ext (Matrix.ext fun a b => ?_)
    show j (g.val a b) = j (i₀.symm (i₀ (g.val a b)))
    rw [RingEquiv.symm_apply_apply]
  let σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((conjSP s).w.adicCompletion L)) :=
    ⟨σ.V, σ.ρ.comp ψ, fun v => (σ.smooth v).preimage hψc,
      GlobalTheory.LocCompSplit.isIrreducible_comp_of_surjective σ.ρ ψ hψs σ.irr⟩
  refine ⟨κ, σ', LinearEquiv.refl ℂ σ.V, hκ, fun x => ?_, ⟨i', T, hi', hi'L, hTi, hTm, fun x hx a => ?_⟩, fun g a => ?_⟩
  · rw [← hi'L, conjSP_i, IsCMField.complexConj_apply_apply, ← hiL]
    show j (i₀.symm (i₀ (s.i x))) = j (s.i x)
    rw [RingEquiv.symm_apply_apply]
  · have h1 : ψ (Matrix.GeneralLinearGroup.map j.toRingHom (invTranspose n (s.loc n x))) =
        Matrix.GeneralLinearGroup.map i₀.toRingHom (s.loc n x) := by
      rw [hj, hψκ, map_invTranspose, invTranspose_invTranspose]
    have h2 := hTe x hx a
    rw [← h1, ← conjSP_loc] at h2
    exact h2
  · show σ.ρ (invTranspose n g) a = σ.ρ (ψ (Matrix.GeneralLinearGroup.map κ.toRingHom g)) a
    rw [hψκ]

theorem exists_isLocS_conjSP : ∀ (D : D7) (n : ℕ) (π : NG.AutRep D.host.E n) (s : SplitPlace D.host.E)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion D.host.E))), IsLocS π.S s σ →
    ∃ (κ : s.w.adicCompletion D.host.E ≃+* (GlobalTheory.TypeTame.conjSP s).w.adicCompletion D.host.E)
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).w.adicCompletion D.host.E))) (e : σ.V ≃ₗ[ℂ] σ'.V),
      Continuous κ ∧ (∀ x : D.host.E, κ (algebraMap D.host.E _ x) = algebraMap D.host.E _ (D.host.conj x)) ∧
      IsLocS π.S (GlobalTheory.TypeTame.conjSP s) σ' ∧
      ∀ g a, e (σ.ρ (GlobalTheory.TypeTame.invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a) := by
  intro D n π s σ hσ
  obtain ⟨κ, σ', e, h1, h2, h3, h4⟩ := exists_conj π.S s σ hσ
  exact ⟨κ, σ', e, h1, fun x => by rw [h2, GlobalTheory.SplitPlaceOver.host_conj_eq'], h3, h4⟩

end GlobalTheory.ConjLocComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatible
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.SerSys.SuppTame

section Chain

open GlobalTheory.LocGL

theorem isIrreducible_of_isIrrRep {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : IsIrrRep ρ) : ρ.IsIrreducible := by
  obtain ⟨hn, hW⟩ := h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => hv ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h1 : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← e] at h1
    exact (Submodule.mem_bot ℂ).1 h1
  · rcases hW S.toSubmodule (fun x w hw => S.apply_mem_toSubmodule x hw) with h0 | h1
    · exact Or.inl (Subrepresentation.ext (by rw [h0]; rfl))
    · exact Or.inr (Subrepresentation.ext (by rw [h1]; rfl))

theorem isIrrRep_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : IsIrrRep ρ := by
  haveI := h
  refine ⟨?_, fun W hW => ?_⟩
  · by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have : (⊥ : Subrepresentation ρ) = ⊤ := Subrepresentation.ext (Subsingleton.elim (α := Submodule ℂ V) _ _)
    exact bot_ne_top this
  · rcases eq_bot_or_eq_top (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation ρ) with h0 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h0)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)

theorem hasSupport_zero (hZ : GlobalTheory.Published.ZelevinskyPolynomialRing) {g : ℕ} [Fact g.Prime] {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin 0) ℚ_[g]) V) (hs : GlobalTheory.PRep.IsSmooth π)
    (hi : π.IsIrreducible) : HasSupport π (0 : Multiset (IrrGL (k := ℚ_[g]))) := by
  obtain ⟨s, hs'⟩ := SupportRing.exists_hasSupport hZ (IrrGL.of π hs hi)
  have h1 : HasSupport π s := hs'.of_equiv (IrrGL.equivOf π hs hi).symm
  have h2 := h1.sum_fst
  rw [Fintype.card_fin] at h2
  have h3 : s = 0 := by
    by_contra hne
    obtain ⟨y, hy⟩ := Multiset.exists_mem_of_ne_zero hne
    have h4 := (h1.isCusp hy).1
    have h5 : y.1 ≤ (s.map Sigma.fst).sum := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hy)
    omega
  rwa [h3] at h1

theorem chain : GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (g : ℕ) [Fact g.Prime] (π : Supp.GLRep g), IsIrrRep π.2.ρ → GlobalTheory.PRep.IsSmooth π.2.ρ → ∃ (L : List (Supp.GLRep g)) (y : List (GlobalTheory.LocGL.IrrGL (k := ℚ_[g]))), Supp.InInd π L ∧ (∀ ρ ∈ L, 0 < ρ.1 ∧ IsIrrRep ρ.2.ρ ∧ GlobalTheory.PRep.IsSmooth ρ.2.ρ ∧ ρ.2.ρ.IsIrreducible ∧ GlobalTheory.SmGL.IsCuspidal ρ.2.ρ) ∧ GlobalTheory.LocGL.HasSupport π.2.ρ (y : Multiset (GlobalTheory.LocGL.IrrGL (k := ℚ_[g]))) ∧ List.Forall₂ (fun (ρ : Supp.GLRep g) (x : GlobalTheory.LocGL.IrrGL (k := ℚ_[g])) => ∃ (hs : GlobalTheory.PRep.IsSmooth ρ.2.ρ) (hi : ρ.2.ρ.IsIrreducible), (GlobalTheory.LocGL.IrrGL.of ρ.2.ρ hs hi).Inert x) L y := by
  intro hZ g _
  have H : ∀ (N : ℕ) (π : Supp.GLRep g), π.1 = N → IsIrrRep π.2.ρ → GlobalTheory.PRep.IsSmooth π.2.ρ →
      ∃ (L : List (Supp.GLRep g)) (y : List (IrrGL (k := ℚ_[g]))), Supp.InInd π L ∧
        (∀ ρ ∈ L, 0 < ρ.1 ∧ IsIrrRep ρ.2.ρ ∧ GlobalTheory.PRep.IsSmooth ρ.2.ρ ∧ ρ.2.ρ.IsIrreducible ∧
          GlobalTheory.SmGL.IsCuspidal ρ.2.ρ) ∧ HasSupport π.2.ρ (y : Multiset (IrrGL (k := ℚ_[g]))) ∧
        List.Forall₂ (fun (ρ : Supp.GLRep g) (x : IrrGL (k := ℚ_[g])) =>
          ∃ (hs : GlobalTheory.PRep.IsSmooth ρ.2.ρ) (hi : ρ.2.ρ.IsIrreducible), (IrrGL.of ρ.2.ρ hs hi).Inert x) L y := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro π hN hπ hs
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · subst h0
        refine ⟨[], [], Supp.InInd.nil π hN hπ, by simp, ?_, List.Forall₂.nil⟩
        obtain ⟨n, π⟩ := π
        simp only at hN
        subst hN
        exact hasSupport_zero hZ _ hs (isIrreducible_of_isIrrRep hπ)
      · obtain ⟨a, b, hab, W, W', _, _, _, _, σ, ρ, hb, hσs, hσi, hρs, hρi, hρc, φ, hφ⟩ :=
          GlobalTheory.JacFactor.exists_map_jac₂ ℚ_[g] π.1 _ π.2.ρ hs (isIrreducible_of_isIrrRep hπ) (hN ▸ hpos)
        have hM : Supp.MapsToProd π.2.ρ σ ρ := GlobalTheory.GLp.Supp.mapsToProd_of_jac₂ g a b π.1 hab _ _ _ π.2.ρ σ ρ φ hφ
        let σ' : Supp.GLRep g := ⟨a, Rep.of σ⟩
        let ρ' : Supp.GLRep g := ⟨b, Rep.of ρ⟩
        obtain ⟨Lσ, yσ, hI, hL, hS, hF⟩ :=
          ih a (by omega) σ' rfl (isIrrRep_of_isIrreducible hσi) hσs
        have hρsupp : HasSupport ρ {IrrGL.of ρ hρs hρi} :=
          (hasSupport_self (IrrGL.isCusp_of.2 ⟨hb, hρc⟩)).of_equiv (IrrGL.equivOf ρ hρs hρi).symm
        obtain ⟨μ₁, μ₂, h₁, h₂, hsupp⟩ := GlobalTheory.IndChain.SuppStep.supp_of_mapsToProd hZ g _ _ _ _ _ _ π.2.ρ σ ρ hs (isIrreducible_of_isIrrRep hπ) hM
          yσ {IrrGL.of ρ hρs hρi} hS hρsupp
        refine ⟨ρ' :: Lσ, (IrrGL.of ρ hρs hρi).tw μ₂ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₂) ::
          yσ.map (fun x => x.tw μ₁ (GlobalTheory.SmGL.isSmoothChar_of_isUnram h₁)), ?_, ?_, ?_, ?_⟩
        · exact Supp.InInd.cons π σ' ρ' Lσ hπ (isIrrRep_of_isIrreducible hρi) hI hM
        · exact List.forall_mem_cons.2 ⟨⟨hb, isIrrRep_of_isIrreducible hρi, hρs, hρi, hρc⟩, hL⟩
        · convert hsupp using 1
          rw [← Multiset.cons_coe, ← Multiset.map_coe, Multiset.map_singleton, add_comm, Multiset.singleton_add]
        · refine List.Forall₂.cons ⟨hρs, hρi, μ₂, h₂, rfl⟩ ?_
          refine List.forall₂_map_right_iff.2 (hF.imp fun ρ x ⟨hs, hi, hin⟩ => ⟨hs, hi, ?_⟩)
          exact IrrGL.inert_equivalence.trans hin ⟨μ₁, h₁, rfl⟩
  intro π hπ hs
  exact H _ π rfl hπ hs

end Chain

end GlobalTheory.SerSys.SuppTame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachShiftMemOfExpansions
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

section Core

open TensorProduct Formalism.MainNotions.RamifiedCoefficientChains.Sh Formalism.MainNotions.N.Pv.LocalLengthBound.Ser Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt
open Formalism.MainNotions.CrystallineLiftingInputs (DL)
open Formalism.MainNotions.LiftingTheory (qp)
open Formalism.MainNotions.WachCoordinates (FilLev)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem wachExp_diag_shift_iff {M : Type} [AddCommGroup M] [Module LL M] {Fl : ℤ → Submodule LL M}
    (hF : Antitone Fl) {m : ℤ} {d : ℤ → M} (hd : ∀ k < m, d k = 0) (u : PowerSeries LL)
    (hu : IsUnit u) (y : ℕ) :
    (∀ k, conv ((u * PowerSeries.X) ^ y) d k ∈ Fl (-k)) ↔ ∀ k, d k ∈ Fl (-k - y) := by
  have hd' : LB m d := hd
  have hu0 : PowerSeries.constantCoeff (u ^ y) ≠ 0 :=
    ((hu.pow y).map PowerSeries.constantCoeff).ne_zero
  have e : conv ((u * PowerSeries.X) ^ y) d = fun k => smulS (u ^ y) d (k - y) := by
    show smulS ((u * PowerSeries.X) ^ y) d = _
    rw [mul_comm, mul_pow, smulS_mul hd', smulS_X_pow (LB_smulS hd' _)]
  rw [e]
  constructor
  · intro h k
    have h1 : Dg Fl (-(y : ℤ)) (smulS (u ^ y) d) := fun j => by
      have := h (j + y)
      simp only [add_sub_cancel_right] at this
      rwa [show -(y : ℤ) - j = -(j + y) by ring]
    have h2 := Dg_smulS hF (LB_smulS hd' _) h1 (u ^ y)⁻¹ k
    rw [smulS_inv hd' _ hu0] at h2
    rwa [show -k - (y : ℤ) = -(y : ℤ) - k by ring]
  · intro h k
    have h1 : Dg Fl (-(y : ℤ)) d := fun j => by
      rw [show -(y : ℤ) - j = -j - y by ring]; exact h j
    have h2 := Dg_smulS hF hd' h1 (u ^ y) (k - y)
    rwa [show -(y : ℤ) - (k - y) = -k by ring] at h2

theorem wachExp_mem_iff (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hRg : ExpRing W)
    (hRu : ExpRules W) (hCr : ExpCrit W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) (i : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR) (hx : DL W T i x) (hd : IsExp W T i ζ x d)
    (Y : ℕ) (hY : qp W ^ Y • x ∈ W.N T) (y : ℕ) :
    qp W ^ y • x ∈ W.N T ↔ ∀ k, d k ∈ FilLev W T i 0 (-k - y) := by
  have hK : Module.finrank K₀ K = 1 := Formalism.MainNotions.UnusedSlot80.SatW.finrank_one_of_bij' hA.1
  obtain ⟨h9r, -⟩ := (h9 T hT hA.2.1 hA.2.2).2.2 hK
  have hR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W h9r
  have hqΔ := Formalism.MainNotions.LiftingTheory.lifta_qΔ W hR.πΔ
  have hDL : DL W T i (qp W ^ y • x) := by
    refine ⟨by rw [smul_comm, hx.1], fun δ hδ => ?_⟩
    rw [γD_smul', map_pow, hqΔ δ hδ, hx.2 δ hδ]
  obtain ⟨⟨u, hu, hq⟩, -, -⟩ := hRg hA i ζ hζ
  have hE := (hRu hA T hT i ζ hζ).2.2.2.2.1 (qp W ^ y) x d hd
  have hN : qp W ^ Y • (qp W ^ y • x) ∈ W.N T := by
    rw [smul_comm]; exact (W.N T).smul_mem _ hY
  rw [(hCr hA T hT i ζ hζ _ _ hDL hE).1 ⟨Y, hN⟩, map_pow, hq]
  obtain ⟨m, hm⟩ := hd.1
  exact wachExp_diag_shift_iff (Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T i 0) hm u hu y

theorem wachShift_mem_of_exp [NeZero n] (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hRg : ExpRing W) (hRu : ExpRules W) (hCr : ExpCrit W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hp : (PD.p : LL) ≠ 0) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) (y' Y : ℕ) (cO : ℤ → O)
    (hc : ∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O))
    (xs : List ℤ)
    (hxs : ∀ (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i → IsJumpV PD T.ρ τ a →
      y' < j → j ≤ Y → a + (j : ℤ) ∈ xs)
    (seq : ℕ → W.DD T) (h0 : DL W T i (seq 0)) (h0N : qp W ^ Y • seq 0 ∈ W.N T)
    (hrec : ∀ k < xs.length, W.π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) =
      W.γD T W.gam (seq k) - seq k) :
    DL W T i (seq xs.length) ∧ qp W ^ y' • seq xs.length ∈ W.N T := by
  classical
  have hU := Formalism.MainNotions.UnusedSlot35.DssRec.π₀_unit W h9 hA T hT
  have hDS := rToolMod_dStab W h9
  have hQ : ∀ k ≤ xs.length, QLattice W T i Y (seq k) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨h0, h0N⟩
    | succ k ih =>
      intro hk
      have hk' : k < xs.length := hk
      have e : seq (k + 1) = derivationOnWachModule W T (seq k) + (-cO (xs.getD k 0)) • seq k := by
        have h1 : seq (k + 1) + cO (xs.getD k 0) • seq k = derivationOnWachModule W T (seq k) :=
          Formalism.MainNotions.UnusedSlot35.DssRec.smul_inj W.π₀ hU (by rw [hrec k hk', uniformizer_smul_derivation W T hU]; rfl)
        rw [← h1, neg_smul, add_neg_cancel_right]
      rw [e]
      exact qLattice_add W T (qLattice_derivation W T hDS hA hT i Y (ih hk'.le))
        (qLattice_smul W T _ (ih hk'.le))
  refine ⟨(hQ _ le_rfl).1, ?_⟩
  obtain ⟨⟨u, hu, hq⟩, hπ0, -⟩ := hRg hA i ζ hζ
  obtain ⟨hex, -, hadd, hsO, hsA, hγ, -⟩ := hRu hA T hT i ζ hζ
  have hqne : W.lev i ζ (qp W ^ Y) ≠ 0 := by
    rw [map_pow, hq]
    exact pow_ne_zero _ (mul_ne_zero hu.ne_zero PowerSeries.X_ne_zero)
  have hf : ∀ k : ℕ, ∃ d : ℤ → T.V ⊗[Qp] BdR, (∃ m : ℤ, ∀ j < m, d j = 0) ∧
      (k ≤ xs.length → IsExp W T i ζ (seq k) d) := by
    intro k
    by_cases hk : k ≤ xs.length
    · obtain ⟨d, hd, -⟩ := hex (seq k) _ (hQ k hk).2 hqne
      exact ⟨d, hd.1, fun _ => hd⟩
    · exact ⟨0, ⟨0, fun _ _ => rfl⟩, fun h => absurd h hk⟩
  choose f hfb hfe using hf
  rw [wachExp_mem_iff W h9 hRg hRu hCr hA T hT i ζ hζ _ _ (hQ _ le_rfl).1 (hfe _ le_rfl) Y
    (hQ _ le_rfl).2 y']
  have hf0 := (wachExp_mem_iff W h9 hRg hRu hCr hA T hT i ζ hζ _ _ h0 (hfe 0 (Nat.zero_le _)) Y
    h0N Y).1 h0N
  let uL : LLˣ := Units.map (algebraMap O LL : O →* LL) (W.χΓ W.gam)
  refine filtLaurent_shift_line LL _ (fun a => FilLev W T i 0 a)
    (Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T i 0) uL (W.lev i ζ W.π₀) (fun x => algebraMap O LL (cO x))
    (by rw [hπ0]; exact neg_ne_zero.2 hp) (fun x => ?_) y' Y xs (fun a j ha hj hj' => ?_) f hfb
    (fun m hm k => ?_) hf0
  · have h1 := congrArg (algebraMap O LL) (hc x)
    rw [map_mul, map_natCast, map_sub, map_one] at h1
    have h2 : ((uL ^ (-x) : LLˣ) : LL) = algebraMap O LL (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) := by
      rw [← map_zpow]; rfl
    rw [hπ0, h2]
    linear_combination -h1
  · let e : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hA.1
    let τ : K →ₐ[Qp] LL := (W.emb i).comp e.symm.toAlgHom
    have hτ : Formalism.MainNotions.LiftingTheory.Over W τ i := by
      apply AlgHom.ext
      intro z
      show W.emb i (e.symm (e z)) = W.emb i z
      rw [e.symm_apply_apply]
    have hF : ∀ b : ℤ, FildR PD T.ρ τ b = FilLev W T i 0 b := by
      intro b
      rw [((hD hA.1 T.V T.ρ hT).2 τ).2.2 b, show τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i from hτ]
      unfold FilLev
      simp only [Nat.cast_zero, sub_zero, pow_zero, Module.End.one_eq_id, Submodule.map_id]
    refine hxs τ a j hτ ?_ hj hj'
    unfold IsJumpV
    rw [hF, hF]
    exact ha
  · have e1 := hfe m hm.le
    have e2 := hfe (m + 1) hm
    have hL := hsA W.π₀ _ _ (hadd _ _ _ _ e2 (hsO (cO (xs.getD m 0)) _ _ e1))
    have hR := hadd _ _ _ _ (hγ _ _ e1) (hsO (-1) _ _ e1)
    have ex : W.γ T (seq m) + (-1 : O) • seq m =
        W.π₀ • (seq (m + 1) + cO (xs.getD m 0) • seq m) := by
      rw [hrec m hm, neg_one_smul, ← sub_eq_add_neg]; rfl
    rw [ex] at hR
    have hN : qp W ^ Y • (W.π₀ • (seq (m + 1) + cO (xs.getD m 0) • seq m)) ∈ W.N T := by
      rw [smul_comm]
      exact (W.N T).smul_mem _
        (qLattice_add W T (hQ (m + 1) hm) (qLattice_smul W T _ (hQ m hm.le))).2
    have h3 := congrFun ((hex _ _ hN hqne).unique hL hR) k
    have h2 : ((uL ^ k : LLˣ) : LL) = (algebraMap O LL (W.χΓ W.gam : O)) ^ k := by
      rw [Units.val_zpow_eq_zpow_val]; rfl
    rw [h2, sub_smul, one_smul]
    refine Eq.trans ?_ (h3.trans ?_)
    · rfl
    · simp [sub_eq_add_neg]

end Core

set_option synthInstance.maxHeartbeats 100000 in
theorem wachShift_mem_of_expansions : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc), ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL), Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hA.2.2) → Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing ((HW l).W K 1 LL hA.2.2) → Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules ((HW l).W K 1 LL hA.2.2) → Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit ((HW l).W K 1 LL hA.2.2) → Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris ((D.loc l).PD K) ↥LL.1 → ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (y' Y : ℕ) (cO : ℤ → ↥(OL LL)), (∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x = 1 - (((((HW l).W K 1 LL hA.2.2).χΓ ((HW l).W K 1 LL hA.2.2).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL))) → ∀ xs : List ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL hA.2.2) τ i → IsJumpV ((D.loc l).PD K) T.ρ τ a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) → ∀ seq : ℕ → ((HW l).W K 1 LL hA.2.2).DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq 0) → Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ Y • seq 0 ∈ ((HW l).W K 1 LL hA.2.2).N T → (∀ k < xs.length, ((HW l).W K 1 LL hA.2.2).π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) = ((HW l).W K 1 LL hA.2.2).γD T ((HW l).W K 1 LL hA.2.2).gam (seq k) - seq k) → Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq xs.length) ∧ Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ y' • seq xs.length ∈ ((HW l).W K 1 LL hA.2.2).N T := by
  intro D HW l _ K LL hA h9 hRg hRu hCr hD T hT i y' Y cO hc xs hxs seq h0 h0N hrec
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨ζ, hζ⟩ := Formalism.MainNotions.UnusedSlot80.exists_prim_of_good D hA.2.2
  refine wachShift_mem_of_exp _ h9 hRg hRu hCr hD
    (Formalism.MainNotions.UnusedSlot80.caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1) ?_ ζ (by rw [hp]; exact hζ) T hT i y' Y
    cO (fun x => by rw [hp]; exact hc x) xs hxs seq h0 h0N hrec
  rw [hp]
  exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

end GlobalTheory
end

