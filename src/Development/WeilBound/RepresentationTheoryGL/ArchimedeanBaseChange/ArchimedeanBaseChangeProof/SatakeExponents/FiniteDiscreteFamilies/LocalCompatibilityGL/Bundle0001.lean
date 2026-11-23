module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FinDiscNOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1144
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0636

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.FixedMonoBo
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.F5.Bo

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem isoV_symm' {V V' : Submodule ℂ (Sm E N)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (h : SpectralAccumulation.IsoV V V') : SpectralAccumulation.IsoV V' V := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.symm, fun o φ ψ e => ?_⟩
  have hm : act o (T.symm φ : Sm E N) ∈ V := hV o _ (T.symm φ).2
  have h1 := hT o (T.symm φ) ⟨_, hm⟩ rfl
  rw [LinearEquiv.apply_symm_apply, ← e] at h1
  have h2 : T ⟨_, hm⟩ = ψ := Subtype.ext h1
  rw [← h2, LinearEquiv.symm_apply_apply]

theorem isoV_trans' {U V V' : Submodule ℂ (Sm E N)} (h : SpectralAccumulation.IsoV U V) (h' : SpectralAccumulation.IsoV V V') : SpectralAccumulation.IsoV U V' := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨T', hT'⟩ := h'
  exact ⟨T.trans T', fun o φ ψ e => hT' o (T φ) (T ψ) (hT o φ ψ e)⟩

end

end PositivityTheory.Rg.BcB.F.F5.Bo

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.LocIso
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.F5.Bo

namespace LocalIsomorphism

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

theorem finRep_eq_act (h : GL (Fin N) (Af E)) (φ : Sm E N) : finRep E N h φ = act (.fin h) φ := by
  rfl

end LocalIsomorphism

theorem LocIso_holds : LocIso := by
  intro E _ _ _ N V V' hV w σ hσ
  obtain ⟨f, hf0, hfV, hfeq⟩ := hσ
  obtain ⟨T, hT⟩ := hV
  refine ⟨(Submodule.subtype V').comp ((T : V →ₗ[ℂ] V').comp (f.codRestrict V hfV)), ?_, ?_, ?_⟩
  · intro h0
    apply hf0
    refine LinearMap.ext fun v => ?_
    have h1 := LinearMap.congr_fun h0 v
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Submodule.coe_subtype,
      ZeroMemClass.coe_eq_zero, LinearEquiv.coe_coe] at h1
    have h2 : f.codRestrict V hfV v = 0 := by
      simpa using (T.map_eq_zero_iff).1 h1
    simpa [LinearMap.codRestrict] using congrArg Subtype.val h2
  · intro v
    exact (T _).2
  · intro g v
    have key := hT (.fin (locGL E N w g)) (f.codRestrict V hfV v) (f.codRestrict V hfV (σ.ρ g v))
      (by simp only [LinearMap.codRestrict_apply]; rw [hfeq, LocalIsomorphism.finRep_eq_act])
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
    rw [key, LocalIsomorphism.finRep_eq_act]

end PositivityTheory.Rg.BcB.F.F5.Bo

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.LocUniq
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.DiscLocEx

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.F5.Bo.LocalUniqueness

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem isoPart_opD {V : Submodule ℂ (Sm E a)} (hV : _root_.GlobalTheory.CuspRep.IsStable V) (w : HeightOneSpectrum (𝓞 E)) {W : Type}
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) W) (o : Op E a) {x : V}
    (hx : x ∈ GlobalTheory.CuspRep.LocUniq.isoPart σ (locRepD hV w)) :
    opD hV o x ∈ GlobalTheory.CuspRep.LocUniq.isoPart σ (locRepD hV w) := by
  cases o with
  | fin k =>
    exact GlobalTheory.CuspRep.LocUniq.isoPart_fin (finPartD hV) w σ k hx
  | cpt k =>
    refine GlobalTheory.CuspRep.LocUniq.isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx
    change (rt E a (infGL E a (Unitary.toUnits k)) * rt E a (finGL E a (locGL E a w g))) y.1 =
      (rt E a (finGL E a (locGL E a w g)) * rt E a (infGL E a (Unitary.toUnits k))) y.1
    rw [← map_mul, ← map_mul, infGL_comm]
  | lie X =>
    refine GlobalTheory.CuspRep.LocUniq.isoPart_comm σ _ _ (fun g y => Subtype.ext ?_) hx
    exact LinearMap.congr_fun (lie_rt_fin X (locGL E a w g)) y.1

theorem equiv_of_isLocCompGL {V : Submodule ℂ (Sm E a)} (hV : IsDiscrete V) (w : HeightOneSpectrum (𝓞 E))
    (σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E))) (h : IsLocCompGL V w σ) (h' : IsLocCompGL V w σ') :
    Nonempty (σ.ρ.Equiv σ'.ρ) := by
  obtain ⟨f, h0, hfV, hf⟩ := h
  obtain ⟨f', h0', hfV', hf'⟩ := h'
  let F : σ.V →ₗ[ℂ] V := f.codRestrict V hfV
  let F' : σ'.V →ₗ[ℂ] V := f'.codRestrict V hfV'
  have hF : ∀ g v, F (σ.ρ g v) = locRepD hV.stable w g (F v) := fun g v => Subtype.ext (hf g v)
  have hF' : ∀ g v, F' (σ'.ρ g v) = locRepD hV.stable w g (F' v) := fun g v => Subtype.ext (hf' g v)
  have := σ.irred
  have := σ'.irred
  refine GlobalTheory.CuspRep.LocUniq.equiv_of_isoPart σ.ρ σ'.ρ (locRepD hV.stable w) ?_
    ⟨F', fun g => LinearMap.ext (hF' g)⟩ fun e => h0' (LinearMap.ext fun v => ?_)
  · have hm := Submodule.map_injective_of_injective V.injective_subtype
    rcases hV.irred ((GlobalTheory.CuspRep.LocUniq.isoPart σ.ρ (locRepD hV.stable w)).map V.subtype)
      (Submodule.map_subtype_le _ _) (by
        rintro o _ ⟨x, hx, rfl⟩
        exact ⟨_, isoPart_opD hV.stable w σ.ρ o hx, rfl⟩) with h1 | h1
    · refine absurd (LinearMap.ext fun v => ?_) h0
      have h2 : GlobalTheory.CuspRep.LocUniq.isoPart σ.ρ (locRepD hV.stable w) = ⊥ := hm (h1.trans (Submodule.map_bot _).symm)
      have h3 : F v ∈ GlobalTheory.CuspRep.LocUniq.isoPart σ.ρ (locRepD hV.stable w) :=
        Submodule.mem_iSup_of_mem (⟨F, fun g => LinearMap.ext (hF g)⟩ : σ.ρ.IntertwiningMap (locRepD hV.stable w))
          ⟨v, rfl⟩
      rw [h2] at h3
      exact congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h3)
    · exact hm (h1.trans (Submodule.map_subtype_top _).symm)
  · have := congrArg (fun T : σ'.ρ.IntertwiningMap (locRepD hV.stable w) => (T.toLinearMap v : Sm E a)) e
    exact this

end PositivityTheory.Rg.BcB.F.F5.Bo.LocalUniqueness

namespace PositivityTheory.Rg.BcB.F.F5.Bo

theorem LocUniq_holds : LocUniq := by
  intro E _ _ _ N V hV w σ σ' h h'
  obtain ⟨e⟩ := LocalUniqueness.equiv_of_isLocCompGL hV w σ σ' h h'
  exact GlobalTheory.LocGL.IrrGL.of_eq_of.2 ⟨e⟩

end PositivityTheory.Rg.BcB.F.F5.Bo

end
end

