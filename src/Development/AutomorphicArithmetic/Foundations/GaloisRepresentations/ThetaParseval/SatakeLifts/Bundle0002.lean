module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.CompUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.CompUnitPf
section
open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CuspRep UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.TP.Loc.compUnit :
    UpperTheory.Gal.TP.Loc.CompUnit := by
  intro E _ _ _ n U hU w hw τ hτ
  obtain ⟨e, he⟩ := _root_.GlobalTheory.locU_equiv_GL E n w hw
  obtain ⟨B, hh, hp, hd, hi⟩ := GlobalTheory.DefU.Petersson.exists_invariant_pos_form E n
  obtain ⟨hirr, f, h0, hf, h2⟩ := hτ
  have key : ∀ g, ∃ x : GlobalTheory.UnitaryBC.UA E n, ∀ v, f (τ.ρ g v) = GlobalTheory.UnitaryBC.RU E n x (f v) := fun g =>
    ⟨(e.symm g).1, fun v => by
      have h3 := h2 (e.symm g) v
      have hy : ((GlobalTheory.UnitaryBC.cLoc w).comp (GlobalTheory.UnitaryBC.locU n w).subtype) (e.symm g) = g := by
        have := he (e.symm g)
        rw [e.apply_symm_apply] at this
        exact this.symm
      rw [hy] at h3
      exact h3⟩
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    have hst : ∀ g, ∀ v ∈ LinearMap.ker f, τ.ρ g v ∈ LinearMap.ker f := fun g v hv => by
      obtain ⟨x, hx⟩ := key g
      rw [LinearMap.mem_ker, hx, LinearMap.mem_ker.1 hv, map_zero]
    rcases ((GlobalTheory.CuspRep.isIrreducible_iff _).1 hirr).2 (LinearMap.ker f) hst with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) h0
  let f' : τ.V →ₗ[ℂ] GlobalTheory.DefU.autU E n := f.codRestrict _ (fun v => hU.aut _ (hf v))
  have hf' : ∀ v, f' v = 0 → v = 0 := fun v h =>
    hinj ((congrArg Subtype.val h).trans (map_zero f).symm)
  have heq : ∀ g, ∃ x, ∀ v, f' (τ.ρ g v) = GlobalTheory.DefU.autRep E n x (f' v) := fun g => by
    obtain ⟨x, hx⟩ := key g
    exact ⟨x, fun v => Subtype.ext (hx v)⟩
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v u => B (f' u) (f' v))
    (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp), ?_, ?_, ?_⟩
  · intro v u
    simpa using (hh (f' u) (f' v)).symm
  · intro v hv
    have hne : B (f' v) (f' v) ≠ 0 := fun h => hv (hf' v (hd _ h))
    have him : (B (f' v) (f' v)).im = 0 := by
      have := congrArg Complex.im (hh (f' v) (f' v))
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    have hre : (B (f' v) (f' v)).re ≠ 0 := fun h => hne (Complex.ext h him)
    exact lt_of_le_of_ne (hp _) (Ne.symm (by simpa using hre))
  · intro g v u
    obtain ⟨x, hx⟩ := heq g
    simp only [LinearMap.mk₂'ₛₗ_apply, hx]
    exact hi x _ _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PullGoodPf
section
open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CuspRep UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem map_surj {k k' : Type} [Field k] [Field k'] (c : k →+* k') (hs : Function.Surjective c) (n : ℕ) :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := Fin n) c) := by
  intro g
  let e : k ≃+* k' := RingEquiv.ofBijective c ⟨c.injective, hs⟩
  refine ⟨Matrix.GeneralLinearGroup.map (n := Fin n) (e.symm : k' →+* k) g, ?_⟩
  apply Units.ext
  ext i j
  have : c (e.symm ((g : Matrix (Fin n) (Fin n) k') i j)) = (g : Matrix (Fin n) (Fin n) k') i j :=
    e.apply_symm_apply _
  simpa using this

private theorem map_cont {k k' : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [Field k']
    [TopologicalSpace k'] [IsTopologicalRing k'] (c : k →+* k') (hc : Continuous c) (n : ℕ) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) c) := by
  have h : Continuous (RingHom.mapMatrix (m := Fin n) c : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) k') :=
    Continuous.matrix_map continuous_id hc
  exact Continuous.units_map (RingHom.mapMatrix (m := Fin n) c : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) k').toMonoidHom h

private theorem irr_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ H X) (φ : H' →* H) (hφ : Function.Surjective φ) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ) := by
  obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 h
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h1 W fun g v hv => ?_⟩
  obtain ⟨g', rfl⟩ := hφ g
  exact hW g' v hv

theorem UpperTheory.Gal.TP.Loc.pullGood :
    UpperTheory.Gal.TP.Loc.PullGood := by
  intro k k' _ _ _ _ _ _ c hc hs n V _ _ ρ
  refine ⟨fun h => isSmooth_comp h _ (map_cont c hc n), fun h => irr_comp ρ _ (map_surj c hs n) h, ?_⟩
  rintro ⟨B, h1, h2, h3⟩
  exact ⟨B, h1, h2, fun g v w => h3 _ v w⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.SatDet
section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem range_map_eq {α : Type} (t : ℕ) (F : ℕ → α) :
    (Finset.univ : Finset (Fin t)).val.map (fun i : Fin t => F (i : ℕ)) = (Finset.range t).val.map F := by
  have h : (Finset.range t).val = (Finset.univ : Finset (Fin t)).val.map (fun i : Fin t => (i : ℕ)) := by
    have h' : Finset.range t = (Finset.univ : Finset (Fin t)).map Fin.valEmbedding := by
      ext i
      simp only [Finset.mem_range, Finset.mem_map, Finset.mem_univ, true_and, Fin.valEmbedding_apply]
      exact ⟨fun hi => ⟨⟨i, hi⟩, rfl⟩, fun ⟨j, hj⟩ => hj ▸ j.2⟩
    rw [h', Finset.map_val]
    rfl
  rw [h, Multiset.map_map]
  rfl

theorem UpperTheory.Gal.TP.Loc.satDet :
    UpperTheory.Gal.TP.Loc.SatDet := by
  intro K _ _ w t c hc ϖ hϖ
  have hv : valuation (w.adicCompletion K) (ϖ : w.adicCompletion K) = uniformizer (w.adicCompletion K) :=
    GlobalTheory.MuInert.valuation_eq_uniformizer w hϖ
  have hord : Formalism.UG.ordV K w (ϖ : w.adicCompletion K) = 1 := by
    rw [GlobalTheory.LGrp.BorelCompletion.ordV_eq, show Valued.v (ϖ : w.adicCompletion K) = _ from hϖ]
    rfl
  have h := GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake K w t _ _ _ (hasSatake_detRep hc hv)
  have hm : GlobalTheory.LFun.seg w (c ϖ) t = (Finset.univ : Finset (Fin t)).val.map
      (fun i : Fin t => c ϖ * absPow (w.adicCompletion K) (((i : ℕ) : ℂ) - ((t : ℂ) - 1) / 2) ϖ) := by
    rw [GlobalTheory.LFun.seg, ← range_map_eq]
    refine Multiset.map_congr rfl fun i _ => ?_
    congr 1
    ext
    rw [GlobalTheory.SatInd.val_absPow_completion, hord]
    simp only [GlobalTheory.LFun.coe_npowU, GlobalTheory.LFun.npow, Formalism.UG.qV]
    congr 1
    push_cast
    ring
  rw [hm]
  exact h
end

