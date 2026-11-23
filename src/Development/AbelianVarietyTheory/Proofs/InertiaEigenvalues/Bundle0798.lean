module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralHilbert90FiniteIdelesTrivialWhereTrivial
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0684
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0102
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntUnitRoot
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntegralHilbertNinety

theorem conj_sig (D : D7) : Formalism.L2.DIV.IsConjOf D.sp.cm.sig := by
  refine ⟨fun h0 => ?_, fun e => star_star e, fun e he => ?_⟩
  · have hs : Function.Surjective (algebraMap D.host.F D.host.E) := fun e => (D.sp.cm.fixed e).1 (AlgHom.congr_fun h0 e)
    have h1 : Module.finrank D.host.F D.host.E = 1 :=
      (LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap D.host.F D.host.E)
        ⟨(algebraMap D.host.F D.host.E).injective, hs⟩)).symm.trans (Module.finrank_self _)
    have := D.sp.cm.deg2
    omega
  · exact (D.sp.cm.fixed e).1 he

theorem swap_sig (D : D7) (w : Af D.host.F ⊗[D.host.F] D.host.E) :
    Formalism.IndefR.Lev.swapAE D (sigR (Af D.host.F) D.sp.cm.sig w) =
      Formalism.UG.sigR D.sp.cm.sig _ (Formalism.IndefR.Lev.swapAE D w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, RingHom.map_add (f := _), RingHom.map_add (f := _)]

abbrev swapEquiv (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E ≃+* Formalism.IndefR.Lev.EAf D :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv

theorem swapEquiv_apply (D : D7) (w : Af D.host.F ⊗[D.host.F] D.host.E) :
    swapEquiv D w = Formalism.IndefR.Lev.swapAE D w := rfl


set_option maxHeartbeats 2000000 in
theorem exists_int_unit_root : ∀ (D : D7) (z : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ),
    (z : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D →
    (∃ y₀ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ, (y₀ : Af D.host.F ⊗[D.host.F] D.host.E) =
      z * sigR (Af D.host.F) D.sp.cm.sig (y₀ : Af D.host.F ⊗[D.host.F] D.host.E)) →
    ∃ y : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ, (y : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧
      ((y⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D ∧
      (y : Af D.host.F ⊗[D.host.F] D.host.E) = z * sigR (Af D.host.F) D.sp.cm.sig (y : Af D.host.F ⊗[D.host.F] D.host.E) := by
  intro D z hz ⟨y₀, hy₀⟩
  have hss : ∀ w, sigR (Af D.host.F) D.sp.cm.sig (sigR (Af D.host.F) D.sp.cm.sig w) = w := fun w => by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show a ⊗ₜ[D.host.F] (D.sp.cm.sig (D.sp.cm.sig x)) = a ⊗ₜ[D.host.F] x
      rw [(conj_sig D).2.1 x]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

  have hzs : (z : Af D.host.F ⊗[D.host.F] D.host.E) * sigR (Af D.host.F) D.sp.cm.sig z = 1 := by
    have h1 : sigR (Af D.host.F) D.sp.cm.sig (y₀ : Af D.host.F ⊗[D.host.F] D.host.E) =
        sigR (Af D.host.F) D.sp.cm.sig z * y₀ := by
      conv_lhs => rw [hy₀]
      rw [map_mul, hss]
    have h2 : (y₀ : Af D.host.F ⊗[D.host.F] D.host.E) = z * sigR (Af D.host.F) D.sp.cm.sig z * y₀ := by
      rw [mul_assoc, ← h1]; exact hy₀
    have h3 := congrArg (· * ((y₀⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E)) h2
    simp only [Units.mul_inv, mul_assoc, mul_one] at h3
    exact h3.symm
  have hzinv : ((z⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) =
      sigR (Af D.host.F) D.sp.cm.sig z := Units.inv_eq_of_mul_eq_one_right hzs

  obtain ⟨z', hz'⟩ : ∃ z' : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ,
      (z' : Formalism.L2.DIV.AfE D.host.F D.host.E) = Formalism.IndefR.Lev.swapAE D z :=
    ⟨Units.map (Formalism.IndefR.Lev.swapAE D).toMonoidHom z, Units.coe_map _ _⟩
  have hconj : ∀ u : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ,
      ((Formalism.L2.DIV.conjId D.sp.cm.sig u : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) =
        Formalism.UG.sigR D.sp.cm.sig (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (u : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    intro u
    rw [Formalism.L2.DIV.conjId, Units.coe_map]
    rfl
  have hU1 : z' ∈ Formalism.L2.DIV.U1 D.sp.cm.sig := by
    rw [Formalism.L2.DIV.U1, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.id_apply]
    apply Units.ext
    rw [Units.val_mul, Units.val_one, hconj, hz', ← swap_sig, ← map_mul, hzs, map_one]
  have hz'inv : ((z'⁻¹ : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E) =
      Formalism.IndefR.Lev.swapAE D ((z⁻¹ : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) :=
    Units.inv_eq_of_mul_eq_one_right (by rw [hz', ← map_mul, Units.mul_inv, map_one])
  have hint : z' ∈ Formalism.L2.DIV.intU D.host.F D.host.E := by
    rw [Formalism.L2.DIV.intU, Submonoid.mem_units_iff]
    refine ⟨?_, ?_⟩
    · rw [hz']
      exact (GlobalTheory.IdemSupport.mem_intAE_iff _).1 hz
    · rw [hz'inv]
      refine (GlobalTheory.IdemSupport.mem_intAE_iff _).1 ?_
      rw [hzinv]
      exact GlobalTheory.DetOnto.sigR_mem_intAE D hz
  obtain ⟨x, hx, hxz, -⟩ := GlobalTheory.TwU.IntegralHilbert90Unramified.exists_integral_h90_preimage_trivial_where_trivial D.host.F D.host.E D.sp.cm.sig (conj_sig D)
    (GlobalTheory.HeckeAdjoint.unramified_host D) z' hU1 hint
  have hx' := (Submonoid.mem_units_iff _ _).1 hx
  have hxe : (x : Formalism.L2.DIV.AfE D.host.F D.host.E) =
      (z' : Formalism.L2.DIV.AfE D.host.F D.host.E) * Formalism.UG.sigR D.sp.cm.sig _ (x : Formalism.L2.DIV.AfE D.host.F D.host.E) := by
    have h := congrArg (fun u : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ =>
      ((u * Formalism.L2.DIV.conjId D.sp.cm.sig x : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E)) hxz
    simp only [Formalism.L2.DIV.h90, MonoidHom.div_apply, MonoidHom.id_apply, div_mul_cancel] at h
    rw [Units.val_mul, hconj] at h
    exact h
  refine ⟨Units.map (swapEquiv D).symm.toRingHom.toMonoidHom x, ?_, ?_, ?_⟩
  · rw [GlobalTheory.IdemSupport.mem_intAE_iff, ← swapEquiv_apply]
    change swapEquiv D ((swapEquiv D).symm (x : Formalism.L2.DIV.AfE D.host.F D.host.E)) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact hx'.1
  · rw [GlobalTheory.IdemSupport.mem_intAE_iff, ← swapEquiv_apply, ← map_inv]
    change swapEquiv D ((swapEquiv D).symm ((x⁻¹ : (Formalism.L2.DIV.AfE D.host.F D.host.E)ˣ) : Formalism.L2.DIV.AfE D.host.F D.host.E)) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact hx'.2
  · apply (swapEquiv D).injective
    change swapEquiv D ((swapEquiv D).symm (x : Formalism.L2.DIV.AfE D.host.F D.host.E)) =
      swapEquiv D ((z : Af D.host.F ⊗[D.host.F] D.host.E) *
        sigR (Af D.host.F) D.sp.cm.sig ((swapEquiv D).symm (x : Formalism.L2.DIV.AfE D.host.F D.host.E)))
    rw [RingEquiv.apply_symm_apply, map_mul, swapEquiv_apply, swapEquiv_apply, swap_sig, ← swapEquiv_apply D
      ((swapEquiv D).symm _), RingEquiv.apply_symm_apply, ← hz']
    exact hxe

end GlobalTheory.IntegralHilbertNinety
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsHeckeDatum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeDatumExists

variable {D : D7}

theorem conj_ne_of_split {P : Pl D.host.E} (h : IsSplitPl D.host P) : Formalism.DivisionValues.conjPl P ≠ P := by
  intro hP
  obtain ⟨x, hx, hy⟩ := h
  refine hy (Formalism.DivisionValues.cO D.host.E x) ?_ ?_
  · show starRingAut (x : D.host.E) = D.host.conj (x : D.host.E)
    rw [starRingAut_apply]
    exact Formalism.BasicNotions.bridge_star_holds D.R D.host _
  · have : Formalism.DivisionValues.cO _ x ∈ (Formalism.DivisionValues.conjPl P).asIdeal := Ideal.mem_map_of_mem _ hx
    rwa [hP] at this

theorem exists_isDC_levG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {α : GA D V}
    (hα : α ∈ GfC V) : ∃ R : Finset (GA D V), Bridge.IsDC (Lev.levG V β L) α R := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hle : Lev.levG V β L ≤ GfC V := fun k hk => hk.1
  have hi := GlobalTheory.HeckeLabels.relIndex_conj_ne_zero (L := GfC V) (GlobalTheory.ParahoricCompact.isCompact_levG V β L)
    (GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L) (fun k hk hk' => ⟨hk, hk'⟩) hα
  rw [inf_eq_left.2 hle] at hi
  obtain ⟨R, r1, r2⟩ := GlobalTheory.HeckeLabels.exists_reps hi
  refine ⟨R, fun a ha => ?_, fun g ⟨k₁, k₂, hg⟩ => ?_⟩
  · obtain ⟨k₁, h₁, k₂, h₂, e⟩ := r1 a ha
    exact ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, e⟩
  · exact r2 g ⟨k₁, k₁.2, k₂, k₂.2, hg⟩

theorem exists_isHeckeDatum : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X),
    ρ.Good → ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool), ∀ (k : ℕ) (P : Pl D.host.E), Formalism.MainNotions.IntegralHeckeForms.HkIdx i k P →
      ∃ α R z, ρ.IsHeckeDatum i j b k P α R z := by
  intro D N X ρ _ i j b k P hk
  obtain ⟨-, hkr, hsp, -⟩ := hk
  obtain ⟨e, he⟩ := GlobalTheory.Hk3.SplitMatch.exists_isIdemAt (conj_ne_of_split hsp)
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  obtain ⟨α, R₀, R₀', hα, -⟩ := GlobalTheory.Hk3.SplitMatch.exists_data he h1 h2 (Wc D j)
  have hA := (hα k (hkr.trans (r_le_rank_Wc j))).1
  obtain ⟨R, hR⟩ := exists_isDC_levG (Wc D j) _ _ hA.1
  have hee : e * e = e := he.1.1
  set u : (AE D)ˣ := Matrix.GeneralLinearGroup.det (matHom (Wc D j) (α k)) with hu
  have huv : (u : AE D) * ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := Units.mul_inv u
  let z : (AE D)ˣ := Units.mkOfMulEqOne (e * u + (1 - e)) (e * ((u⁻¹ : (AE D)ˣ) : AE D) + (1 - e)) (by
    linear_combination ((u : AE D) * ((u⁻¹ : (AE D)ˣ) : AE D) - u - ((u⁻¹ : (AE D)ˣ) : AE D) + 1) * hee + e * huv)
  refine ⟨α k, R, z, ⟨e, ϖ, he, h1, h2, hA⟩, hR, ?_⟩
  show (z : AE D) = idemAt P * (mt (Wc D j) (α k)).det + (1 - idemAt P)
  rw [idemAt_eq he]
  rfl

end GlobalTheory.HeckeDatumExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLadicCoefficientFieldEmbeddingsComplex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.EmbExt

open Cardinal

theorem exists_extend_of_countable {A K : Type} [Field A] [Field K] [Algebra A K] [Countable A]
    (hK : #K ≤ 𝔠) (φ : A →+* ℂ) : ∃ ψ : K →+* ℂ, ∀ a, ψ (algebraMap A K a) = φ a := by
  letI : Algebra A ℂ := φ.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis A K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis A ℂ
  have hA : #A ≤ ℵ₀ := Cardinal.mk_le_aleph0
  have hC : ℵ₀ < #ℂ := by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have ht' : #ℂ = #t := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hA hC
  have hst : #s ≤ #t := by
    rw [← ht', Cardinal.mk_complex]
    exact (Cardinal.mk_le_mk_of_subset (Set.subset_univ _)).trans (by simpa using hK)
  obtain ⟨f⟩ := hst
  have hw : AlgebraicIndependent A (fun x : s => ((f x : t) : ℂ)) :=
    ht.1.comp (fun x => f x) f.injective
  let S := Algebra.adjoin A (Set.range ((↑) : s → K))
  let g : S →ₐ[A] ℂ := (MvPolynomial.aeval (fun x : s => ((f x : t) : ℂ))).comp hs.1.aevalEquiv.symm.toAlgHom
  have hg : Function.Injective g := (show Function.Injective (MvPolynomial.aeval (fun x : s => ((f x : t) : ℂ))) from hw).comp
    hs.1.aevalEquiv.symm.injective
  letI : Algebra S ℂ := g.toRingHom.toAlgebra
  haveI : Module.IsTorsionFree S ℂ := Module.isTorsionFree_iff_algebraMap_injective.2 hg
  haveI : Module.IsTorsionFree S K := Module.isTorsionFree_iff_algebraMap_injective.2 Subtype.val_injective
  haveI : Algebra.IsAlgebraic S K := hs.isAlgebraic
  let ψ : K →ₐ[S] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ψ.toRingHom, fun a => ?_⟩
  have h1 : algebraMap A K a = algebraMap S K (algebraMap A S a) := rfl
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, ψ.commutes]
  exact g.commutes a

end GlobalTheory.EmbExt

namespace GlobalTheory.EmbExt

theorem isAlgebraic_rat_of_isIntegral_int {R F : Type} [CommRing R] [Field F] [CharZero F] (g : R →+* F)
    {y : R} (hy : IsIntegral ℤ y) : IsAlgebraic ℚ (g y) := by
  obtain ⟨p, hp, hev⟩ := hy
  refine ⟨p.map (Int.castRingHom ℚ), (hp.map _).ne_zero, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  have h : (algebraMap ℚ F).comp (Int.castRingHom ℚ) = g.comp (algebraMap ℤ R) := RingHom.ext_int _ _
  rw [h, ← Polynomial.hom_eval₂, hev, map_zero]

end GlobalTheory.EmbExt

namespace GlobalTheory.EmbExt

theorem exists_side_embeddings : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (f0 : ∀ i, Bool → (FractionRing (X.O0 i) →+* ℂ)), (∀ i b x, f0 i b ((if b then X.emb0 i else X.emb0b i) x) = embLL0 D x) → (∀ i k, Cardinal.mk (FractionRing (X.Ok i k)) ≤ Cardinal.continuum) → ∃ (e : ∀ i, Bool → (FractionRing (X.O i) →+* ℂ)) (ek : ∀ i, Bool → ∀ k, FractionRing (X.Ok i k) →+* ℂ), (∀ i b x, e i b (sideEmb X i b x) = embLL0 D x) ∧ (∀ i b k (x : X.O i), ek i b k (algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (algebraMap (X.O i) (X.Ok i k) x)) = e i b (algebraMap (X.O i) (FractionRing (X.O i)) x)) ∧ (∀ i b (y : X.O0 i), IsIntegral ℤ y → e i b (algebraMap (X.O i) (FractionRing (X.O i)) (algebraMap (X.O0 i) (X.O i) y)) = f0 i b (algebraMap (X.O0 i) (FractionRing (X.O0 i)) y)) := by
  intro D N X f0 hf0 hcard
  have hcz : ∀ i, CharZero (FractionRing (X.O0 i)) := fun i => charZero_of_injective_ringHom (X.emb0 i).injective
  have key : ∀ i b, ∃ e : FractionRing (X.O i) →+* ℂ, letI := hcz i; ∀ z : FractionRing (X.O0 i), IsAlgebraic ℚ z →
      e (IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i))
        (L := FractionRing (X.O i)) (X.O_inj i) z) = f0 i b z := by
    intro i b
    letI := hcz i
    let A := algebraicClosure ℚ (FractionRing (X.O0 i))
    haveI : Algebra.IsAlgebraic ℚ A := ⟨fun a => IntermediateField.isAlgebraic_iff.2 (mem_algebraicClosure_iff.1 a.2)⟩
    haveI : Countable A := by
      rw [← Cardinal.mk_le_aleph0_iff]
      exact (Algebra.IsAlgebraic.cardinalMk_le_max ℚ A).trans (by simp)
    let m := IsFractionRing.map (A := X.O0 i) (B := X.O i) (K := FractionRing (X.O0 i))
        (L := FractionRing (X.O i)) (X.O_inj i)
    letI : Algebra A (FractionRing (X.O i)) := (m.comp (algebraMap A (FractionRing (X.O0 i)))).toAlgebra
    have hK : Cardinal.mk (FractionRing (X.O i)) ≤ Cardinal.continuum :=
      (Cardinal.mk_le_of_injective (IsFractionRing.map (A := X.O i) (B := X.Ok i 0) (K := FractionRing (X.O i))
        (L := FractionRing (X.Ok i 0)) (X.Ok_inj i 0)).injective).trans (hcard i 0)
    obtain ⟨ψ, hψ⟩ := exists_extend_of_countable hK ((f0 i b).comp (algebraMap A (FractionRing (X.O0 i))))
    refine ⟨ψ, fun z hz => ?_⟩
    have hzA : z ∈ A := mem_algebraicClosure_iff.2 hz
    exact hψ ⟨z, hzA⟩
  choose e he using key
  have keyk : ∀ i b k, ∃ ek : FractionRing (X.Ok i k) →+* ℂ, ∀ x : X.O i,
      ek (algebraMap (X.Ok i k) (FractionRing (X.Ok i k)) (algebraMap (X.O i) (X.Ok i k) x)) =
        e i b (algebraMap (X.O i) (FractionRing (X.O i)) x) := by
    intro i b k
    letI : Algebra (X.O i) ℂ := ((e i b).comp (algebraMap (X.O i) (FractionRing (X.O i)))).toAlgebra
    haveI : Module.IsTorsionFree (X.O i) ℂ := Module.isTorsionFree_iff_algebraMap_injective.2
      ((e i b).injective.comp (IsFractionRing.injective (X.O i) (FractionRing (X.O i))))
    haveI : Module.IsTorsionFree (X.O i) (FractionRing (X.Ok i k)) := by
      refine Module.isTorsionFree_iff_algebraMap_injective.2 ?_
      rw [IsScalarTower.algebraMap_eq (X.O i) (X.Ok i k) (FractionRing (X.Ok i k))]
      exact (IsFractionRing.injective (X.Ok i k) (FractionRing (X.Ok i k))).comp (X.Ok_inj i k)
    haveI := X.Ok_fin i k
    haveI : Algebra.IsAlgebraic (X.O i) (X.Ok i k) := Algebra.IsIntegral.isAlgebraic
    haveI : Algebra.IsAlgebraic (X.O i) (FractionRing (X.Ok i k)) :=
      (IsFractionRing.isAlgebraic_iff' (X.O i) (X.Ok i k) (FractionRing (X.Ok i k))).1 inferInstance
    let ψ : FractionRing (X.Ok i k) →ₐ[X.O i] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨ψ.toRingHom, fun x => ?_⟩
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← IsScalarTower.algebraMap_apply, ψ.commutes]
    rfl
  choose ek hek using keyk
  refine ⟨e, ek, fun i b x => ?_, hek, fun i b y hy => ?_⟩
  · letI := hcz i
    have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
    have h2 : IsAlgebraic ℚ ((if b then X.emb0 i else X.emb0b i) x) :=
      hx.algHom ((if b then X.emb0 i else X.emb0b i).toRatAlgHom)
    rw [← hf0 i b x, ← he i b _ h2]
    rfl
  · letI := hcz i
    have h2 : IsAlgebraic ℚ (algebraMap (X.O0 i) (FractionRing (X.O0 i)) y) :=
      isAlgebraic_rat_of_isIntegral_int _ hy
    rw [← he i b _ h2]
    simp [IsFractionRing.map, IsLocalization.map_eq]

end GlobalTheory.EmbExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemThPsiOfMemSpan
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries
open Formalism.IndefR.Links
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ser

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}


open Classical in
def specXi (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) : GA D (Wc D j) → ℂ :=
  ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) • ρ.xi i j b Y Q M h P a

theorem exists_mem_thPsi_of_mem_span {ρ : Setup X} {hρ : ρ.Good} {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw}
    {j : Fin D.R.m} {b : Bool} {rd : Rd ρ Y i j b} (T : CellTie hρ Y rd) (hR : RatTwist hρ rd) {k : ℕ}
    {Q : Finset (Pl D.host.E)} {ψ : G D.host.E N.Om →* (X.Ok i k)ˣ} (hψ : TwOK i k Q ψ) (hQ : ClsQ (D := D) Q)
    (d : Y.Dat i ((j : ℕ) + 1) b) {f : GA D (Wc D j) → ℂ}
    (hf : f ∈ Submodule.span (ρ.eOk i b k).range (ρ.gens i j b k Q ψ (T.cls d) (T.coef d))) :
    ∃ z ∈ Formalism.MainNotions.IntegralHeckeForms.ThPsi Y i ((j : ℕ) + 1) b k Q ψ {d}, rdK rd hρ k z = f := by
  induction hf using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨z, hz⟩ := hR k Q ψ hψ hQ _ _ _ (T.dat d) hs
    refine ⟨z, Submodule.subset_span ?_, hz⟩
    exact Set.mem_biUnion (Set.mem_singleton d) ((T.thPsi_iff k Q ψ hψ d z).2 (hz ▸ hs))
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | add f g _ _ hf hg =>
    obtain ⟨z, hz, rfl⟩ := hf
    obtain ⟨z', hz', rfl⟩ := hg
    exact ⟨z + z', add_mem hz hz', map_add _ _ _⟩
  | smul c f _ hf =>
    obtain ⟨z, hz, rfl⟩ := hf
    obtain ⟨c', hc'⟩ := c.2
    refine ⟨c' • z, Submodule.smul_mem _ _ hz, ?_⟩
    rw [map_smulₛₗ]
    change ρ.eOk i b k c' • rdK rd hρ k z = (c : ℂ) • rdK rd hρ k z
    rw [hc']

end Ser

end GlobalTheory.SeriesTie

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SpecLoc

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}


open Classical in
def specLoc (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (PP : ↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M))) (y : Matrix (Fin (Wc D j).rank) (Fin (Vc D j).rank) (kP PP.1)) : ℂ :=
  ∑ c : ZMod (X.l i ^ M), ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) (Pi.single PP c))) : X.Ok i k) *
    ((Base.univFam (univOf Y i (admissibleConjugatePairPlaces X i Q M) M ρ.rc) (ρ.β j) PP.1 c y : ℚ) : ℂ)

def specSer (ρ : Setup X) (Y : NExp D.R D.host D.what₂ D.LL0 N X) (i : X.Tw) (j : Fin D.R.m) (b : Bool) (k : ℕ)
    (Q : Finset (Pl D.host.E)) (M : ℕ) (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ) (h : GA D (Vc D j))
    (P : PolF D (Wc D j).rank (Vc D j).rank) : GA D (Wc D j) → ℂ :=
  twistBy (Wc D j) (ρ.tw i b k Q (χ.comp (Y.delU i Q M))).chi
    (series (ρ.B i j b).F (ρ.om i j b 1) ((ρ.B i j b).vecAt (half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) (specLoc ρ Y i j b k Q M χ)) h P)

end SpecLoc

end GlobalTheory.SeriesTie

namespace GlobalTheory.SeriesTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Ser2

variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

open Classical in
theorem rdK_specU_grpSum {ρ : Setup X} (hρ : ρ.Good) {Y : NExp D.R D.host D.what₂ D.LL0 N X} {i : X.Tw}
    {j : Fin D.R.m} {b : Bool} (rd : Rd ρ Y i j b) (k : ℕ) (Q : Finset (Pl D.host.E)) (M : ℕ)
    (χ : Multiplicative (DelQM D.host (X.l i) Q M) →* (X.Ok i k)ˣ)
    (x : (↥(half (ρ.ch i) (admissibleConjugatePairPlaces X i Q M)) → ZMod (X.l i ^ M)) → Y.Fm i ((j : ℕ) + 1) b) :
    rdK rd hρ k (Formalism.MainNotions.IntegralHeckeForms.specU Y i ((j : ℕ) + 1) b Q M k χ (grpSum Y (ρ.ch i) Q M x)) =
      ∑ a, ρ.eOk i b k (χ (Multiplicative.ofAdd (spread Y i Q M (ρ.ch i) a)) : X.Ok i k) • rd (x a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [grpSum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Formalism.MainNotions.IntegralHeckeForms.specU, LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.comm_tmul, AlgHom.toLinearMap_apply, AddMonoidAlgebra.lift_single, one_smul,
    MonoidHom.coe_comp, Units.coeHom_apply]
  rw [rdK_tmul]

end Ser2

end GlobalTheory.SeriesTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipIdxNeZero
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.LevelSeries

def flipElt {D : D7} (e : AE D) (m : ℕ) : AE D :=
  e * (m : AE D) + cA D e * incA D ((m : D.host.E)⁻¹) + (1 - e - cA D e)

theorem flipIdx_ne_zero {D : D7} (V W : HSp D) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) {m : ℕ} (hm : m ≠ 0) :
    flipIdx V W T m ≠ 0 := by
  unfold flipIdx
  rw [Finset.prod_ne_zero_iff]
  intro PP _
  refine pow_ne_zero _ ?_
  rw [Ne, Ideal.absNorm_eq_zero_iff, HeightOneSpectrum.maxPowDividing]
  exact pow_ne_zero _ PP.ne_bot

end GlobalTheory.LevelSeries

end
end

