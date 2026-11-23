module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorRealPlaceEqHeisenbergIntegralBase
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyUnitaryTorusOrbitalClassTrivialLocal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianIsometryBaseChange
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormClassesIffConjUnitaryTorusEllipticElements
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusElementCharpolyRegularCentralizer
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0297
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorUpdateFactorFromBaseVector
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensorStep

theorem wAt_wAt_ne {D : D7} {m n : ℕ} {p q : Place D} (h : p ≠ q) (w : Mx D m n) : wAt p (wAt q w) = 0 := by
  have h0 : idem D p * idem D q = 0 := (_root_.GlobalTheory.PlaceTensor.idem_spec D).2.1 p q h
  funext i j
  show idem D p * (idem D q * w i j) = (0 : Mx D m n) i j
  rw [← mul_assoc, h0, zero_mul]
  rfl

theorem wAt_wAt_self {D : D7} {m n : ℕ} (p : Place D) (w : Mx D m n) : wAt p (wAt p w) = wAt p w := by
  have h1 : idem D p * idem D p = idem D p := (_root_.GlobalTheory.PlaceTensor.idem_spec D).1 p
  funext i j
  show idem D p * (idem D p * w i j) = idem D p * w i j
  rw [← mul_assoc, h1]

theorem change_factor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x x' : Place D → WO S T → ℂ) (f : WO S T → ℂ) (q : Place D), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → x q = f₀ → (∀ p, p ≠ q → x' p = x p) → IsLocal ψ θ S T sS sT ΛS ΛT q (x' q) → ∃ f', IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' f' ∧ ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → (∀ w : WO S T, ipO μ 𝓕 (heisO ψ S T (wAt q w) f) g = c * ipO μ 𝓕 (heisO ψ S T (wAt q w) f₀) g') → ipO μ 𝓕 f' g = c * ipO μ 𝓕 (x' q) g' := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x x' f q hf hxq hx' hloc

  have hop : IsLocOp ψ S T μ 𝓕 f₀ q (x' q) := by
    rcases q with v | τ
    · exact _root_.GlobalTheory.PlaceTensorFin.isLocOp_of_isLocal_fin D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ v _ hloc
    · exact _root_.GlobalTheory.RealLocOp.isLocOp_real D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ τ _ hloc
  obtain ⟨L, hL, himg, hx'L⟩ := hop
  have hfpure := hf
  obtain ⟨hres, hfth, hprod⟩ := hf

  obtain ⟨f', hf'th, hf'⟩ := himg f hfth
  have hstd := GlobalTheory.PlaceTensor.base_std hB
  have hlaws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd S T
  have hthw : ∀ u, IsThetaFunO ψ S T (heisO ψ S T u f₀) := fun u => hlaws.1 u f₀ (GlobalTheory.PlaceTensor.base_theta hB)
  refine ⟨f', ⟨⟨?_, ?_⟩, hf'th, ?_⟩, ?_⟩
  · intro p
    by_cases hp : p = q
    · subst hp; exact hloc
    · rw [hx' p hp]; exact hres.1 p
  · refine (hres.2.union (Set.finite_singleton q)).subset ?_
    intro p hp
    by_cases hpq : p = q
    · exact Or.inr hpq
    · left
      have hp' : x' p ≠ f₀ := hp
      rw [hx' p hpq] at hp'
      exact hp'
  · intro w
    have hfin := (hprod w).1
    have hsupp : (Function.mulSupport fun p => ipO μ 𝓕 (x' p) (heisO ψ S T (wAt p w) f₀)).Finite := by
      refine (hfin.union (Set.finite_singleton q)).subset ?_
      intro p hp
      by_cases hpq : p = q
      · exact Or.inr hpq
      · left
        rw [Function.mem_mulSupport] at hp ⊢
        rw [hx' p hpq] at hp
        exact hp
    refine ⟨hsupp, ?_⟩

    have hrest : (∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x' p) (heisO ψ S T (wAt p w) f₀)) =
        ∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀) :=
      finprod_congr fun p => finprod_congr fun hp => by rw [hx' p hp]

    have key : ∀ u, ipO μ 𝓕 (heisO ψ S T (wAt q u) f) (heisO ψ S T w f₀) =
        (∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀)) *
          ipO μ 𝓕 (heisO ψ S T (wAt q u) f₀) (heisO ψ S T (wAt q w) f₀) := by
      intro u
      obtain ⟨-, -, hpu⟩ := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hfpure (wAt q u)
      obtain ⟨hfinu, hequ⟩ := hpu w
      rw [hequ, ← mul_finprod_cond_ne q hfinu]
      dsimp only
      rw [hxq, wAt_wAt_self, mul_comm]
      congr 1
      exact finprod_congr fun p => finprod_congr fun hp => by rw [wAt_wAt_ne hp, WeilVacMove.heisO_zero]
    rw [← mul_finprod_cond_ne q hsupp, hrest, hf' _ (hthw w)]
    simp_rw [key]
    rw [hL, hx'L _ (hthw _), mul_comm]
  · intro g g' c hg hg' hcoef
    rw [hf' g hg, hx'L g' hg']
    simp_rw [hcoef]
    exact hL c _

end GlobalTheory.PlaceTensorStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalUnitaryClassesIffLocalClassFamilies
section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrEll.RatClasses

section General

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r n : ℕ} {P : PPol σ r}
  {J : Matrix (Fin n) (Fin n) E} {k k' : Type} [CommRing k] [Algebra F k] [CommRing k'] [Algebra F k']

theorem mapsCls_unique {ψ : k →ₐ[F] k'} {q : Cls P k} {a b : Cls P k'} (ha : MapsCls P ψ q a)
    (hb : MapsCls P ψ q b) : a = b := by
  obtain ⟨x, x', hx, rfl, ex⟩ := ha
  obtain ⟨y, y', hy, rfl, ey⟩ := hb
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 (hx.trans hy.symm))
  let m := Algebra.TensorProduct.map ψ (AlgHom.id F (Fld P))
  have hm : ∀ z, sigR k' (star' P) (m z) = m (sigR k (star' P) z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [m, sigR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ⟨Units.map m.toMonoidHom c, ?_⟩)
  have hc' : x.1.1 * (c.1 * sigR k (star' P) c.1) = y.1.1 := by
    have : c.1 * sigR k (star' P) c.1 = (x.1⁻¹ * y.1).1 := congrArg Units.val hc
    rw [this, Units.val_mul, Units.mul_inv_cancel_left]
  change _ = x'.1⁻¹ * y'.1
  rw [eq_inv_mul_iff_mul_eq]
  apply Units.ext
  change x'.1.1 * (m c.1 * sigR k' (star' P) (m c.1)) = y'.1.1
  rw [ex, ey, hm, ← hc', map_mul, map_mul]

theorem mapH_diagH (ψ : k →ₐ[F] k') (γ : Formalism.UG.UJ (σ : E →+* E) J) :
    mapH σ J ψ (diagH σ J k γ) = diagH σ J k' γ :=
  Subtype.ext (Units.ext (Matrix.ext fun r s => by
    change Algebra.TensorProduct.map ψ (AlgHom.id F E) ((1 : k) ⊗ₜ[F] (γ.1.1 r s)) = (1 : k') ⊗ₜ[F] (γ.1.1 r s)
    simp))

variable [NumberField F] [NumberField E] (hc : IsCMExt F E σ) (hJ : IsHermND σ J)
include hc hJ

theorem hasCls_unique {γ : HA k σ J} {q q' : Cls P k} (h : HasCls P k J γ q) (h' : HasCls P k J γ q') : q = q' := by
  obtain ⟨x, φ, h, rfl, e⟩ := h
  obtain ⟨x', φ', h', rfl, e'⟩ := h'
  exact (_root_.GlobalTheory.TrEll.cls_conj_torus F E σ hc r n P J hJ k x φ h x' φ' h').2.1 (by rw [e, e'])

theorem hasCls_of_isConj {γ γ' : HA k σ J} {q : Cls P k} (h : HasCls P k J γ q) (e : IsConj γ γ') :
    HasCls P k J γ' q := by
  obtain ⟨x, φ, h, rfl, rfl⟩ := h
  obtain ⟨g, rfl⟩ := isConj_iff.1 e
  exact (_root_.GlobalTheory.TrEll.cls_conj_torus F E σ hc r n P J hJ k x φ h x φ h).2.2.2 g

theorem isConj_of_hasCls {γ γ' : HA k σ J} {q : Cls P k} (h : HasCls P k J γ q) (h' : HasCls P k J γ' q) :
    IsConj γ γ' := by
  obtain ⟨x, φ, h, e, rfl⟩ := h
  obtain ⟨x', φ', h', e', rfl⟩ := h'
  obtain ⟨g, hg⟩ := (_root_.GlobalTheory.TrEll.cls_conj_torus F E σ hc r n P J hJ k x φ h x' φ' h').1 (e.trans e'.symm)
  exact isConj_iff.2 ⟨g, (hg _).symm⟩

theorem exists_mapsCls (ψ : k →ₐ[F] k') {γ : HA k σ J} {q : Cls P k} (h : HasCls P k J γ q) :
    ∃ q', MapsCls P ψ q q' ∧ HasCls P k' J (mapH σ J ψ γ) q' := by
  obtain ⟨x, φ, h, rfl, rfl⟩ := h
  obtain ⟨x', φ', h', e1, e2, -⟩ := _root_.GlobalTheory.TrEll.BaseChg.exists_isom_baseChange F E σ hc r n P J hJ k k' ψ x φ h
  exact ⟨_, ⟨x, x', rfl, rfl, e1⟩, x', φ', h', rfl, e2⟩

theorem exists_mapsCls_rat (k : Type) [CommRing k] [Algebra F k] {γ : GRat σ J} {q : Cls P F}
    (h : HasCls P F J (diagH σ J F γ) q) :
    ∃ q', MapsCls P (k := F) (Algebra.ofId F k) q q' ∧ HasCls P k J (diagH σ J k γ) q' := by
  simpa only [mapH_diagH] using exists_mapsCls hc hJ (Algebra.ofId F k) h

theorem exists_hasCls_rat {P : PPol σ n} (γ : GRat σ J) (h : γ.1.1.charpoly = P.1) :
    ∃ q, HasCls P F J (diagH σ J F γ) q := by
  obtain ⟨P', e, hq⟩ := (_root_.GlobalTheory.TrEll.RatEll.exists_cls_of_irreducible F E σ hc n J hJ).2 γ (h ▸ P.2.2.1)
  obtain rfl : P' = P := Subtype.ext (e.symm.trans h)
  exact hq

theorem charpoly_of_hasCls {γ : GRat σ J} {q : Cls P F} (h : HasCls P F J (diagH σ J F γ) q) :
    γ.1.1.charpoly = P.1 := by
  obtain ⟨x, φ, h, -, e⟩ := h
  have h1 := (_root_.GlobalTheory.TrEll.gam_charpoly_regular_cent F E σ hc r n P J hJ F x φ h).1
  rw [e] at h1
  apply Polynomial.map_injective (inclR (F := F) (E := E) F) (inclR (F := F) (E := E) F).injective
  rw [← h1, ← Matrix.charpoly_map]
  rfl

theorem isConj_of_diagH {γ γ' : GRat σ J} (h : IsConj (diagH σ J F γ) (diagH σ J F γ')) : IsConj γ γ' := by
  have hb := (_root_.GlobalTheory.TrEll.RatEll.exists_cls_of_irreducible F E σ hc n J hJ).1
  obtain ⟨g, e⟩ := isConj_iff.1 h
  obtain ⟨g, rfl⟩ := hb.2 g
  exact isConj_iff.2 ⟨g, hb.1 (by simpa only [map_mul, map_inv] using e)⟩

theorem existsUnique_hasCls_rat {P : PPol σ n} (k : Type) [CommRing k] [Algebra F k] (γ : GRat σ J)
    (h : γ.1.1.charpoly = P.1) : ∃! q, HasCls P k J (diagH σ J k γ) q := by
  obtain ⟨q, hq⟩ := exists_hasCls_rat hc hJ γ h
  obtain ⟨q', -, hq'⟩ := exists_mapsCls_rat hc hJ k hq
  exact ⟨q', hq', fun _ h => hasCls_unique hc hJ h hq'⟩

theorem exists_common {γ γ' : GRat σ J} {q q' : Cls P F} (h : HasCls P F J (diagH σ J F γ) q)
    (h' : HasCls P F J (diagH σ J F γ') q')
    (H : ∀ a, HasCls P k J (diagH σ J k γ) a → HasCls P k J (diagH σ J k γ') a) :
    ∃ a, MapsCls P (k := F) (Algebra.ofId F k) q a ∧ MapsCls P (k := F) (Algebra.ofId F k) q' a := by
  obtain ⟨a, h1, h2⟩ := exists_mapsCls_rat hc hJ k h
  obtain ⟨b, h3, h4⟩ := exists_mapsCls_rat hc hJ k h'
  exact ⟨a, h1, hasCls_unique hc hJ h4 (H a h2) ▸ h3⟩

theorem hasCls_of_mapsCls {γ : GRat σ J} {q : Cls P F} (h : HasCls P F J (diagH σ J F γ) q) {a : Cls P k}
    (H : MapsCls P (k := F) (Algebra.ofId F k) q a) : HasCls P k J (diagH σ J k γ) a := by
  obtain ⟨b, h1, h2⟩ := exists_mapsCls_rat hc hJ k h
  exact mapsCls_unique h1 H ▸ h2

end General

theorem rat_classes_iff_local (E : Type) [Field E] [NumberField E] (F : Subfield E) [NumberField F] (σ : E →ₐ[F] E)
    (hc : IsCMExt F E σ) (hu : Algebra.Unramified (𝓞 F) (𝓞 E)) (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E)
    (hJ : IsHermND σ J) :
    (∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → (∀ v, ∃! q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q) ∧
      (∀ w, ∃! q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q) ∧
      ∀ᶠ v in cofinite, HasCls P _ J (proj σ J v (ratEmb σ J γ)) 1) ∧
    (∀ γ γ' : GRat σ J, γ.1.1.charpoly = P.1 → γ'.1.1.charpoly = P.1 → (IsConj γ γ' ↔
      (∀ v q, HasCls P _ J (proj σ J v (ratEmb σ J γ)) q → HasCls P _ J (proj σ J v (ratEmb σ J γ')) q) ∧
        ∀ w q, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) q → HasCls P _ J (projArch σ J w (ratEmb σ J γ')) q)) ∧
    ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), Cls P (Fv F v)) (qa : ∀ w : InfinitePlace F, Cls P w.Completion),
      (∀ v, qf v ∈ XSet P _ J) → (∀ w, qa w ∈ XSet P _ J) → (∀ᶠ v in cofinite, qf v = 1) →
      ∃ γ : GRat σ J, γ.1.1.charpoly = P.1 ∧ (∀ v, HasCls P _ J (proj σ J v (ratEmb σ J γ)) (qf v)) ∧
        ∀ w, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) (qa w) := by
  have e1 : ∀ v γ, proj σ J v (ratEmb σ J γ) = diagH σ J (Fv F v) γ := proj_ratEmb σ J
  have e2 : ∀ w γ, projArch σ J w (ratEmb σ J γ) = diagH σ J w.Completion γ := projArch_ratEmb σ J
  obtain ⟨H1, H2⟩ := GlobalTheory.T.rationalNormClasses_eq_local_unramifiedCM E F σ hc hu r P J hJ
  refine ⟨fun γ h => ⟨fun v => ?_, fun w => ?_, ?_⟩, fun γ γ' h h' => ⟨fun e => ⟨fun v q hq => ?_, fun w q hq => ?_⟩,
    fun H => ?_⟩, fun qf qa hf ha h1 => ?_⟩
  · rw [e1]; exact existsUnique_hasCls_rat hc hJ _ γ h
  · rw [e2]; exact existsUnique_hasCls_rat hc hJ _ γ h
  · have := isLattice_stdLattice (E := E) (n := r)
    filter_upwards [_root_.GlobalTheory.TrEll.eventually_unitLoc_orbCls F E σ hc r P J hJ (stdLattice E r),
      eventually_proj_mem_stabLoc σ J (stdLattice E r) (ratEmb σ J γ)] with v hv hm
    obtain ⟨q, hq, -⟩ := existsUnique_hasCls_rat hc hJ (Fv F v) γ h
    rw [← e1] at hq
    exact hv.2.1 _ q hq ⟨1, by simpa only [inv_one, one_mul, mul_one] using hm⟩ ▸ hq
  · exact hasCls_of_isConj hc hJ hq ((proj σ J v).map_isConj ((ratEmb σ J).map_isConj e))
  · exact hasCls_of_isConj hc hJ hq ((projArch σ J w).map_isConj ((ratEmb σ J).map_isConj e))
  · simp only [e1, e2] at H
    obtain ⟨q, hq⟩ := exists_hasCls_rat hc hJ γ h
    obtain ⟨q', hq'⟩ := exists_hasCls_rat hc hJ γ' h'
    obtain rfl : q = q' := H1 q q' (hq.mem P) (hq'.mem P) (fun v => exists_common hc hJ hq hq' (H.1 v))
      fun w => exists_common hc hJ hq hq' (H.2 w)
    exact isConj_of_diagH hc hJ (isConj_of_hasCls hc hJ hq hq')
  · obtain ⟨q, hq, h2, h3⟩ := H2 qf qa hf ha h1
    obtain ⟨g, hg⟩ := exists_hasCls P hq
    obtain ⟨γ, rfl⟩ := (_root_.GlobalTheory.TrEll.RatEll.exists_cls_of_irreducible F E σ hc r J hJ).1.2 g
    refine ⟨γ, charpoly_of_hasCls hc hJ hg, fun v => ?_, fun w => ?_⟩
    · rw [e1]; exact hasCls_of_mapsCls hc hJ hg (h2 v)
    · rw [e2]; exact hasCls_of_mapsCls hc hJ hg (h3 w)

end GlobalTheory.TrEll.RatClasses
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationTransportTopGroupEquiv
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
namespace GlobalTheory.TransportIso

theorem irreducible_admissible_integralOp_transport : ∀ (G G' : Type) [Group G] [Group G'] [TopologicalSpace G] [TopologicalSpace G'] [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G'] (Φ : G ≃ₜ* G') (ν : Measure G) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W), (σ.IsIrreducible → Representation.IsIrreducible (σ.comp Φ.symm.toMulEquiv.toMonoidHom)) ∧ (IsAdmissible σ → IsAdmissible (σ.comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ G' W)) ∧ ∀ (f : G → ℂ) (f' : G' → ℂ), (∀ g, f' (Φ g) = f g) → ∀ A, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp (ν.map Φ) (σ.comp Φ.symm.toMulEquiv.toMonoidHom : Representation ℂ G' W) f' A ↔ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ f A := by
  intro G G' _ _ _ _ _ _ _ _ Φ ν W _ _ σ
  have hs : ∀ g' : G', Φ.symm.toMulEquiv g' = Φ.symm g' := fun _ => rfl
  have hs2 : ∀ g' : G', Φ.symm.toMulEquiv.toMonoidHom g' = Φ.symm g' := fun _ => rfl
  have hcomp' : ∀ g' : G', (σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' = σ (Φ.symm g') := fun _ => rfl
  have hcomp : ∀ g : G, (σ.comp Φ.symm.toMulEquiv.toMonoidHom) (Φ g) = σ g := by
    intro g; rw [hcomp', Φ.symm_apply_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro hσ
    let e : Subrepresentation (σ.comp Φ.symm.toMulEquiv.toMonoidHom) ≃o Subrepresentation σ :=
      { toFun := fun U => ⟨U.toSubmodule, fun g v hv => by
          have := U.apply_mem_toSubmodule (Φ g) hv
          rwa [hcomp] at this⟩
        invFun := fun U => ⟨U.toSubmodule, fun g' v hv => by
          rw [hcomp']
          exact U.apply_mem_toSubmodule _ hv⟩
        left_inv := fun U => rfl
        right_inv := fun U => rfl
        map_rel_iff' := Iff.rfl }
    exact e.isSimpleOrder
  · rintro ⟨hsm, hfd⟩
    refine ⟨?_, ?_⟩
    · intro v
      have : {g' : G' | (σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' v = v} = Φ.symm ⁻¹' {g | σ g v = v} := by
        ext g'; exact Iff.rfl
      rw [this]
      exact (hsm v).preimage Φ.symm.continuous
    · intro K' hK'o hK'c
      let K : Subgroup G := K'.comap Φ.toMulEquiv.toMonoidHom
      have hKo : IsOpen (K : Set G) := hK'o.preimage Φ.continuous
      have hKc : IsCompact (K : Set G) := by
        have : (K : Set G) = Φ.symm '' (K' : Set G') := by
          ext g; constructor
          · intro hg; exact ⟨Φ g, hg, by simp⟩
          · rintro ⟨g', hg', rfl⟩
            show Φ (Φ.symm g') ∈ K'
            simpa using hg'
        rw [this]; exact hK'c.image Φ.symm.continuous
      have heq : GlobalTheory.PRep.fixed (σ.comp Φ.symm.toMulEquiv.toMonoidHom) K' = GlobalTheory.PRep.fixed σ K := by
        ext v
        simp only [GlobalTheory.PRep.fixed, GlobalTheory.PRep.eig]
        constructor
        · intro hv h
          have := hv ⟨Φ h, h.2⟩
          simp at this ⊢
          convert this using 3
          exact (Φ.symm_apply_apply _).symm
        · intro hv h
          have := hv ⟨Φ.symm h, show Φ (Φ.symm h) ∈ K' by simpa using h.2⟩
          simp at this ⊢
          convert this using 3
          rfl
      rw [heq]
      exact hfd K hKo hKc
  · intro f f' hf A
    let e : G ≃ᵐ G' := Φ.toHomeomorph.toMeasurableEquiv
    have hmap : ν.map Φ = ν.map e := rfl
    have he : ∀ g, e g = Φ g := fun g => rfl
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp, hmap]
    refine forall_congr' fun v => forall_congr' fun l => ?_
    rw [integrable_map_equiv, integral_map_equiv]
    have hfun : ((fun g' => f' g' * l ((σ.comp Φ.symm.toMulEquiv.toMonoidHom) g' v)) ∘ e) = fun g => f g * l (σ g v) := by
      funext g; simp only [Function.comp_apply, he, hf, hcomp]
    have hfun' : (fun g => f' (e g) * l ((σ.comp Φ.symm.toMulEquiv.toMonoidHom) (e g) v)) = fun g => f g * l (σ g v) := by
      funext g; simp only [Function.comp_apply, he, hf, hcomp]
    rw [hfun, hfun']

end GlobalTheory.TransportIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightRegularOperatorRepresentedContinuous
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Cusp GlobalTheory.IndefiniteRowSideFullHecke.CuspidalNoRadicalFixed
open scoped Pointwise

namespace GlobalTheory.RopRep

theorem rop_rep : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ f ∈ CcGA V, ∀ F : DividedPowerChartLift V μ, (∀ x, Integrable (fun y => f (x⁻¹ * y) * lift (GQ V) F y) μ) ∧ Continuous (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) ∧ LeftInv (GQ V) (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) ∧ lift (GQ V) (RopG V μ f F) =ᵐ[μ] fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ := by
  intro D V μ _ _ f hf F
  obtain ⟨hfc, hfs⟩ := GlobalTheory.Orb.continuous_of_mem_ccAd hf
  have hloc : LocallyIntegrable (lift (GQ V) F) μ :=
    (locallyIntegrable_iff).2 fun C hC => (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F C hC).2
  have hint : ∀ x, Integrable (fun y => f (x⁻¹ * y) * lift (GQ V) F y) μ := fun x =>
    hloc.integrable_smul_left_of_hasCompactSupport (hfc.comp (continuous_const_mul _))
      (hfs.comp_homeomorph (Homeomorph.mulLeft x⁻¹))
  have hconv : (fun x => ∫ y, f (x⁻¹ * y) * lift (GQ V) F y ∂μ) = convR μ f (lift (GQ V) F) :=
    funext fun x => (convR_eq f _ x).symm
  refine ⟨hint, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun x₀ => ?_
    obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x₀
    obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hfs
    have hC : IsCompact (K * tsupport f) := hK.mul hfs
    have hCi : IntegrableOn (lift (GQ V) F) (K * tsupport f) μ :=
      (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact _ (GQ V) μ F _ hC).2
    refine continuousAt_of_dominated
      (bound := (K * tsupport f).indicator fun y => M * ‖lift (GQ V) F y‖)
      (.of_forall fun x => (hint x).1) ?_ ?_ (.of_forall fun y => ?_)
    · filter_upwards [hKx] with x hx
      refine .of_forall fun y => ?_
      by_cases hy : f (x⁻¹ * y) = 0
      · rw [hy, zero_mul, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => mul_nonneg ((norm_nonneg _).trans (hM 1)) (norm_nonneg _)) _
      · have hmem : y ∈ K * tsupport f :=
          ⟨x, hx, x⁻¹ * y, subset_tsupport f hy, by simp⟩
        rw [Set.indicator_of_mem hmem, norm_mul]
        exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
    · exact (integrable_indicator_iff hC.isClosed.measurableSet).2 (hCi.norm.const_mul M)
    · exact ((hfc.comp (continuous_inv.mul continuous_const)).mul continuous_const).continuousAt
  · rw [hconv]
    exact (leftInv_lift _).convR f
  · rw [hconv]
    exact (GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR _ (GQ V) μ f
      (hfc.integrable_of_hasCompactSupport hfs) F).2

end GlobalTheory.RopRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissible
section
namespace GlobalTheory.SchurAdmissibility

theorem schur_admissible (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ G N)
    (hirr : Representation.IsIrreducible π) (hadm : GlobalTheory.PRep.IsAdmissible π)
    (φ : N →ₗ[ℂ] N) (hφ : ∀ (g : G) (x : N), φ (π g x) = π g (φ x)) :
    ∃ c : ℂ, φ = c • LinearMap.id := by
  by_cases hN : ∀ v : N, v = 0
  · exact ⟨0, LinearMap.ext fun v => by rw [hN (φ v)]; simp⟩
  push Not at hN
  obtain ⟨v, hv⟩ := hN
  let S : Subgroup G :=
    { carrier := {g : G | π g v = v}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hSo : IsOpen (S : Set G) := hadm.1 v
  have hSc : IsClosed (S : Set G) := S.isClosed_of_isOpen hSo
  have hLo : IsOpen ((K ⊓ S : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKo.inter hSo
  have hLc : IsCompact ((K ⊓ S : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKc.inter_right hSc
  haveI hfd := hadm.2 (K ⊓ S) hLo hLc
  have hmem : ∀ w : N, w ∈ GlobalTheory.PRep.fixed π (K ⊓ S) ↔
      ∀ h : (K ⊓ S : Subgroup G), π (h : G) w = w := by
    intro w
    change (∀ h : (K ⊓ S : Subgroup G), π (h : G) w = _) ↔ _
    simp
  have hvm : v ∈ GlobalTheory.PRep.fixed π (K ⊓ S) := (hmem v).2 fun h => h.2.2
  haveI : Nontrivial (GlobalTheory.PRep.fixed π (K ⊓ S)) :=
    ⟨⟨⟨v, hvm⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have hres : ∀ w ∈ GlobalTheory.PRep.fixed π (K ⊓ S), φ w ∈ GlobalTheory.PRep.fixed π (K ⊓ S) := by
    intro w hw
    rw [hmem] at hw ⊢
    intro h
    rw [← hφ, hw h]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (φ.restrict hres)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw0 : (w : N) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have hw1 : φ w = c • (w : N) := congrArg Subtype.val hw.apply_eq_smul
  let U : Subrepresentation π :=
    { toSubmodule := Module.End.eigenspace φ c
      apply_mem_toSubmodule := by
        intro g x hx
        rw [Module.End.mem_eigenspace_iff] at hx ⊢
        rw [hφ, hx, map_smul] }
  refine ⟨c, ?_⟩
  rcases hirr.eq_bot_or_eq_top U with h | h
  · exfalso
    have h1 : (w : N) ∈ U.toSubmodule := Module.End.mem_eigenspace_iff.2 hw1
    rw [h] at h1
    exact hw0 h1
  · ext x
    have h1 : x ∈ U.toSubmodule := by
      rw [h]; trivial
    exact Module.End.mem_eigenspace_iff.1 h1

end GlobalTheory.SchurAdmissibility
end

