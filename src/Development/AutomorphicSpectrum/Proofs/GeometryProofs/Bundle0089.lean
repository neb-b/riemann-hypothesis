module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0002
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.RootOfRealisationTelescoping
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleOfDensePart
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslDiffEq
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorGeneric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0086
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0082
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0087
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0065
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.WeilBound.CoreStatements.AmpleLineBundles.ExistsPointsOverNumberFields
public import Development.WeilBound.CoreStatements.AmpleLineBundles.LineHtInvariantBaseChangeScaling

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermRootLineDegree
section
open MvPolynomial NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_rootFlat_of_realis : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (S : GlobalTheory.CompanionTheory.Ar.PB.AnSys (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N) (Option (Ψ × Fin N))) (Re : GlobalTheory.CompanionTheory.Ar.PB.Realis S M.P) (τ : Ψ) (i₀ : Fin N) (F : Type) [Field F] [NumberField F] (φ : F →+* M.Ω) (A : HermLine M.ι) (Sf : FlatHerm M.y φ A), OverInt M.y φ → IsSmoothHerm A → (i₀ : ℕ) + 1 = N → 0 < S.t₀ → A.a = ∑ i, M.xdeg (τ, i) → (∀ (σ : Ψ) (i : Fin N), M.xdeg (σ, i) + (Re.ref (some (σ, i))).a = if h : 0 < (i : ℕ) then (Re.ref (some (σ, ⟨i - 1, by omega⟩))).a else 0) → (∀ t, 0 < t → t ≤ S.t₀ → ∀ (σ : Ψ) (i : Fin N), ∀ z ∈ mcPts M.P, (M.x t (σ, i)).h z * (Re.line (some (σ, i)) t).h z = if h : 0 < (i : ℕ) then (Re.line (some (σ, ⟨i - 1, by omega⟩)) t).h z else 1) → (∀ x, Re.π x ∈ S.open' → -Real.log (A.h (Re.R.lift x x)) = Real.log ((Re.ref (some (τ, i₀))).h (Re.R.lift x x)) + S.ph (some (τ, i₀)) (Re.π x)) → ∃ R : RootFlat M τ, R.ht = Sf.ht :=
  PositivityTheory.Xgn.root_of_realisation_telescoping

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericOfSmoothSurjective
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

namespace GlobalTheory.CompanionTheory.Ar.CptLift

theorem isCptGen_of_smooth_of_surjective : ∀ (K : Type) [Field K] (X₀ X' : Scheme.{0}) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (π : X' ⟶ X₀)
    (s' : X' ⟶ Spec (CommRingCat.of K)), Smooth s' → ξ' ≫ π = ξ → IsCptGen ξ →
    Function.Surjective (π.stalkMap (genPt ξ')).hom → IsCptGen ξ' := by
  intro K _ X₀ X' Ω _ ξ ξ' π s' hs hc hξ hsurj
  subst hc
  have hd : ∀ x : X', IsDomain (X'.presheaf.stalk x) := fun x =>
    GroundTheory.Arith.SchemeCoh.isDomain_stalk_of_smooth_field s' x
  have hcomp : (Scheme.stalkClosedPointTo (ξ' ≫ π)).hom =
      (Scheme.stalkClosedPointTo ξ').hom.comp (π.stalkMap (genPt ξ')).hom :=
    congrArg (fun t => t.hom) (Scheme.stalkClosedPointTo_comp ξ' π)
  have hbij : Function.Bijective (Scheme.stalkClosedPointTo ξ').hom := by
    have hb := hξ.bij
    rw [hcomp] at hb
    refine ⟨fun a b hab => ?_, fun c => ?_⟩
    · obtain ⟨a', rfl⟩ := hsurj a
      obtain ⟨b', rfl⟩ := hsurj b
      exact congrArg _ (hb.1 hab)
    · obtain ⟨a, ha⟩ := hb.2 c
      exact ⟨_, ha⟩
  refine ⟨hbij, fun p => ?_⟩
  have hinj : Function.Injective (X'.presheaf.stalkSpecializes p.2).hom := by
    haveI := hd (genPt ξ')
    exact GlobalTheory.PushInv.stalkSpecializes_injective p.2
  intro a b hab
  exact hinj (hbij.1 hab)

end GlobalTheory.CompanionTheory.Ar.CptLift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermJetPointComposition
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.JetPts

section
variable {X0 : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ X0)

theorem homAt_comp_homAt {A B C : Type} [CommRing A] [Algebra k A] [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
    (g : A →ₐ[k] B) (f : B →ₐ[k] C) : homAt x f ≫ homAt x g = homAt x (f.comp g) := by
  apply Over.OverMorphism.ext
  simp only [homAt, Over.comp_left, Over.homMk_left, spMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem homAt_id_eq {A : Type} [CommRing A] [Algebra k A] : homAt x (AlgHom.id k A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  simp only [homAt, Over.homMk_left, spMap]
  exact Spec.map_id _

def trJ (κ : Type) {n M : ℕ} (h : n ≤ M) : Jet k κ M →ₐ[k] Jet k κ n :=
  Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right (by omega))

theorem trJ_mk (κ : Type) {n M : ℕ} (h : n ≤ M) (P : MvPolynomial κ k) :
    trJ (k := k) κ h (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ P := rfl

theorem x_eq_of_trunc {Y : Over X0} {κ : Type} (z : ∀ m, overAt x (Jet k κ m) ⟶ Y)
    (hz : ∀ m, homAt x (jetTrunc : Jet k κ (m + 1) →ₐ[k] Jet k κ m) ≫ z (m + 1) = z m) {n M : ℕ} (h : n ≤ M) :
    homAt x (trJ κ h) ≫ z M = z n := by
  induction M, h using Nat.le_induction with
  | base =>
    have e : trJ (k := k) κ (le_refl n) = AlgHom.id k _ := by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      rfl
    rw [e, homAt_id_eq, Category.id_comp]
  | succ M h ih =>
    have e : (trJ (k := k) κ (Nat.le_succ_of_le h)) = (trJ κ h).comp jetTrunc := by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      rfl
    rw [← ih, ← hz M, e, ← homAt_comp_homAt, Category.assoc]

end

section
variable {k : Type} [Field k] {d : ℕ}

theorem liftJet_mk_eq {κ B : Type} [CommRing B] [Algebra k B] {n : ℕ} (f : MvPolynomial κ k →ₐ[k] B)
    (h : Ideal.span (Set.range fun i => f (MvPolynomial.X i)) ^ (n + 1) = ⊥) (P : MvPolynomial κ k) :
    liftJet f h (Ideal.Quotient.mk _ P) = f P := rfl

theorem jetMap_mk_eq {κ κ' : Type} {n : ℕ} (φ : κ → MvPolynomial κ' k) (hφ : ∀ i, φ i ∈ orig k κ') (P : MvPolynomial κ k) :
    (jetMap φ hφ : Jet k κ n →ₐ[k] Jet k κ' n) (Ideal.Quotient.mk _ P) = Ideal.Quotient.mk _ (MvPolynomial.aeval φ P) := rfl

theorem jq_mk_zero (w : Fin d → k) (p m : ℕ) (j : Fin d) :
    jq w p m (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 2), j))) =
      algebraMap k _ (w j) * dQ (Jet k (Fin 1 × Fin d) m) p := by
  rw [jq, liftJet_mk_eq]
  simp

theorem jq_mk_one (w : Fin d → k) (p m : ℕ) (j : Fin d) :
    jq w p m (Ideal.Quotient.mk _ (MvPolynomial.X ((1 : Fin 2), j))) =
      inR (k := k) (Jet k (Fin 1 × Fin d) m) p (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) := by
  rw [jq, liftJet_mk_eq]
  simp

theorem inL_mk (B : Type) [CommRing B] [Algebra k B] (p : ℕ) :
    inL (k := k) B p (Ideal.Quotient.mk _ (MvPolynomial.X ())) = dQ B p := by
  rw [inL, liftJet_mk_eq]
  simp

theorem ring_zero (w : Fin d → k) (p m : ℕ) :
    (jq w p m).comp (jetCopy d (p + m + 1) (0 : Fin 2)) =
      (inL (k := k) (Jet k (Fin 1 × Fin d) m) p).comp
        ((jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()).comp
          (trJ (Fin 1 × Fin d) (show p ≤ p + m + 1 by omega))) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨a, j⟩
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  have h1 : jetCopy (S := k) d (p + m + 1) (0 : Fin 2) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 2), j)) := by
    rw [jetCopy, jetMap_mk_eq]
    simp
  have h2 : jetSubstP (S := k) p (fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ())
      (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      algebraMap k _ (w j) * Ideal.Quotient.mk _ (MvPolynomial.X ()) := by
    rw [jetSubstP, jetMap_mk_eq]
    simp only [MvPolynomial.aeval_X, map_mul, MvPolynomial.constantCoeff_C, MvPolynomial.constantCoeff_X, mul_zero,
      map_zero, sub_zero]
    rfl
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, trJ_mk, h1, h2, jq_mk_zero, map_mul, AlgHom.commutes, inL_mk]

theorem ring_one (w : Fin d → k) (p m : ℕ) :
    (jq w p m).comp (jetCopy d (p + m + 1) (1 : Fin 2)) =
      (inR (k := k) (Jet k (Fin 1 × Fin d) m) p).comp
        (trJ (Fin 1 × Fin d) (show m ≤ p + m + 1 by omega)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨a, j⟩
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  have h1 : jetCopy (S := k) d (p + m + 1) (1 : Fin 2) (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), j))) =
      Ideal.Quotient.mk _ (MvPolynomial.X ((1 : Fin 2), j)) := by
    rw [jetCopy, jetMap_mk_eq]
    simp
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, trJ_mk, h1, jq_mk_one]

end

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ), homAt x (jq w p m) ≫ jptG t x d g.x (p + m + 1) (0 : Fin 2) = homAt x (inL (k := k) (Jet k (Fin 1 × Fin d) m) p) ≫ homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p ∧ homAt x (jq w p m) ≫ jptG t x d g.x (p + m + 1) (1 : Fin 2) = homAt x (inR (k := k) (Jet k (Fin 1 × Fin d) m) p) ≫ g.x m := by
  intro E _ _ _ H _ X0 t k _ p x d g w m
  constructor
  · have hx := x_eq_of_trunc x g.x g.chart.trunc (show p ≤ p + m + 1 by omega)
    show homAt x (jq w p m) ≫ homAt x (jetCopy d (p + m + 1) (0 : Fin 2)) ≫ g.x (p + m + 1) = _
    rw [← hx, ← Category.assoc, homAt_comp_homAt, ring_zero, ← homAt_comp_homAt, ← homAt_comp_homAt]
    simp only [Category.assoc]
  · have hx := x_eq_of_trunc x g.x g.chart.trunc (show m ≤ p + m + 1 by omega)
    show homAt x (jq w p m) ≫ homAt x (jetCopy d (p + m + 1) (1 : Fin 2)) ≫ g.x (p + m + 1) = _
    rw [← hx, ← Category.assoc, homAt_comp_homAt, ring_one, ← homAt_comp_homAt]
    simp only [Category.assoc]

end GlobalTheory.CompanionTheory.Ar.Coc.JetPts
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptBirationalArithVar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem flagged_model_dim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) [Nonempty K], Function.Injective β → Birational y ∧ IsArithVar (mCoordIdeal y) (Fintype.card (CMType H) * ((D.p + D.q) * (D.p + D.q - 1) / 2) + 1) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J _ y 𝔐 Fl _ hβ
  obtain ⟨-, ⟨x, hx⟩, hchar, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.HodgeCpt.basic E H D l Xo c O β Y S Ω K J y 𝔐 hβ
  have hA := _root_.GlobalTheory.CompanionTheory.Ar.CptTrdeg.trdeg_eq_dim E H D l Xo c O β Y 𝔐.Ω₀ 𝔐.ξ₀ Ω x 𝔐.fn hβ 𝔐.gen₀ (hx ▸ 𝔐.fn_over)
  letI : Algebra 𝔐.Ω₀ Ω := 𝔐.fn.toAlgebra
  have hB := GlobalTheory.T.generic_flag_trdeg_formula 𝔐.Ω₀ Ω Fl.Li₀ 𝔐.Li Fl.j (CMType H ⊕ CMType H) (labelRk D) Fl.V₀ Fl.b Fl.deg Fl.generic
  haveI : CharZero 𝔐.Ω₀ := (RingHom.charZero_iff 𝔐.fn.injective).mpr hchar
  haveI : FaithfulSMul ℤ 𝔐.Ω₀ := (faithfulSMul_iff_algebraMap_injective ℤ 𝔐.Ω₀).mpr Int.cast_injective
  haveI : FaithfulSMul 𝔐.Ω₀ Ω := (faithfulSMul_iff_algebraMap_injective 𝔐.Ω₀ Ω).mpr 𝔐.fn.injective
  have htow := trdeg_add_eq ℤ 𝔐.Ω₀ (A := Ω)
  rw [hA, hB] at htow
  have hcard : Fintype.card (CMType H) = Module.finrank ℚ E / 2 := by
    rw [Fintype.card_eq_nat_card]; exact GlobalTheory.PeriodCoord.card_cmType H
  have harith : D.dim + ∑ σ : CMType H ⊕ CMType H, labelRk D σ * (labelRk D σ - 1) / 2 =
      Fintype.card (CMType H) * ((D.p + D.q) * (D.p + D.q - 1) / 2) := by
    have h1 : (D.p + D.q) * (D.p + D.q - 1) / 2 = D.p * (D.p - 1) / 2 + D.q * (D.q - 1) / 2 + D.p * D.q := by
      rw [← Nat.choose_two_right, ← Nat.choose_two_right, ← Nat.choose_two_right, Nat.add_choose_eq]
      simp [Finset.Nat.antidiagonal_succ, Finset.sum_range_succ]
      ring
    rw [Fintype.sum_sum_type, h1, Datum.dim, ← hcard]
    simp [Finset.sum_const, Finset.card_univ, labelRk]
    ring
  have htr : Algebra.trdeg ℤ Ω = ((Fintype.card (CMType H) * ((D.p + D.q) * (D.p + D.q - 1) / 2) : ℕ) : Cardinal) := by
    rw [← htow, ← harith]; push_cast; rfl
  exact GlobalTheory.T.birational_of_transcendence_degree 𝔐.X Ω 𝔐.ξ K J y _ 𝔐.tie htr

end GlobalTheory.CompanionTheory.Ar
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyPlaceWeight
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem constLine_zero_tensor {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    (constLine (ι := ι) 0).tensor (constLine 0) = constLine 0 := by
  simp [HermLine.tensor, constLine, HermLine.ofWeight]

theorem ptsIntegral_eq_mean : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (d : ℕ) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ), IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) → (∀ σ z, PtOver y φ σ z → u z = t σ) → ptsIntegral W (pot L) u = meanEmb t * ptsIntegral W (pot L) (fun _ => 1) := by
  intro hPI K _ ι _ Ω _ F _ _ y φ I W n L d t u hI hd hO hle hW hL ht hu
  have hex := fun σ : F →+* ℂ => GlobalTheory.T.exists_place_weight_conj_invariant K ι Ω F y φ (Set.indicator {σ} 1) hO
  choose χ hχ _ using hex
  have hsplit : ∀ (t' : (F →+* ℂ) → ℝ) (u' : ((Σ k, ι k) → ℂ) → ℝ),
      (∀ σ z, PtOver y φ σ z → u' z = t' σ) →
      ptsIntegral W (pot L) u' = ∑ σ : F →+* ℂ, t' σ * ptsIntegral W (pot L) (χ σ) :=
    fun t' u' h => _root_.GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_place hPI K ι Ω F y φ W n L t' u' χ hO hle hW hL h hχ
  have hc : IsSmoothHerm (constLine (ι := ι) 0) := contDiffOn_const
  have hzero : I W (n + 1) (Fin.snoc L (constLine 0)) = 0 := by
    have h := hI.2.1 W n L (constLine 0) (constLine 0) hW hL hc hc
    rw [constLine_zero_tensor] at h
    linarith
  have hunit : ∀ α : (𝓞 F)ˣ,
      ∑ σ : F →+* ℂ, Real.log ‖σ ((α : 𝓞 F) : F)‖ * ptsIntegral W (pot L) (χ σ) = 0 := by
    intro α
    obtain ⟨S, -, hκ⟩ := GlobalTheory.T.flat_herm_unit_constant K ι Ω F y φ α hO
    obtain ⟨v, hv, -⟩ := GlobalTheory.T.exists_place_weight_conj_invariant K ι Ω F y φ (fun σ => Real.log (S.κ σ)) hO
    have h1 := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.inter_eq_neg_integral K ι Ω F y φ I W n L (constLine 0) S d v hI hd hO hle hW hL hc hv
    have h2 := hsplit (fun σ => Real.log (S.κ σ)) v fun σ z hz => (hv.near σ z hz).self_of_nhds
    simp only [hκ] at h2
    linarith
  have hmain := sum_eq_mean_of_units F (fun σ => ptsIntegral W (pot L) (χ σ)) t hunit ht
  have hone := hsplit (fun _ => 1) (fun _ => 1) fun _ _ _ => rfl
  simp only [one_mul] at hone
  rw [hsplit t u hu, hone, hmain]
  rfl

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetAugmentationOnePthPower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Coc.QAlg

theorem exists_const_add_dQ_mul (B : Type) [CommRing B] (m : ℕ) (x : Jet B Unit m) :
    ∃ (b : B) (y : Jet B Unit m), x = algebraMap B _ b + dQ B m * y := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := orig B Unit ^ (m + 1)) x
  have hmem := sub_const_mem_orig P
  have hr : Set.range (MvPolynomial.X : Unit → MvPolynomial Unit B) = {MvPolynomial.X ()} :=
    Set.range_unique
  rw [orig, hr, Ideal.mem_span_singleton'] at hmem
  obtain ⟨Q, hQ⟩ := hmem
  refine ⟨MvPolynomial.constantCoeff P, Ideal.Quotient.mk _ Q, ?_⟩
  have hP : P = MvPolynomial.C (MvPolynomial.constantCoeff P) + Q * MvPolynomial.X () := by
    rw [hQ]; ring
  conv_lhs => rw [hP]
  rw [map_add (f := _), map_mul, mul_comm]
  rfl

theorem jetAug_dQ (B : Type) [CommRing B] (m : ℕ) :
    (jetAug : Jet B Unit m →ₐ[B] B) (dQ B m) = 0 := by
  show (jetAug : Jet B Unit m →ₐ[B] B)
    (Ideal.Quotient.mk (orig B Unit ^ (m + 1)) (MvPolynomial.X ())) = 0
  simp [jetAug, liftJet, Ideal.Quotient.liftₐ_apply]

theorem add_pow_of_natCast_eq_zero {A : Type} [CommRing A] (p : ℕ) (hp : p.Prime)
    (h : (p : A) = 0) (x y : A) : (x + y) ^ p = x ^ p + y ^ p := by
  rw [add_pow_prime_eq hp, h]
  simp

theorem pow_eq_one_add (B : Type) [CommRing B] (p : ℕ) [hp : Fact p.Prime] (h0 : (p : B) = 0)
    (e : Jet B Unit p) (he : (jetAug : Jet B Unit p →ₐ[B] B) e = 1) :
    ∃ v : B, e ^ p = 1 + dQ B p ^ p * algebraMap B _ (v ^ p) := by
  have hpJ : ((p : ℕ) : Jet B Unit p) = 0 := by
    rw [← map_natCast (algebraMap B (Jet B Unit p)) p, h0, map_zero]
  obtain ⟨b, y, rfl⟩ := exists_const_add_dQ_mul B p e
  have hb : b = 1 := by
    simpa only [map_add (f := _), map_mul, jetAug_dQ, zero_mul, add_zero, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply] using he
  subst hb
  obtain ⟨c, z, rfl⟩ := exists_const_add_dQ_mul B p y
  refine ⟨c, ?_⟩
  have h2 : dQ B p ^ p * dQ B p ^ p = 0 := by
    rw [← pow_add]
    exact pow_eq_zero_of_le (by have := hp.out.one_lt; omega) (dQ_pow B p)
  rw [map_one, add_pow_of_natCast_eq_zero p hp.out hpJ, one_pow, mul_pow,
    add_pow_of_natCast_eq_zero p hp.out hpJ, mul_pow, map_pow]
  linear_combination (z ^ p) * h2

end GlobalTheory.CompanionTheory.Ar.Coc.QAlg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JetLeftMem
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Coc.Pf

theorem gs_appLE {X Y : Scheme.{0}} (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) (y : Y) (hy : y ∈ V)
    (a : Γ(X, U)) : gs (𝟙 Y) y V ((f.appLE U V e).hom a) = gs f y U a := by
  have hf : f y ∈ U := e hy
  have key := Y.presheaf.germ_res_apply (homOfLE e) y hy ((f.app U).hom a)
  unfold gs
  rw [dite_eq_left hf]
  split_ifs with h1
  · exact key
  · exact absurd hy h1

theorem gm_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) (z : Sp B) :
    gm (spMap f) z ⊤ (unitΓ u) = gm (𝟙 _) z ⊤ (unitΓ (Units.map (f : A →* B) u)) := by
  have key := congrArg (fun g => (CommRingCat.Hom.hom g) (u : A)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key
  unfold gm
  rw [dite_eq_left (show (spMap f) z ∈ (⊤ : (Sp A).Opens) from trivial)]
  rw [dite_eq_left (show (𝟙 (Sp B)) z ∈ (⊤ : (Sp B).Opens) from trivial)]
  apply Units.ext
  simp only [MonoidHom.comp_apply, Units.coe_map, pullU, unitΓ, toΓ, MonoidHom.coe_coe, Scheme.Hom.id_app, CommRingCat.hom_id, RingHom.id_apply]
  erw [key]
  rfl

theorem val_scale {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (c : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) :
    val (scaleGenG t φ ε u c) r z J = gm r z ⊤ u * val c r z J := by
  have hz : r z ∈ t.PP.L.wchart φ (fun k => J (r ≫ φ k)) := by
    show r z ∈ ⋂ k, ⇑(φ k) ⁻¹' ↑(t.PP.L.U (J (r ≫ φ k)))
    refine Set.mem_iInter.2 fun k => ?_
    have := hJ (r ≫ φ k)
    simpa [Scheme.Hom.comp_apply] using this
  unfold val scaleGenG
  erw [map_mul, gm_res r z _ hz]

theorem val_genPow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (c : LB.Gen (LB.LinComb t.PP.L φ ε)) (n : ℕ) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι) :
    val (genPowG t φ ε c n) r z J = val c r z J ^ n :=
  map_pow _ _ _

theorem jet_left_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {k : Type} [Field k] (x : Sp k ⟶ X0) {κ : Type} {n : ℕ} (j₀ : t.PP.L.ι)
    (hj₀ : ⊤ ≤ (1 : overAt x k ⟶ t.G).left ⁻¹ᵁ t.PP.L.U j₀) (ψ : overAt x (Jet k κ n) ⟶ t.G)
    (h : homAt x (jetAug : Jet k κ n →ₐ[k] k) ≫ ψ = 1) (q : Sp (Jet k κ n)) : ψ.left q ∈ t.PP.L.U j₀ := by
  have hsurj : Function.Surjective (jetAug : Jet k κ n →ₐ[k] k).toRingHom :=
    fun c => ⟨algebraMap k _ c, (jetAug : Jet k κ n →ₐ[k] k).commutes c⟩
  have hnil : ∀ a : Jet k κ n, jetAug a = 0 → IsNilpotent a := by
    intro a ha
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
    have h0 : MvPolynomial.constantCoeff P = 0 := by
      have : jetAug (Ideal.Quotient.mk _ P : Jet k κ n) = MvPolynomial.aeval (fun _ : κ => (0 : k)) P := rfl
      rw [this] at ha
      simpa [MvPolynomial.aeval_zero'] using ha
    have hP : P ∈ orig k κ := by
      have : P ∈ Ideal.span (MvPolynomial.X '' (Set.univ : Set κ)) := by
        rw [MvPolynomial.mem_ideal_span_X_image]
        intro m hm
        by_contra hc
        push_neg at hc
        have hm0 : m = 0 := by ext i; exact hc i (Set.mem_univ i)
        subst hm0
        rw [MvPolynomial.mem_support_iff, ← MvPolynomial.constantCoeff_eq] at hm
        exact hm h0
      simpa [orig, Set.image_univ] using this
    refine ⟨n + 1, ?_⟩
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.pow_mem_pow hP _
  have hrange := range_comap_of_surjective _ _ hsurj
  have huniv : PrimeSpectrum.zeroLocus (RingHom.ker (jetAug : Jet k κ n →ₐ[k] k).toRingHom : Set (Jet k κ n)) = Set.univ := by
    rw [PrimeSpectrum.zeroLocus_eq_univ_iff]
    intro a ha
    exact mem_nilradical.2 (hnil a (RingHom.mem_ker.1 ha))
  obtain ⟨p, hp⟩ : q ∈ Set.range (PrimeSpectrum.comap (jetAug : Jet k κ n →ₐ[k] k).toRingHom) := by
    rw [hrange, huniv]; trivial
  have hl := congrArg (fun g => Over.Hom.left g) h
  simp only [Over.comp_left] at hl
  have hq : ψ.left q = (1 : overAt x k ⟶ t.G).left p := by
    rw [← hl, ← hp]
    rfl
  rw [hq]
  exact hj₀ (show p ∈ (⊤ : (Sp k).Opens) from trivial)

end GlobalTheory.CompanionTheory.Ar.Coc.Pf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsLift
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.CoverDense

theorem preimage_dense : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω) (Q : (L : Type) → [Field L] → ((Σ k, R.ι k) → L) → Prop), (∀ f : MRing R.ι, (∃ a, IsMultiHomog f a) → f ∉ R.P → ∃ (L : Type) (_ : Field L) (_ : NumberField L), ∃ w ∈ ptsOver L R.P, aeval w f ≠ 0 ∧ Q L w) → ∀ f : MRing M.ι, (∃ a, IsMultiHomog f a) → f ∉ M.P → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L') (w : (Σ k, R.ι k) → L), ∃ z ∈ ptsOver L' (mCoordIdeal (joinOf M R i)), w ∈ ptsOver L R.P ∧ Q L w ∧ (fun p => z (joinInr M.ι R.ι p)) = (fun p => e (w p)) ∧ aeval (fun p => z (joinInl M.ι R.ι p)) f ≠ 0 :=
  CoverDenseAlt.exists_points_over_number_fields

end GlobalTheory.CompanionTheory.Ar.CoverDense
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineHeightInvariantScaling
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht

theorem lineHt_map_scale : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : HermLine ι) (L : Type) [Field L] [NumberField L] (L' : Type) [Field L'] [NumberField L'] (e : L →+* L') (w : (Σ k, ι k) → L) (c : K → L'), (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → (∀ k, c k ≠ 0) → lineHt A L' (fun p => c p.1 * e (w p)) = lineHt A L w :=
  @CoverDenseAlt.lineHt_invariant_base_change_scaling

end GlobalTheory.CompanionTheory.Ar.Ht
end

