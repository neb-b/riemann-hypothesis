module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2639
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2365
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2662
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0010
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2642
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismMatrixTorsionAdjointOnCharactersStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endomorphism_matrix_torsion_adjoint_on_characters : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W → ∀ (X₀ : Type) [AddCommGroup X₀] (β : LinearMap.BilinForm ℤ X₀), (∀ a b, β a b = β b a) → (∀ a, a ≠ 0 → 0 < β a a) → ∀ sc : ℝ, 0 < sc → ∀ j : u.D.toPre.X ≃+ (Fin 8 → X₀), (∀ χ, l.q χ = sc * (qW W β (j χ) : ℤ)) → ∀ (e : ρ.P.A ⟶ ρ.P.A) (E E' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * E' = E.transpose * (W + W.transpose) → (∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ e.left → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)) → ∀ (F : u.G ⟶ u.G) (eA : u.A.A ⟶ u.A.A), IsMonHom F → eA.left ≫ u.φ = u.φ ≫ e.left → eA.left ≫ genMap u.U = genMap u.U ≫ F.left → ∀ m : u.D.toPre.X →+ u.D.toPre.X, EndChar u.U F m → ∀ χ, j (m χ) = fun a => ∑ b, E' a b • j χ b := by
  first | exact @GlobalTheory.Poinc.FibMatrix.main | exact GlobalTheory.Poinc.FibMatrix.main | (intros; apply GlobalTheory.Poinc.FibMatrix.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleBigCellCoordinatesFlagSpace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CellEtale

theorem etale_of_isOpenImmersion_spec {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (h : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ))) : φ.Etale := by
  have : Etale (Spec.map (CommRingCat.ofHom φ)) := inferInstance
  exact (HasRingHomProperty.Spec_iff (P := @Etale)).1 this

theorem etale_of_subsingleton {A B : Type} [CommRing A] [CommRing B] [Subsingleton B] (φ : A →+* B) :
    φ.Etale := by
  letI := φ.toAlgebra
  have : IsLocalization.Away (0 : A) B := by
    refine ⟨fun ⟨y, _⟩ => isUnit_of_subsingleton _, fun z => ⟨⟨0, 1⟩, Subsingleton.elim _ _⟩,
      fun {x y} _ => ⟨⟨0, 1, pow_one 0⟩, by simp⟩⟩
  have : Algebra.Etale A B := Algebra.Etale.of_isLocalizationAway (0 : A)
  exact RingHom.etale_algebraMap.2 this

theorem normal_mvPolynomial : ∀ (X : Scheme.{0}) (K : Type) [Field K] (s : X ⟶ Spec (CommRingCat.of K)) [Smooth s] (U : X.affineOpens) (ι : Type) [Finite ι], IsNoetherianRing (MvPolynomial ι Γ(X, U.1)) ∧ ∀ (𝔭 : Ideal (MvPolynomial ι Γ(X, U.1))) [𝔭.IsPrime], IsDomain (Localization.AtPrime 𝔭) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔭) := by
  intro X K _ s _ U ι _
  have h1 := HasRingHomProperty.appLE (P := @Smooth) s inferInstance ⟨⊤, isAffineOpen_top _⟩ U (by simp)
  let g : K →+* Γ(X, U.1) := (s.appLE ⊤ U.1 (by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hg : g.Smooth := by
    refine RingHom.Smooth.comp ?_ h1
    exact RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)
  let G : K →+* MvPolynomial ι Γ(X, U.1) := MvPolynomial.C.comp g
  have hC : (MvPolynomial.C : Γ(X, U.1) →+* MvPolynomial ι Γ(X, U.1)).Smooth :=
    RingHom.smooth_algebraMap.2 { formallySmooth := inferInstance, finitePresentation := Algebra.FinitePresentation.mvPolynomial Γ(X, U.1) Γ(X, U.1) ι }
  have hG : G.Smooth := RingHom.Smooth.comp hg hC
  algebraize [G]
  refine ⟨?_, fun 𝔭 _ => GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_smooth K 𝔭 _⟩
  have : Algebra.FiniteType K (MvPolynomial ι Γ(X, U.1)) := inferInstance
  exact Algebra.FiniteType.isNoetherianRing K _

theorem isDomain_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (W : (Y₀ TF.X Z).Opens), IsAffineOpen W → Nonempty W → IsDomain Γ(Y₀ TF.X Z, W) := by
  intro E _ _ _ H Dw l Xo c TF Z hF W hW hne
  obtain ⟨hs, hp, hc⟩ := GlobalTheory.VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF
  have : Smooth (str₀ TF.X Z) := SmoothOfRelativeDimension.smooth (GlobalTheory.FlagTan.dimFlag Dw) _
  have : GeometricallyIntegral (str₀ TF.X Z) := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _
  have hY : IsIntegral (Y₀ TF.X Z) := GeometricallyIntegral.geometrically_isIntegral (f := str₀ TF.X Z) (K := c.F)
    (𝟙 _) (𝟙 _) (str₀ TF.X Z) IsPullback.of_id_fst
  infer_instance

theorem finiteType_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)).FiniteType := by
  intro E _ _ _ H Dw l Xo c TF Z hF U n e v hv W k L N h
  have hπ : LocallyOfFiniteType (toBase TF Z) := by
    have : IsProper TF.X.π := TF.X.proper
    infer_instance
  have h1 := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (toBase TF Z) hπ U ⟨W, h.1⟩ h.2.1
  refine RingHom.FiniteType.of_comp_finiteType
    (f := (MvPolynomial.C : Γ(TF.Y.X, U.1) →+* MvPolynomial (VIx Dw) Γ(TF.Y.X, U.1))) ?_
  rw [MvPolynomial.eval₂Hom_comp_C]
  exact h1

theorem etale_cellCoord : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → ∀ (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) (h : IsCell TF Z U e v W k L N), (MvPolynomial.eval₂Hom ((toBase TF Z).appLE U.1 W h.2.1).hom (cellCoord N)).Etale := by
  intro E _ _ _ H Dw l Xo c TF Z hF U n e v hv W k L N h
  by_cases hW : Nonempty W
  · haveI := isDomain_sections E H Dw l Xo c TF Z hF W h.1 hW
    haveI := TF.smooth
    have : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth (n := Dw.dim) TF.Y.s
    obtain ⟨hN, hA⟩ := normal_mvPolynomial TF.Y.X c.F TF.Y.s U (VIx Dw)
    exact etale_of_isOpenImmersion_spec _ (GlobalTheory.T.isOpenImmersion_specMap_of_quasiFinite_of_normal _ hA
      (finiteType_cell E H Dw l Xo c TF Z hF U n e v hv W k L N h)
      (GlobalTheory.T.locallyQuasiFinite_bigCell_to_base_prod_affineSpace E H Dw l Xo c TF Z hF U n e v hv W k L N h)
      (GlobalTheory.T.exists_open_immersion_big_cell_base_affine_coords E H Dw l Xo c TF Z hF U n e v hv W k L N h hW))
  · haveI : Subsingleton Γ(Y₀ TF.X Z, W) := by
      have hE : IsEmpty W := not_nonempty_iff.1 hW
      have : IsEmpty (Spec Γ(Y₀ TF.X Z, W)) := (Scheme.Hom.homeomorph h.1.isoSpec.hom).isEmpty_congr.1 hE
      by_contra hs
      rw [not_subsingleton_iff_nontrivial] at hs
      obtain ⟨m, hm⟩ := Ideal.exists_maximal Γ(Y₀ TF.X Z, W)
      exact this.elim ⟨m, hm.isPrime⟩
    exact etale_of_subsingleton _

end GlobalTheory.CellEtale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgEquivExtendingPadicAlgCl
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped TensorProduct
open scoped Classical

namespace GlobalTheory.LKTrip

theorem exists_algEquiv_extending_padicAlgCl {p : ℕ} [Fact p.Prime]
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (φ : E →ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ x : E, σ x = φ x := by
  refine ⟨AlgEquiv.ofBijective (φ.liftNormal (PadicAlgCl p))
    (Algebra.IsAlgebraic.algHom_bijective _), fun x => ?_⟩
  exact φ.liftNormal_commutes (PadicAlgCl p) x

theorem HTGroup.sum_finrank_Fw_eq_finrank_Kq {p : ℕ} [Fact p.Prime] (G : HTGroup p) :
    ∑ w : Fin G.m, Module.finrank ℚ_[p] (G.Fw w) = Module.finrank G.Kq G.F := by
  letI : Algebra G.Kq (PadicAlgCl p) := ((algebraMap ℚ_[p] (PadicAlgCl p)).comp G.u).toAlgebra
  haveI : FiniteDimensional G.Kq G.F := Module.Finite.of_restrictScalars_finite ℚ G.Kq G.F
  let f : (Σ w : Fin G.m, (G.Fw w →ₐ[ℚ_[p]] PadicAlgCl p)) → (G.F →ₐ[G.Kq] PadicAlgCl p) := fun a =>
    { (a.2 : G.Fw a.1 →+* PadicAlgCl p).comp (G.embW a.1) with
      commutes' := fun x => by
        have h : G.embW a.1 (x : G.F) = algebraMap ℚ_[p] (G.Fw a.1) (G.u x) :=
          Subtype.ext (G.emb_over a.1 x)
        change a.2 (G.embW a.1 (x : G.F)) = algebraMap ℚ_[p] (PadicAlgCl p) (G.u x)
        rw [h, AlgHom.commutes] }
  have hf : ∀ a x, f a x = a.2 (G.embW a.1 x) := fun _ _ => rfl
  have hbij : Function.Bijective f := by
    constructor
    · rintro ⟨w, φ⟩ ⟨w', ψ⟩ h
      have h' : ∀ x, φ (G.embW w x) = ψ (G.embW w' x) := fun x => by
        rw [← hf ⟨w, φ⟩, h, hf]
      obtain ⟨σ, hσ⟩ := exists_algEquiv_extending_padicAlgCl _ φ
      obtain ⟨τ, hτ⟩ := exists_algEquiv_extending_padicAlgCl _ ψ
      obtain rfl : w = w' := by
        refine G.emb_inj w w' (σ.trans τ.symm) (RingHom.ext fun x => ?_)
        change τ.symm (σ (G.emb w x)) = G.emb w' x
        rw [AlgEquiv.symm_apply_eq]
        exact (hσ (G.embW w x)).trans ((h' x).trans (hτ (G.embW w' x)).symm)
      obtain rfl : φ = ψ := by
        refine IntermediateField.adjoin_algHom_ext ℚ_[p] ?_
        rintro _ ⟨x, rfl⟩
        exact h' x
      rfl
    · intro τ
      obtain ⟨w, σ, h⟩ := G.emb_all (τ : G.F →+* PadicAlgCl p) (fun x => τ.commutes x)
      refine ⟨⟨w, (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p).comp (G.Fw w).val⟩, AlgHom.ext fun x => ?_⟩
      exact (DFunLike.congr_fun h x).symm
  have hc := Fintype.card_of_bijective hbij
  rw [Fintype.card_sigma, AlgHom.card] at hc
  simpa only [AlgHom.card] using hc

theorem HTGroup.two_mul_sum_finrank_Fw (p : ℕ) [Fact p.Prime] (G : HTGroup p) :
    2 * ∑ w : Fin G.m, Module.finrank ℚ_[p] (G.Fw w) = Module.finrank ℚ G.F := by
  rw [G.sum_finrank_Fw_eq_finrank_Kq, ← G.hKq.1]
  exact Module.finrank_mul_finrank ℚ G.Kq G.F

end GlobalTheory.LKTrip
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowerLiftOfNonvanishingOnClosed
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.LiftAmple

def chartPullPullPow {X T : Scheme.{0}} (L : LB X) (i : T ⟶ X) (n : ℕ) :
    ChartPull ((lbPow L n).pull i) (lbPow (L.pull i) n) (𝟙 T) where
  idx J := J
  le J y hy := mem_powChart.2 (mem_pull.2 (mem_powChart.1 (mem_pull.1 hy)))
  g y J J' hJ hJ' := by
    let K : PUnit → (L.pull i).ι := J
    let K' : PUnit → (L.pull i).ι := J'
    have h₁ : i y ∈ L.U (J PUnit.unit PUnit.unit) := mem_powChart.1 (mem_pull.1 hJ)
    have h₂ : i y ∈ L.U (J' PUnit.unit PUnit.unit) := mem_powChart.1 (mem_pull.1 hJ')
    have k₁ : (𝟙 T) y ∈ powChart (L.pull i) K := mem_powChart.2 (mem_pull.2 h₁)
    have k₂ : (𝟙 T) y ∈ powChart (L.pull i) K' := mem_powChart.2 (mem_pull.2 h₂)
    refine (gm_pull_g (lbPow L n) i (𝟙 T) y J J' hJ hJ').trans ?_
    refine (gm_lbPow_g n (𝟙 T ≫ i) y (J PUnit.unit) (J' PUnit.unit) (mem_powChart.2 h₁)
      (mem_powChart.2 h₂)).trans ?_
    refine Eq.trans ?_ (gm_lbPow_g (L := L.pull i) n (𝟙 T) y K K' k₁ k₂).symm
    rw [gm_pull_g L i (𝟙 T) y (K PUnit.unit) (K' PUnit.unit) (mem_powChart.1 k₁) (mem_powChart.1 k₂)]

theorem exists_sec_pull_pow {X T : Scheme.{0}} (L : LB X) (i : T ⟶ X) (n : ℕ) (σ : (lbPow (L.pull i) n).Sec) :
    ∃ σ' : ((lbPow L n).pull i).Sec, nonzeroLocus σ' = nonzeroLocus σ :=
  ⟨chartSec (chartPullPullPow L i n) σ, nonzeroLocus_chartSec_id _ σ fun _ J hJ =>
    ⟨J, mem_pull.2 (mem_powChart.2 (mem_pull.1 (mem_powChart.1 hJ)))⟩⟩

end GlobalTheory.LiftAmple

namespace GlobalTheory.LiftAmple

theorem exists_sec_nonzero_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (L : LB X), IsAmpleLB L → ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i] (n : ℕ)
    (s : (lbPow (L.pull i) n).Sec), 1 ≤ n → ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s = ⊤ →
    ∃ (N : ℕ) (u : (lbPow L N).Sec), 1 ≤ N ∧ Set.range i ⊆ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  intro k _ X _ p D hX L hL T i _ n s hn hs
  haveI : Module.Finite ℤ k := hX.finite
  haveI : IsNoetherian ℤ k := inferInstance
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ this
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (_root_.GlobalTheory.surjective_toPushforward_app_top_lbPow k X p hX.isProjOver L hL T i)
  have hN : N₀ ≤ n * (N₀ + 1) := by nlinarith
  obtain ⟨σ', hσ'⟩ := exists_sec_pull_pow L i (n * (N₀ + 1)) (secPow s (N₀ + 1))
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.LB.exists_secPull_eq_of_surjective_toPushforward X T i (lbPow L (n * (N₀ + 1))) (isLB_lbPow hL.isLB _) (hN₀ _ hN) σ'
  refine ⟨n * (N₀ + 1), u, by nlinarith, ?_⟩
  rintro _ ⟨z, rfl⟩
  have hz : z ∈ nonzeroLocus (GlobalTheory.secPull u i) := by
    rw [hu, hσ', nonzeroLocus_secPow s (Nat.le_add_left 1 N₀), hs]; trivial
  rw [nonzeroLocus_secPull] at hz
  exact hz

end GlobalTheory.LiftAmple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowerSectionNonvanishingOnFinite
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem exists_sec_nonvanishing_finite : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ S : Set X, S.Finite → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, S ⊆ NV P e 0 f := by
  intro k _ X _ p D _ P hA S hS
  obtain ⟨n, hn, s, h₁, -, -⟩ := hA.exists_affine_finite_subset hS (U := ⊤) (Set.subset_univ _)
  obtain ⟨f, hf, e⟩ := (_root_.GlobalTheory.HSAmp.pow_sec_dict k X p P n).1 s
  refine ⟨n, hn, f, hf, ?_⟩
  rw [e]
  exact h₁

end GlobalTheory.HSAmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArcDatumRecoveringUnitaryDataCompleteDVRStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arcDatum_recovering_unitaryData_completeDVR : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dm : Datum H) (D : DegData R (maximalIdeal R)) [Module (𝓞 E) D.toPre.X] (o : letI := H.starRing; D.toPre.OAct (𝓞 E)), Nontrivial D.toPre.X → PelOK Dm D.toPre o → ∀ (l : Level H) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F), Function.Injective β → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ₁ : R →+* V₁) (b₁ : O →+* V₁), GlobalTheory.LN.CDvr V₁ → Function.Injective ρ₁ → ρ₁.Finite → IsLocalHom ρ₁ → Function.Injective b₁ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (ρ : R →+* V) (b : O →+* V) (ϖ : V) (a : ArcIn Dm l β V b), GlobalTheory.LN.CDvr V ∧ Function.Injective ρ ∧ ρ.Finite ∧ Irreducible ϖ ∧ ∀ (Xo : Moduli Dm l) (Y : Model Xo c β) (y : Sp V ⟶ Y.X), Y.HasArcData a (maximalIdeal V) (RingHom.id V) ϖ y → ∃ (t : SAB H (Sp V)) (_ : SABMap t Y.t y) (P : PELUnif (maximalIdeal V) t), Nonempty (IsPullDeg ρ D.toPre P.D.toPre) := by
  first | exact @GlobalTheory.TraitArc.exists_input_recovering | exact GlobalTheory.TraitArc.exists_input_recovering | (intros; apply GlobalTheory.TraitArc.exists_input_recovering <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisIntKQ
section
open Matrix GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.IntBasisKQ
open ReciprocityTheory.DiscreteGroups.LocalClassField

variable (p : ℕ) [Fact p.Prime]

theorem exists_basis_OK (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (hK : FiniteDimensional ℚ_[p] K) :
    ∃ (ι : Type) (_ : Fintype ι) (β : Module.Basis ι ℚ_[p] K),
      ∀ x : K, x ∈ OK p K ↔ ∀ i, ‖β.repr x i‖ ≤ 1 := by
  letI := zpAlgOK p K
  haveI := isScalarTower_zp_OK p K
  haveI := isIntegralClosure_OK p K
  haveI := isTorsionFree_zp_K p K
  haveI : Module.Free ℤ_[p] (OK p K) := IsIntegralClosure.module_free ℤ_[p] ℚ_[p] K _
  haveI : Module.Finite ℤ_[p] (OK p K) := IsIntegralClosure.finite ℤ_[p] ℚ_[p] K _
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (OK p K) (nonZeroDivisors ℤ_[p])) K :=
    IsIntegralClosure.isLocalization ℤ_[p] ℚ_[p] K (OK p K)
  let β₀ := Module.finBasis ℤ_[p] (OK p K)
  let β := β₀.localizationLocalization ℚ_[p] (nonZeroDivisors ℤ_[p]) K
  refine ⟨_, inferInstance, β, fun x => ⟨fun hx i => ?_, fun hx => ?_⟩⟩
  · have e : x = algebraMap (OK p K) K ⟨x, hx⟩ := rfl
    rw [e, Module.Basis.localizationLocalization_repr_algebraMap]
    exact (β₀.repr ⟨x, hx⟩ i).2
  · let z : _ → ℤ_[p] := fun i => ⟨β.repr x i, hx i⟩
    have hx' : x = algebraMap (OK p K) K (∑ i, z i • β₀ i) := by
      conv_lhs => rw [← β.sum_repr x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply ℤ_[p] (OK p K) K,
        IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] K, ← Module.Basis.localizationLocalization_apply ℚ_[p]
        (nonZeroDivisors ℤ_[p]) K]
      rfl
    rw [hx']
    exact (∑ i, z i • β₀ i).2

end GlobalTheory.IntBasisKQ

namespace GlobalTheory.IntBasisKQ

variable (p : ℕ) [Fact p.Prime]

section Tensor

variable {A B : Type} [CommRing A] [Algebra ℚ_[p] A] [CommRing B] [Algebra ℚ_[p] B]
  {ι κ : Type} [Fintype ι] [Fintype κ] (β : Module.Basis ι ℚ_[p] A) (γ : Module.Basis κ ℚ_[p] B)
  (OA : Subring A) (OB : Subring B)

def IntCoord (z : A ⊗[ℚ_[p]] B) : Prop := ∀ k, ‖(β.tensorProduct γ).repr z k‖ ≤ 1

variable {p β γ}

theorem intCoord_add {z w : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) (hw : IntCoord p β γ w) :
    IntCoord p β γ (z + w) := fun k => by
  rw [map_add (f := _), Finsupp.add_apply]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hz k) (hw k))

theorem intCoord_smul {z : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) {c : ℚ_[p]} (hc : ‖c‖ ≤ 1) :
    IntCoord p β γ (c • z) := fun k => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) (hz k)

theorem intCoord_neg {z : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) : IntCoord p β γ (-z) := fun k => by
  rw [map_neg, Finsupp.neg_apply, norm_neg]
  exact hz k

theorem intCoord_zero : IntCoord p β γ (0 : A ⊗[ℚ_[p]] B) := fun k => by simp

theorem intCoord_sum {σ : Type} (s : Finset σ) (f : σ → A ⊗[ℚ_[p]] B) (h : ∀ t ∈ s, IntCoord p β γ (f t)) :
    IntCoord p β γ (∑ t ∈ s, f t) := by
  induction s using Finset.induction_on with
  | empty => simpa using intCoord_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact intCoord_add (h a (Finset.mem_insert_self _ _)) (ih fun t ht => h t (Finset.mem_insert_of_mem ht))

variable {OA OB}

theorem intCoord_tmul (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (hB : ∀ y, y ∈ OB ↔ ∀ j, ‖γ.repr y j‖ ≤ 1)
    {a : A} {b : B} (ha : a ∈ OA) (hb : b ∈ OB) : IntCoord p β γ (a ⊗ₜ[ℚ_[p]] b) := fun ⟨i, j⟩ => by
  rw [Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul, norm_mul]
  exact mul_le_one₀ ((hB b).1 hb j) (norm_nonneg _) ((hA a).1 ha i)

theorem basis_mem (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (i : ι) : β i ∈ OA :=
  (hA _).2 fun i' => by
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem intCoord_mul (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (hB : ∀ y, y ∈ OB ↔ ∀ j, ‖γ.repr y j‖ ≤ 1)
    {z w : A ⊗[ℚ_[p]] B} (hz : IntCoord p β γ z) (hw : IntCoord p β γ w) : IntCoord p β γ (z * w) := by
  set b := β.tensorProduct γ
  have e : z * w = ∑ k, ∑ l, (b.repr z k * b.repr w l) • (b k * b l) := by
    conv_lhs => rw [← b.sum_repr z, ← b.sum_repr w]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm]
  rw [e]
  refine intCoord_sum _ _ fun k _ => intCoord_sum _ _ fun l _ => intCoord_smul ?_ ?_
  · obtain ⟨i, j⟩ := k
    obtain ⟨i', j'⟩ := l
    simp only [b, Module.Basis.tensorProduct_apply, Algebra.TensorProduct.tmul_mul_tmul]
    exact intCoord_tmul hA hB (OA.mul_mem (basis_mem hA i) (basis_mem hA i'))
      (OB.mul_mem (basis_mem hB j) (basis_mem hB j'))
  · rw [norm_mul]
    exact mul_le_one₀ (hz k) (norm_nonneg _) (hw l)

theorem mem_closure_iff (hA : ∀ x, x ∈ OA ↔ ∀ i, ‖β.repr x i‖ ≤ 1) (hB : ∀ y, y ∈ OB ↔ ∀ j, ‖γ.repr y j‖ ≤ 1)
    (z : A ⊗[ℚ_[p]] B) :
    z ∈ Subring.closure (Set.range (fun a : OA => (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) a) ∪
      Set.range (fun b : OB => (Algebra.TensorProduct.includeRight : B →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) b)) ↔
      ∀ k, ‖(β.tensorProduct γ).repr z k‖ ≤ 1 := by
  let S : Subring (A ⊗[ℚ_[p]] B) :=
    { carrier := {z | IntCoord p β γ z}
      mul_mem' := intCoord_mul hA hB
      one_mem' := intCoord_tmul hA hB OA.one_mem OB.one_mem
      add_mem' := intCoord_add
      zero_mem' := intCoord_zero
      neg_mem' := intCoord_neg }
  constructor
  · intro hz
    refine (Subring.closure_le (t := S)).2 (Set.union_subset ?_ ?_) hz
    · rintro _ ⟨a, rfl⟩
      exact intCoord_tmul hA hB a.2 OB.one_mem
    · rintro _ ⟨b, rfl⟩
      exact intCoord_tmul hA hB OA.one_mem b.2
  · intro hz
    rw [← (β.tensorProduct γ).sum_repr z]
    refine Subring.sum_mem _ fun ⟨i, j⟩ _ => ?_
    rw [Module.Basis.tensorProduct_apply, TensorProduct.smul_tmul',
      show ((β.tensorProduct γ).repr z (i, j) • β i) ⊗ₜ[ℚ_[p]] γ j =
        (Algebra.TensorProduct.includeLeft : A →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) ((β.tensorProduct γ).repr z (i, j) • β i) *
        (Algebra.TensorProduct.includeRight : B →ₐ[ℚ_[p]] A ⊗[ℚ_[p]] B) (γ j) by
          rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]]
    refine Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨_, ?_⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨_, basis_mem hB j⟩, rfl⟩))
    refine (hA _).2 fun i' => ?_
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, norm_mul]
    refine mul_le_one₀ (hz (i, j)) (norm_nonneg _) ?_
    split_ifs <;> simp

end Tensor

end GlobalTheory.IntBasisKQ

namespace GlobalTheory.IntBasisKQ

theorem exists_basis_intKQ : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (r : ℕ), 0 < r → ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℚ_[p] (KQ p K r)),
      ∀ x, x ∈ intKQ p K r ↔ ∀ i, ‖b.repr x i‖ ≤ 1 := by
  intro p _ K hK r hr
  obtain ⟨ι₁, _, β, hβ⟩ := exists_basis_OK p K hK
  obtain ⟨ι₂, _, γ, hγ⟩ := exists_basis_OK p (Qr p r)
    (ReciprocityTheory.DiscreteGroups.LocalClassField.finiteDimensional_Kn p (Q0 p) inferInstance hr)
  refine ⟨ι₁ × ι₂, inferInstance, β.tensorProduct γ, fun x => ?_⟩
  exact mem_closure_iff (OA := GlobalTheory.LKLoc.intK p K) (OB := GlobalTheory.LKLoc.intR p (Q0 p) r) hβ hγ x

end GlobalTheory.IntBasisKQ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantBijectionLargerClosedFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equivariant_bijection_larger_closed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E₀ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N), Eqv D.toPre A (Kb R) N lab E₀ → (∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) lab', LabExt em lab lab' → ∃ E', Eqv D.toPre A F N lab' E' ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E' s) (Φ F₀) := by
  first | exact @GlobalTheory.Mum.UpExt.exists_eqv_ext | exact GlobalTheory.Mum.UpExt.exists_eqv_ext | (intros; apply GlobalTheory.Mum.UpExt.exists_eqv_ext <;> assumption)
end

