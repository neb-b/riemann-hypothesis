module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0010

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LePreimageOfClosedPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.FormalChart

section Alg

variable {O : Type} [CommRing O] {B : Type} [CommRing B] [Algebra O B] {g : ℕ}

theorem ext_of_isHausdorff (π : MvPolynomial (Fin g) O →ₐ[O] B) (hπ : π.toRingHom.Etale)
    {A : Type} [CommRing A] [Algebra O A] (J : Ideal A) [IsHausdorff J A] (φ₁ φ₂ : B →ₐ[O] A)
    (h : ∀ b, φ₁ b - φ₂ b ∈ J)
    (hs : ∀ j : Fin g, φ₁ (π (MvPolynomial.X j)) = φ₂ (π (MvPolynomial.X j))) : φ₁ = φ₂ := by
  letI : Algebra (MvPolynomial (Fin g) O) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin g) O) B := hπ
  let ρ : MvPolynomial (Fin g) O →ₐ[O] A := φ₁.comp π
  have hρ2 : φ₂.comp π = ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    exact (hs j).symm
  letI : Algebra (MvPolynomial (Fin g) O) A := ρ.toRingHom.toAlgebra
  let ψ₁ : B →ₐ[MvPolynomial (Fin g) O] A :=
    { φ₁.toRingHom with commutes' := fun p => rfl }
  let ψ₂ : B →ₐ[MvPolynomial (Fin g) O] A :=
    { φ₂.toRingHom with commutes' := fun p => AlgHom.congr_fun hρ2 p }
  have hJ : ⨅ i, J ^ i = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact GlobalTheory.eq_of_forall_sub_mem_ideal_pow J fun n => by
      rw [sub_zero]
      exact Ideal.mem_iInf.1 hx n
  have : ψ₁ = ψ₂ := Algebra.FormallyUnramified.ext_of_iInf J hJ fun b => Ideal.Quotient.eq.2 (h b)
  ext x
  exact AlgHom.congr_fun this x

theorem exists_expansion (π : MvPolynomial (Fin g) O →ₐ[O] B) (hπ : π.toRingHom.Etale)
    (e : B →ₐ[O] O) :
    ∃ φ : B →ₐ[O] MvPowerSeries (Fin g) O, (∀ b, MvPowerSeries.constantCoeff (φ b) = e b) ∧
      ∀ j, φ (π (MvPolynomial.X j) - algebraMap O B (e (π (MvPolynomial.X j)))) = MvPowerSeries.X j := by
  letI : Algebra (MvPolynomial (Fin g) O) B := π.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin g) O) B := hπ
  let A := MvPowerSeries (Fin g) O
  let ρ : MvPolynomial (Fin g) O →ₐ[O] A :=
    MvPolynomial.aeval (fun j => algebraMap O A (e (π (MvPolynomial.X j))) + MvPowerSeries.X j)
  letI : Algebra (MvPolynomial (Fin g) O) A := ρ.toRingHom.toAlgebra
  let J : Ideal A := Ideal.span (Set.range MvPowerSeries.X)
  have hf₀ : ((Ideal.Quotient.mkₐ O J).comp ((Algebra.ofId O A).comp e)).comp π =
      (Ideal.Quotient.mkₐ O J).comp ρ := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ρ,
      MvPolynomial.aeval_X, Algebra.ofId_apply]
    rw [eq_comm, Ideal.Quotient.eq, add_sub_cancel_left]
    exact Ideal.subset_span ⟨j, rfl⟩
  let f₀ : B →ₐ[MvPolynomial (Fin g) O] A ⧸ J :=
    { ((Ideal.Quotient.mkₐ O J).comp ((Algebra.ofId O A).comp e)).toRingHom with
      commutes' := fun p => AlgHom.congr_fun hf₀ p }
  obtain ⟨φ', hφ'⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (I := J) f₀
  have hc : ∀ p, φ' (π p) = ρ p := fun p => φ'.commutes p
  let φ : B →ₐ[O] A := { φ'.toRingHom with
    commutes' := fun r => by
      show φ' (algebraMap O B r) = _
      rw [← π.commutes, hc, ρ.commutes] }
  have hφ : ∀ b, φ b = φ' b := fun _ => rfl
  have hJ : J ≤ RingHom.ker (MvPowerSeries.constantCoeff) := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact MvPowerSeries.constantCoeff_X i
  refine ⟨φ, fun b => ?_, fun j => ?_⟩
  · have e1 : Ideal.Quotient.mk J (φ' b) = Ideal.Quotient.mk J (algebraMap O A (e b)) :=
      AlgHom.congr_fun hφ' b
    rw [Ideal.Quotient.eq] at e1
    have e2 := hJ e1
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at e2
    exact e2.trans (MvPowerSeries.constantCoeff_C _)
  · rw [map_sub, AlgHom.commutes, hφ, hc]
    simp [ρ]

theorem exists_factor (π : MvPolynomial (Fin g) O →ₐ[O] B) (hπ : π.toRingHom.Etale)
    (e : B →ₐ[O] O) (φ : B →ₐ[O] MvPowerSeries (Fin g) O)
    (h₁ : ∀ b, MvPowerSeries.constantCoeff (φ b) = e b)
    (h₂ : ∀ j, φ (π (MvPolynomial.X j) - algebraMap O B (e (π (MvPolynomial.X j)))) = MvPowerSeries.X j)
    {T : Type} [CommRing T] [Algebra O T] (J : Ideal T) [IsAdicComplete J T] (ψ : B →ₐ[O] T)
    (hψ : ∀ b, ψ b - algebraMap O T (e b) ∈ J) :
    ∃ v : MvPowerSeries (Fin g) O →ₐ[O] T, (∀ i, v (MvPowerSeries.X i) ∈ J) ∧ v.comp φ = ψ := by
  let v := GlobalTheory.mvEvalAdic O J (fun j => ψ (π (MvPolynomial.X j)) - algebraMap O T (e (π (MvPolynomial.X j))))
    (fun j => hψ _)
  have hv : ∀ j, v (MvPowerSeries.X j) =
      ψ (π (MvPolynomial.X j)) - algebraMap O T (e (π (MvPolynomial.X j))) := fun j =>
    GlobalTheory.mvEvalAdic_X _ _ _ j
  have hv' : ∀ j, v (MvPowerSeries.X j) ∈ J := fun j => hv j ▸ hψ _
  refine ⟨v, hv', ext_of_isHausdorff π hπ J _ _ (fun b => ?_) (fun j => ?_)⟩
  · have := GlobalTheory.algHom_sub_constantCoeff_mem v hv' (φ b)
    rw [h₁] at this
    have h3 := sub_mem this (hψ b)
    rwa [sub_sub_sub_cancel_right] at h3
  · have := hv j
    rw [← h₂, map_sub, map_sub, AlgHom.commutes, AlgHom.commutes, sub_left_inj] at this
    exact this

end Alg

section Geo
open GlobalTheory.KeyKa.EtBaseChange

variable {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {T : Type} [CommRing T]

theorem spMap_valH (w : Sp T ⟶ X) (hw : ⊤ ≤ w ⁻¹ᵁ V) :
    spMap (R := Γ(X, V)) (valH w V hw) ≫ hV.fromSpec = w := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec w hV (isAffineOpen_top (Spec (CommRingCat.of T))) hw
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  show Spec.map (w.appLE V ⊤ hw ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom) ≫ hV.fromSpec = w
  rw [Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem le_preimage (φ : Γ(X, V) →+* T) : ⊤ ≤ (spMap (R := Γ(X, V)) φ ≫ hV.fromSpec) ⁻¹ᵁ V :=
  fun _ _ => hV.range_fromSpec.subset (Set.mem_range_self _)

theorem valH_spMap (φ : Γ(X, V) →+* T) :
    valH (spMap (R := Γ(X, V)) φ ≫ hV.fromSpec) V (le_preimage hV φ) = φ := by
  have h := spMap_valH hV _ (le_preimage hV φ)
  rw [cancel_mono] at h
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem spMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R')
    (f' : R' →+* R'') : spMap (f'.comp f) = spMap f' ≫ spMap f := by
  rw [← Spec.map_comp]
  rfl

theorem fromSpec_comp {O : Type} [CommRing O] (h : X ⟶ Sp O) :
    hV.fromSpec ≫ h = spMap (R' := Γ(X, V))
      ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ h.appLE ⊤ V le_top).hom := by
  have e := IsAffineOpen.SpecMap_appLE_fromSpec h (isAffineOpen_top (Spec (CommRingCat.of O))) hV
    (le_top : V ≤ h ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at e
  rw [← e, ← Spec.map_comp]
  rfl

theorem le_preimage_of_closedPoint [IsLocalRing T] (w : Sp T ⟶ X)
    (hw : w (IsLocalRing.closedPoint T) ∈ V) : ⊤ ≤ w ⁻¹ᵁ V := fun p _ =>
  ((IsLocalRing.specializes_closedPoint p).map w.continuous).mem_open V.isOpen hw

end Geo


open GlobalTheory.KeyKa.EtBaseChange in
theorem exists_formal_chart : ∀ (O : Type) [CommRing O] [IsLocalRing O] (X : Scheme.{0}) (h : X ⟶ Sp O) (g : ℕ) (z : Sp O ⟶ X), SmoothOfRelativeDimension g h → z ≫ h = 𝟙 _ → ∃ θ : Sp (MvPowerSeries (Fin g) O) ⟶ X, θ (IsLocalRing.closedPoint (MvPowerSeries (Fin g) O)) = z (IsLocalRing.closedPoint O) ∧ θ ≫ h = spMap (algebraMap O (MvPowerSeries (Fin g) O)) ∧ (∃ (V : X.Opens) (t : Fin g → Γ(X, V)), ⊤ ≤ θ ⁻¹ᵁ V ∧ ∀ i, valT (T := (MvPowerSeries (Fin g) O)) θ V (t i) = MvPowerSeries.X i) ∧ (∀ (T : Type) [CommRing T] [IsLocalRing T] [Algebra O T] [IsAdicComplete (IsLocalRing.maximalIdeal T) T] (w : Sp T ⟶ X), w ≫ h = spMap (algebraMap O T) → w (IsLocalRing.closedPoint T) = θ (IsLocalRing.closedPoint (MvPowerSeries (Fin g) O)) → ∃ e : (MvPowerSeries (Fin g) O) →ₐ[O] T, (∀ i, e (MvPowerSeries.X i) ∈ IsLocalRing.maximalIdeal T) ∧ spMap e.toRingHom ≫ θ = w) := by
  intro O _ _ X h g z hG hz
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ :=
    hG.exists_isStandardSmoothOfRelativeDimension (z (IsLocalRing.closedPoint O))
  have hU' : U = ⊤ := by
    have h1 : (z ≫ h) (IsLocalRing.closedPoint O) ∈ U :=
      (Scheme.Hom.comp_apply z h (IsLocalRing.closedPoint O)).symm ▸ e hx
    have h2 := le_preimage_of_closedPoint (z ≫ h) h1
    rw [hz] at h2
    exact eq_top_iff.2 h2
  subst hU'
  let a : O →+* Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ h.appLE ⊤ V le_top).hom
  have ha : hV.fromSpec ≫ h = spMap (R' := Γ(X, V)) a := fromSpec_comp hV h
  have h2 : RingHom.IsStandardSmoothOfRelativeDimension g a :=
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
      (Scheme.ΓSpecIso (CommRingCat.of O)).symm.commRingCatIsoToRingEquiv hs
  obtain ⟨π₀, hπ1, hπ⟩ := h2.exists_etale_mvPolynomial
  clear_value a
  letI : Algebra O Γ(X, V) := a.toAlgebra
  let π : MvPolynomial (Fin g) O →ₐ[O] Γ(X, V) := { π₀ with commutes' := fun r => RingHom.congr_fun hπ1 r }
  have hpt : ∀ (T : Type) [CommRing T] [Algebra O T] (w : Sp T ⟶ X), ⊤ ≤ w ⁻¹ᵁ V →
      w ≫ h = spMap (algebraMap O T) →
      ∃ ψ : Γ(X, V) →ₐ[O] T, spMap (R := Γ(X, V)) ψ.toRingHom ≫ hV.fromSpec = w := by
    intro T _ _ w hw hw'
    have e1 := spMap_valH hV w hw
    have e2 : spMap ((valH w V hw).comp a) = spMap (algebraMap O T) := by
      rw [spMap_comp, ← ha, ← Category.assoc, e1, hw']
    have e3 : (valH w V hw).comp a = algebraMap O T :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
    exact ⟨⟨valH w V hw, fun r => RingHom.congr_fun e3 r⟩, e1⟩
  obtain ⟨ε, rfl⟩ := hpt O z (le_preimage_of_closedPoint z hx) (hz.trans (Spec.map_id _).symm)
  obtain ⟨φ, hφ₁, hφ₂⟩ := exists_expansion π hπ ε
  have hcl : (spMap (R := Γ(X, V)) φ.toRingHom ≫ hV.fromSpec)
      (IsLocalRing.closedPoint (MvPowerSeries (Fin g) O)) =
      (spMap (R := Γ(X, V)) ε.toRingHom ≫ hV.fromSpec) (IsLocalRing.closedPoint O) := by
    refine congrArg hV.fromSpec (PrimeSpectrum.ext (Ideal.ext fun b => ?_))
    show φ b ∈ IsLocalRing.maximalIdeal _ ↔ ε b ∈ IsLocalRing.maximalIdeal _
    rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
      MvPowerSeries.isUnit_iff_constantCoeff, hφ₁]
  refine ⟨spMap (R := Γ(X, V)) φ.toRingHom ≫ hV.fromSpec, hcl, ?_,
    ⟨V, fun j => π (MvPolynomial.X j) - algebraMap O _ (ε (π (MvPolynomial.X j))), le_preimage hV _,
      fun j => ?_⟩, ?_⟩
  · rw [Category.assoc, ha, ← spMap_comp]
    exact congrArg spMap φ.comp_algebraMap
  · rw [valT_eq _ _ (le_preimage hV _), valH_spMap]
    exact hφ₂ j
  · intro T _ _ _ _ w hw hw'
    rw [hcl] at hw'
    obtain ⟨ψ, rfl⟩ := hpt T w (le_preimage_of_closedPoint w (hw' ▸ hx)) hw
    have h3 := congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective hw')
    obtain ⟨v, hv, rfl⟩ := exists_factor π hπ ε φ hφ₁ hφ₂ (IsLocalRing.maximalIdeal T) ψ fun b => by
      have h4 : b - algebraMap O _ (ε b) ∈ (IsLocalRing.maximalIdeal O).comap ε.toRingHom := by
        show ε (b - algebraMap O _ (ε b)) ∈ IsLocalRing.maximalIdeal O
        simp
      have h5 : ψ (b - algebraMap O _ (ε b)) ∈ IsLocalRing.maximalIdeal T := h3.ge h4
      rwa [map_sub, AlgHom.commutes] at h5
    refine ⟨v, hv, ?_⟩
    rw [← Category.assoc, ← spMap_comp]
    rfl

end GlobalTheory.FormalChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LineBundlePowSectionsEqThetaLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.LevelDict

section Charts

variable {X : Scheme.{0}} (L : LB X) (n : ℕ)

theorem sec_ext {M : LB X} {s t : M.Sec} (h : ∀ i, s.f i = t.f i) : s = t := by
  obtain ⟨f, hf⟩ := s
  obtain ⟨f', hf'⟩ := t
  obtain rfl : f = f' := funext h
  rfl

theorem powChart_le (j : (lbPow L n).ι) : (lbPow L n).U j ≤ L.U (j PUnit.unit) :=
  fun _ hy => Set.mem_iInter.1 hy PUnit.unit

theorem le_powChart (j : (lbPow L n).ι) : L.U (j PUnit.unit) ≤ (lbPow L n).U j :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy

theorem lbPow_g (j j' : (lbPow L n).ι) : ((lbPow L n).g j j').val =
    rs X (inf_le_inf (powChart_le L n j) (powChart_le L n j'))
      (L.g (j PUnit.unit) (j' PUnit.unit) ^ (n : ℤ)).val := by
  have h : (lbPow L n).g j j' = res (inf_le_inf (powChart_le L n j) (powChart_le L n j'))
      (L.g (j PUnit.unit) (j' PUnit.unit) ^ (n : ℤ)) := by
    rw [map_zpow]
    unfold lbPow LB.LinComb
    dsimp only
    rw [Fintype.prod_unique]
    rfl
  rw [h]
  rfl

def powSecEquiv : (lbPow L n).Sec ≃ (pw L (n : ℤ)).Sec where
  toFun s := ⟨fun i => rs X (le_powChart L n fun _ => i) (s.f fun _ => i), fun i k => by
    have h := congrArg (rs X (inf_le_inf (le_powChart L n fun _ => i) (le_powChart L n fun _ => k)))
      (s.compat (fun _ => i) (fun _ => k))
    refine (rs_rs _ _ _).trans ((rs_rs _ _ _).symm.trans (h.trans ((map_mul _ _ _).trans ?_)))
    exact congrArg₂ (· * ·) ((congrArg _ (lbPow_g L n _ _)).trans ((rs_rs _ _ _).trans (rs_self _ _)))
      ((rs_rs _ _ _).trans (rs_rs _ _ _).symm)⟩
  invFun s := ⟨fun j => rs X (powChart_le L n j) (s.f (j PUnit.unit)), fun j k => by
    have h := congrArg (rs X (inf_le_inf (powChart_le L n j) (powChart_le L n k)))
      (s.compat (j PUnit.unit) (k PUnit.unit))
    rw [lbPow_g]
    refine (rs_rs _ _ _).trans ((rs_rs _ _ _).symm.trans (h.trans ((map_mul _ _ _).trans ?_)))
    exact congrArg _ ((rs_rs _ _ _).trans (rs_rs _ _ _).symm)⟩
  left_inv s := sec_ext fun _ => (rs_rs _ _ _).trans (rs_self _ _)
  right_inv s := sec_ext fun _ => (rs_rs _ _ _).trans (rs_self _ _)

theorem valAt'_powSecEquiv (s : (lbPow L n).Sec) (x : Sp ℂ ⟶ X) (j : (lbPow L n).ι)
    (h : ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit)) :
    valAt' x (L.U (j PUnit.unit)) ((powSecEquiv L n s).f (j PUnit.unit)) = valAt' x ((lbPow L n).U j) (s.f j) :=
  valAt'_map x (homOfLE (le_powChart L n j)).op (s.f j) h

end Charts

theorem transfer {S S' T T' : Type*} (E : S ≃ S') (G : T ≃ T') {P : T → Prop} {P' : T' → Prop} {Q : S → T → Prop}
    {Q' : S' → T' → Prop} (hP : ∀ t, P' (G t) ↔ P t) (hQ : ∀ s t, Q' (E s) (G t) ↔ Q s t)
    (h : (∀ s, ∃! t, P t ∧ Q s t) ∧ ∀ t, P t → ∃! s, Q s t) :
    (∀ s, ∃! t, P' t ∧ Q' s t) ∧ ∀ t, P' t → ∃! s, Q' s t := by
  refine ⟨fun s => ?_, fun t ht => ?_⟩
  · obtain ⟨s, rfl⟩ := E.surjective s
    rw [← G.existsUnique_congr (p := fun t => P t ∧ Q s t) fun t => by rw [hP, hQ]]
    exact h.1 s
  · obtain ⟨t, rfl⟩ := G.surjective t
    rw [← E.existsUnique_congr (p := fun s => Q s t) fun s => by rw [hQ]]
    exact h.2 t ((hP t).1 ht)

theorem ext_of_ne_zero {g : ℕ} {θ f f' : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0) (hf : Continuous f)
    (hf' : Continuous f') (h : ∀ z, θ z ≠ 0 → f z = f' z) : ∀ z, f z = f' z :=
  congrFun (Continuous.ext_on (ThetaTangent.dense_ne_zero hθ h0) hf hf' h)

section Frames

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ}


open PullHermitian in
theorem exists_frame_ratio (hL : L.IsLB) (u u₀ : HolUnif A L g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hF : ∀ z, u₀.ex (F z) = u.ex z) :
    ∃ r : (Fin g → ℂ) → ℂ, Differentiable ℂ r ∧ (∀ z, r z ≠ 0) ∧
      ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i → u₀.fr i (F z) = r z * u.fr i z := by
  have hFd : Differentiable ℂ F := (LinearMap.toContinuousLinearMap F).differentiable
  have tr : ∀ {U : A.left.Opens} {z}, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → ⊤ ≤ (u₀.ex (F z)).left ⁻¹ᵁ U :=
    fun h => by rwa [hF]
  obtain ⟨r, hr, hrφ⟩ := exists_glue
    (fun i : L.ι => {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
    (fun i => (u.hol _ 0).1)
    (fun z => PullHermitian.exists_chart (u.ex z).left hL)
    (fun i z => u₀.fr i (F z) / u.fr i z)
    (fun i => by
      have d2 := (u₀.fr_hol i).comp (s := {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i})
        hFd.differentiableOn fun z hz => tr hz
      simp only [div_eq_mul_inv]
      exact d2.mul ((u.fr_hol i).inv fun z hz => u.fr_ne i z hz))
    (fun i j z hi hj => by
      have h1 := u.fr_compat i j z (inf_of _ hi hj)
      have h2 := u₀.fr_compat i j (F z) (tr (inf_of _ hi hj))
      rw [hF] at h2
      rw [div_eq_div_iff (u.fr_ne _ _ hi) (u.fr_ne _ _ hj), h1, h2]
      ring)
  refine ⟨r, hr, fun z => ?_, fun i z hi => ?_⟩
  · obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left hL
    rw [hrφ i z hi]
    exact div_ne_zero (u₀.fr_ne _ _ (tr hi)) (u.fr_ne _ _ hi)
  · rw [hrφ i z hi, div_mul_cancel₀ _ (u.fr_ne _ _ hi)]

end Frames

theorem isLevel_thetaChar {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) (hab : charHalf g a b) :
    IsLevel τ a b 1 (thetaChar τ a b) ∧ thetaChar τ a b ≠ 0 := by
  obtain ⟨h0, h1, -⟩ := TorusAlg.thetaChar_level hs hp hab.1 hab.2
  have hm : thetaChar τ a b ∈ thetaLevelChar (fun i => (a i).re) (fun i => (b i).re) 1 τ := by
    rw [h1]
    exact Submodule.mem_span_singleton_self _
  rw [mem_thetaLevelChar, TorusAlg.ofRealVec_re hab.1, TorusAlg.ofRealVec_re hab.2] at hm
  refine ⟨⟨hm.1, fun m n z => ?_⟩, h0⟩
  have h := hm.2 n m z
  rw [add_assoc, add_comm (τ.mulVec _), ReciprocityTheory.PTheta.eC, ReciprocityTheory.PTheta.eC, ← Complex.exp_add] at h
  refine h.trans ?_
  rw [pow_one]
  congr 2
  unfold ReciprocityTheory.PTheta.ofIntVec
  push_cast
  ring

theorem sections_eq_level : ThetaUnifAV → ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (l : ℕ), charHalf g a b → Wit x h u τ a b → (∀ s : RR x l, ∃! F, IsLevel τ a b l F ∧ FnPw x u s F) ∧ ∀ F, IsLevel τ a b l F → ∃! s : RR x l, FnPw x u s F := by
  intro hT g x h u τ a b l hab ⟨hs, hp, hΛ, _, hth, _⟩
  subst h
  obtain ⟨u₀, H₀, χ₀, -, hu₀, -, hv, hw, -, hsec, -⟩ := hT x.P x.rig x.rig_gen
  obtain ⟨F, hF, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo x.P.A x.P.isAb x.P.L x.P.g x.P.g u₀ hv hw u.ex u.ex_add
    (fun U f => by simpa only [Set.mem_univ, true_and] using u.hol U f)
  let e : (Fin x.P.g → ℂ) ≃ₗ[ℂ] (Fin x.P.g → ℂ) := LinearEquiv.ofInjectiveEndo F (UnifCompare.injective u u₀ F hF)
  have he : ∀ z, e z = F z := fun z => rfl
  have hed : Differentiable ℂ e := (LinearMap.toContinuousLinearMap F).differentiable
  have hed' : Differentiable ℂ e.symm := (LinearMap.toContinuousLinearMap e.symm.toLinearMap).differentiable
  obtain ⟨r, hr, hr0, hrf⟩ := exists_frame_ratio x.P.isLB u u₀ F hF
  obtain ⟨hθ, hθ0⟩ := isLevel_thetaChar hs hp hab
  let G : ((Fin x.P.g → ℂ) → ℂ) ≃ ((Fin x.P.g → ℂ) → ℂ) :=
    { toFun := fun f z => f (e z) * r z ^ l
      invFun := fun f w => f (e.symm w) * (r (e.symm w) ^ l)⁻¹
      left_inv := fun f => funext fun w => by
        simp only [e.apply_symm_apply]
        exact mul_inv_cancel_right₀ (pow_ne_zero _ (hr0 _)) _
      right_inv := fun f => funext fun z => by
        simp only [e.symm_apply_apply]
        exact inv_mul_cancel_right₀ (pow_ne_zero _ (hr0 _)) _ }
  have hG : ∀ f z, G f z = f (e z) * r z ^ l := fun _ _ => rfl

  have key : ∀ (m n : Fin x.P.g → ℤ) (k : u₀.Λ), (k : Fin x.P.g → ℂ) =
      e ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) → ∀ z,
      χ₀ k * Complex.exp (Real.pi * hermForm H₀ (e z) k + Real.pi / 2 * hermForm H₀ k k) *
        r (z + ((fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))) =
      Complex.exp (2 * Real.pi * Complex.I * (a ⬝ᵥ (fun i => (m i : ℂ)) - b ⬝ᵥ (fun i => (n i : ℂ)) -
        ((fun i => (n i : ℂ)) ⬝ᵥ τ.mulVec (fun i => (n i : ℂ))) / 2 - (fun i => (n i : ℂ)) ⬝ᵥ z)) * r z := by
    intro m n k hk
    have hec := hed.continuous
    have hrc := hr.continuous
    refine ext_of_ne_zero hθ.1 hθ0 ?_ ?_ fun z hz => ?_
    · unfold hermForm
      fun_prop
    · fun_prop
    · have h1 := hθ.2 m n z
      rw [pow_one] at h1
      set w := (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)) with hw
      have hper : u.ex (z + w) = u.ex z := by
        rw [u.ex_add, (u.ker w).2 ((hΛ w).2 ⟨m, n, hw⟩), _root_.mul_one]
      obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex z).left x.P.isLB
      have hi' : ⊤ ≤ (u.ex (z + w)).left ⁻¹ᵁ x.P.L.U i := by rwa [hper]
      have h2 := hth i z hi
      have h3 := hth i _ hi'
      rw [hper, h2, h1] at h3
      have h4 := hu₀.2.2.2 k i (e z) (by rw [he, hF]; exact hi)
      rw [hk, ← map_add (f := _), he, he (z + w), hrf i z hi, hrf i _ hi', ← he, ← hk] at h4
      refine mul_right_cancel₀ (mul_ne_zero hz (u.fr_ne i _ hi')) ?_
      unfold hermForm
      linear_combination r z * h3 - thetaChar τ a b z * h4
  refine transfer (powSecEquiv x.P.L l) G (fun f => ?_) (fun s f => ?_) (hsec l)
  on_goal 1 => refine ⟨fun hf => ⟨?_, fun k w => ?_⟩, fun hf => ⟨?_, fun m n z => ?_⟩⟩
  on_goal 5 => refine ⟨fun hf j w hj => ?_, fun hf i z hi => ?_⟩
  · rw [← G.symm_apply_apply f]
    exact (hf.1.comp hed').mul (((hr.comp hed').pow l).inv fun w => pow_ne_zero _ (hr0 _))
  · obtain ⟨z, rfl⟩ := e.surjective w
    obtain ⟨m, n, hmn⟩ := (hΛ (e.symm k)).1 ((UnifCompare.mem_iff u u₀ F hF _).1 (by
      rw [← he, e.apply_symm_apply]; exact k.2))
    have hk := e.symm_apply_eq.1 hmn
    have h1 := hf.2 m n z
    rw [hG, hG, map_add (f := _), ← hk, mul_comm (f (e z)), ← _root_.mul_assoc, ← mul_pow, ← key m n k hk z, mul_pow] at h1
    refine mul_right_cancel₀ (pow_ne_zero l (hr0 _)) (h1.trans ?_)
    ring
  · exact (hf.1.comp hed).mul (hr.pow l)
  · have hk := (UnifCompare.mem_iff u u₀ F hF _).2 ((hΛ _).2 ⟨m, n, rfl⟩)
    have h1 := hf.2 ⟨e _, hk⟩ (e z)
    rw [hG, hG, map_add (f := _), mul_comm (f (e z)), ← _root_.mul_assoc, ← mul_pow, ← key m n ⟨e _, hk⟩ rfl z, mul_pow, h1]
    ring
  · obtain ⟨z, rfl⟩ := e.surjective w
    rw [he] at hj ⊢
    rw [hF] at hj ⊢
    have hi := top_le_preimage_mono _ (powChart_le _ _ j) hj
    rw [← valAt'_powSecEquiv _ _ s _ j hi, hrf _ z hi, mul_pow, ← _root_.mul_assoc]
    exact hf _ z hi
  · have h1 := hf (fun _ => i) (F z) (by rw [hF]; exact top_le_preimage_mono _ (le_powChart _ _ fun _ => i) hi)
    rw [hF, hrf i z hi, mul_pow, ← _root_.mul_assoc] at h1
    exact (valAt'_powSecEquiv _ _ s _ (fun _ => i) hi).trans h1

end GlobalTheory.LevelDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalAtIffWit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KeyKa

theorem normalAt_iff_wit : ∀ (g : ℕ) (x : KeyIn ℂ) (h : x.P.g = g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin g → ℂ), NormalAt x τ 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) 1 ↔ ∃ u : HolUnif x.P.A x.P.L g, Wit x h u (τ.submatrix (Fin.cast h.symm) (Fin.cast h.symm)) a b := by
  intro g x h τ a b
  subst h
  exact normalAt_one_iff ..

end GlobalTheory.KeyKa
end
end

