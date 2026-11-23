module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0905
public import GroundTheory.Brauer.BaseChangeCSA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyIdeleMapInfIdeleNegOne
section
open NumberField IsDedekindDomain

noncomputable section

open Formalism.L2.Host GlobalTheory.UnitaryBC GlobalTheory.CuspRep ReciprocityTheory.Neutral.Bridge.HCFR

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in
theorem continuous_infAdeleMap (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap K L) :=
  continuous_fst.comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap K L).comp
    (Continuous.prodMk_left (0 : FiniteAdeleRing (𝓞 K) K)))

omit [IsCMField E] in
theorem continuous_finAdeleMap (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap K L) :=
  continuous_snd.comp ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap K L).comp
    (Continuous.prodMk_right (0 : InfiniteAdeleRing K)))

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open Classical in
theorem pInf_ideleMap_infIdele (v : InfinitePlace (maximalRealSubfield E)) (w : InfinitePlace E) :
    pInf E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1)) : Ad E) w =
      if w.comap (algebraMap (maximalRealSubfield E) E) = v then -1 else 1 := by
  show (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w))
    (AbsoluteValue.Completion.map (w.comap (algebraMap (maximalRealSubfield E) E)).1 w.1
      (Pi.mulSingle v ((-1 : (v.Completion)ˣ) : v.Completion) (w.comap (algebraMap (maximalRealSubfield E) E)))) = _
  split_ifs with h
  · subst h
    rw [Pi.mulSingle_eq_same]
    simp
  · rw [Pi.mulSingle_eq_of_ne h]
    simp

theorem pFin_ideleMap_infIdele (v : InfinitePlace (maximalRealSubfield E)) :
    pFin E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1)) : Ad E) = 1 :=
  map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap (maximalRealSubfield E) E)

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open Classical in
def iAt (v : InfinitePlace (maximalRealSubfield E)) : (Cinf E)ˣ where
  val w := if w.comap (algebraMap (maximalRealSubfield E) E) = v then Complex.I else 1
  inv w := if w.comap (algebraMap (maximalRealSubfield E) E) = v then -Complex.I else 1
  val_inv := by
    funext w
    simp only [Pi.mul_apply, Pi.one_apply]
    split_ifs <;> simp
  inv_val := by
    funext w
    simp only [Pi.mul_apply, Pi.one_apply]
    split_ifs <;> simp

theorem apply_ideleMap_infIdele_neg_one (χ : HChar E)
    (hc : ∀ x : (AdeleRing (𝓞 E) E)ˣ, χ.1 (Units.map (conjAd E).toMonoidHom x) = χ.1 x)
    (v : InfinitePlace (maximalRealSubfield E)) :
    χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))) = 1 := by
  classical
  have h1 : pInf E (infId E (iAt v)).val = (iAt v).val := by
    change (infEq E).symm (1 - infEq E 1 + infEq E (iAt v).val) = _
    simp
  have h2 : pFin E (infId E (iAt v)).val = 1 := by
    change (1 : Af E) - 0 + 0 = 1
    simp
  have key : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1)) =
      infId E (iAt v) * (Units.map (conjAd E).toMonoidHom (infId E (iAt v)))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    refine Units.ext (ad_ext ?_ ?_)
    · funext w
      change pInf E ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))).val *
        conjAd E (infId E (iAt v)).val) w = pInf E (infId E (iAt v)).val w
      rw [map_mul, Pi.mul_apply, GlobalTheory.ThetaPull.pInf_conjAd, h1, pInf_ideleMap_infIdele]
      change _ * starRingEnd ℂ ((iAt v).val w) = (iAt v).val w
      simp only [iAt]
      split_ifs <;> simp
    · change pFin E ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (infIdele _ v (-1))).val *
        conjAd E (infId E (iAt v)).val) = pFin E (infId E (iAt v)).val
      rw [map_mul, GlobalTheory.ThetaPull.pFin_conjAd, h2,
        pFin_ideleMap_infIdele, map_one, one_mul]
  rw [key, map_mul, map_inv, hc, mul_inv_cancel]

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem apply_conjAd_of_isAbsPow {χ : HChar E} {u : ℝ} (h : χ.IsAbsPow u) (x : (AdeleRing (𝓞 E) E)ˣ) :
    χ.1 (Units.map (conjAd E).toMonoidHom x) = χ.1 x := by
  have e : χ * GlobalTheory.ThetaPull.thetaChar χ = 1 := GlobalTheory.HeckeUnrTrivial.eq_one_of_val_eq_one _ fun v _ => by
    have h2 := (GlobalTheory.ThetaPull.isAbsPow_thetaChar h).2.1 v
    have h0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 fun h0 => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    refine Units.ext ?_
    rw [HChar.val_mul, Units.val_mul, h.2.1 v, h2, Units.val_one, ← Complex.cpow_add _ _ h0]
    simp
  have h3 := congrArg (fun c : HChar E => c.1 x) e
  change χ.1 x * (χ.1 (Units.map (conjAd E).toMonoidHom x))⁻¹ = 1 at h3
  exact (mul_inv_eq_one.1 h3).symm

theorem adeleMap_conj_eq (x : AdeleRing (𝓞 E) E) :
    @GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap E E _ _ _ _
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra x = conjAd E x := by
  letI : Algebra E E := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_infiniteAdeleRing_of_numberField_field E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField E
  have key : ∀ k : E, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap E E (algebraMap E (AdeleRing (𝓞 E) E) k) =
      conjAd E (algebraMap E (AdeleRing (𝓞 E) E) k) := by
    intro k
    rw [conjAd_algebraMap]
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap E E k
  have hsymm : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  refine Prod.ext ?_ ?_
  · exact congrFun ((InfiniteAdeleRing.denseRange_algebraMap E).equalizer (continuous_infAdeleMap E E)
      ((continuous_infEq E).comp (continuous_star.comp hsymm))
      (funext fun k => congrArg Prod.fst (key k))) x.1
  · exact congrFun ((GlobalTheory.AdeleCharTwist.denseRange_fin (F := E)).equalizer
      (continuous_finAdeleMap E E) (continuous_conjFin _)
      (funext fun k => congrArg Prod.snd (key k))) x.2

theorem ideleConj_eq (x : (AdeleRing (𝓞 E) E)ˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E x = Units.map (conjAd E).toMonoidHom x :=
  Units.ext (adeleMap_conj_eq x.val)

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def resReal (χ : HChar E) : HChar (maximalRealSubfield E) :=
  ⟨χ.1.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E),
    χ.2.1.comp (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap _ E), fun k =>
      (congrArg χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele _ E k)).trans (χ.2.2 _)⟩

theorem resReal_apply (χ : HChar E) (x : (AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E))ˣ) :
    (resReal χ).1 x = χ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) := rfl

theorem resReal_locInf_neg_one {χ : HChar E} {u : ℝ} (h : χ.IsAbsPow u) (v : InfinitePlace (maximalRealSubfield E)) :
    (resReal χ).locInf v (-1) = 1 :=
  apply_ideleMap_infIdele_neg_one χ (apply_conjAd_of_isAbsPow h) v

end GlobalTheory.PolChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSphereMeanEqOfFrameNormEq
section
set_option autoImplicit false

noncomputable section

open MvPolynomial NumberField Module GlobalTheory.ChowHt GlobalTheory.CompHt MeasureTheory

namespace GlobalTheory.SphereMeanFrame

set_option autoImplicit false in
open MvPolynomial NumberField Module MeasureTheory in
theorem _root_.GlobalTheory.SphereMeanFrame.eval_linSubst {B N n : ℕ} (M : Matrix (Fin N) (Fin n) ℂ)
    (f : MvPolynomial (Fin B × Fin N) ℂ) (u : Fin B × Fin n → ℂ) :
    eval u (_root_.GlobalTheory.ChowHt.linSubst M f) =
      eval (fun p : Fin B × Fin N => ∑ k, M p.2 k * u (p.1, k)) f := by
  unfold _root_.GlobalTheory.ChowHt.linSubst
  rw [_root_.ReciprocityTheory.MultiplicativeHeights.eval_aeval_alt]
  simp


set_option autoImplicit false in
open MvPolynomial NumberField Module MeasureTheory in
theorem _root_.GlobalTheory.SphereMeanFrame.blockSphereMean_linSubst {B N : ℕ} (Q : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ)
    (hQ : ∀ x : EuclideanSpace ℂ (Fin (N + 1)), ‖Matrix.toEuclideanLin Q x‖ = ‖x‖)
    (f : MvPolynomial (Fin B × Fin (N + 1)) ℂ) :
    _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B (N + 1) (_root_.GlobalTheory.ChowHt.linSubst Q f) = _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B (N + 1) f := by
  let T : EuclideanSpace ℂ (Fin (N + 1)) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (N + 1)) :=
    { toLinearMap := Matrix.toEuclideanLin Q, norm_map' := hQ }
  let U := T.toLinearIsometryEquiv rfl
  let V : EuclideanSpace ℂ (Fin (N + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin (N + 1)) :=
    { toLinearEquiv := U.toLinearEquiv.restrictScalars ℝ, norm_map' := U.norm_map }
  set μ : Measure (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) := Measure.pi fun _ => _root_.ReciprocityTheory.MultiplicativeHeights.sphereProb (N + 1) with hμ
  set Φ : (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) → (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) :=
    fun z b => _root_.ReciprocityTheory.MultiplicativeHeights.sphereMap V (z b) with hΦdef
  have hΦ : MeasurePreserving Φ μ μ := measurePreserving_pi _ _ (fun _ => _root_.ReciprocityTheory.MultiplicativeHeights.measurePreserving_sphereMap V)
  set g : (Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1)) → ℝ := fun z => Real.log ‖eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) f‖ with hg
  have hcont : Continuous (fun z : Fin B → _root_.ReciprocityTheory.MultiplicativeHeights.UnitSphereC (N + 1) => _root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) := by
    unfold _root_.ReciprocityTheory.MultiplicativeHeights.blockPoint
    exact continuous_pi fun p => (continuous_apply p.2).comp
      ((_root_.ReciprocityTheory.MultiplicativeHeights.continuous_spherePoint (N + 1)).comp (continuous_apply p.1))
  have hgm : Measurable g :=
    Real.measurable_log.comp (((MvPolynomial.continuous_eval f).comp hcont).norm.measurable)
  have hpt : ∀ z, eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) (_root_.GlobalTheory.ChowHt.linSubst Q f) = eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint (Φ z)) f := by
    intro z
    rw [_root_.GlobalTheory.SphereMeanFrame.eval_linSubst]
    congr 1
  change ∫ z, Real.log ‖eval (_root_.ReciprocityTheory.MultiplicativeHeights.blockPoint z) (_root_.GlobalTheory.ChowHt.linSubst Q f)‖ ∂μ = ∫ z, g z ∂μ
  simp_rw [hpt]
  change ∫ z, g (Φ z) ∂μ = ∫ z, g z ∂μ
  rw [← integral_map hΦ.measurable.aemeasurable hgm.aestronglyMeasurable, hΦ.map_eq]


set_option autoImplicit false in
open MvPolynomial NumberField Module MeasureTheory in
theorem _root_.GlobalTheory.SphereMeanFrame.blockSphereMean_eq_of_frameNorm_eq : ∀ (B N : ℕ) (A A' : Matrix (Fin N) (Fin N) ℂ),
    A.det ≠ 0 → A'.det ≠ 0 → (∀ z, _root_.GlobalTheory.ChowHt.frameNorm A z = _root_.GlobalTheory.ChowHt.frameNorm A' z) →
    ∀ f : MvPolynomial (Fin B × Fin N) ℂ,
      _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst A f) = _root_.ReciprocityTheory.MultiplicativeHeights.blockSphereMean B N (_root_.GlobalTheory.ChowHt.linSubst A' f) := by
  intro B N A A' hA hA' hn f
  cases N with
  | zero =>
    have hAA : A = A' := Subsingleton.elim _ _
    rw [hAA]
  | succ N =>
    have hAu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
    have hA'u : IsUnit A'.det := isUnit_iff_ne_zero.mpr hA'
    have hAQ : A * (A⁻¹ * A') = A' := by
      rw [← mul_assoc, Matrix.mul_nonsing_inv _ hAu, one_mul]
    have key : _root_.GlobalTheory.ChowHt.linSubst A' f =
        _root_.GlobalTheory.ChowHt.linSubst (A⁻¹ * A') (_root_.GlobalTheory.ChowHt.linSubst A f) := by
      rw [_root_.GlobalTheory.HeightUnique.linSubst_linSubst, hAQ]
    rw [key, _root_.GlobalTheory.SphereMeanFrame.blockSphereMean_linSubst (A⁻¹ * A')]
    intro x
    have h1 := hn (A'.mulVec x.ofLp)
    simp only [_root_.GlobalTheory.ChowHt.frameNorm, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA'u,
      Matrix.one_mulVec] at h1
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    convert h1 using 4 with i
    rfl

end GlobalTheory.SphereMeanFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedAutomorphicHasRepresentative
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.RepresentativeL2

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  {Γ : Subgroup G} [Countable Γ] {μ : Measure G} {𝓕 : Set G}

theorem meas_mk : Measurable (Quotient.mk (QuotientGroup.rightRel Γ)) := measurable_quotient_mk''

theorem ae_up [μ.IsMulLeftInvariant] (h : IsFundamentalDomain Γ 𝓕 μ) {p : Quotient (QuotientGroup.rightRel Γ) → Prop}
    (hp : ∀ᵐ q ∂((μ.restrict 𝓕).map (Quotient.mk (QuotientGroup.rightRel Γ))), p q) :
    ∀ᵐ x ∂μ, p (Quotient.mk _ x) := by
  have h1 := ae_of_ae_map (meas_mk (Γ := Γ)).aemeasurable hp
  rw [ae_iff, Measure.restrict_apply₀' h.nullMeasurableSet] at h1
  rw [ae_iff]
  refine h.measure_zero_of_invariant _ (fun g => ?_) h1
  ext x
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  have : (Quotient.mk (QuotientGroup.rightRel Γ) (g⁻¹ • x)) = Quotient.mk _ x := by
    refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
    simp [Subgroup.smul_def]
  simp only [Set.mem_setOf_eq, this]

end General

theorem repr_properties : ∀ (D : D7) (V : HSp D), ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → (∀ φ : GA D V → ℂ, Continuous φ → (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → ∃ F, Repr V μ 𝓕 F φ) ∧ (∀ F ψ ψ', Continuous ψ → Continuous ψ' → Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F ψ' → ψ = ψ') ∧ (∀ F F' ψ, Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ → F = F') ∧ (∀ F ψ g, Repr V μ 𝓕 F ψ → Repr V μ 𝓕 (ρ g F) (rTr V g ψ)) ∧ (∀ F F' ψ ψ' (a : ℂ), Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ' → Repr V μ 𝓕 (a • F + F') (a • ψ + ψ')) ∧ ∀ F F' ψ ψ', Repr V μ 𝓕 F ψ → Repr V μ 𝓕 F' ψ' → IntegrableOn (fun x => star (ψ x) * ψ' x) 𝓕 μ ∧ ⟪F, F'⟫_ℂ = ∫ x in 𝓕, star (ψ x) * ψ' x ∂μ := by
  intro D V μ 𝓕 ρ hp hr
  obtain ⟨-, -, -, hB, hT, -, hC⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hp.haar
  haveI := hp.right
  have hm : Measurable (autMk V) := meas_mk
  haveI : IsFiniteMeasure (nuQ V μ 𝓕) := ⟨by
    rw [nuQ, Measure.map_apply hm MeasurableSet.univ]
    simpa [lt_top_iff_ne_top] using hp.fin⟩
  have up : ∀ {p : AutQ V → Prop}, (∀ᵐ q ∂(nuQ V μ 𝓕), p q) → ∀ᵐ x ∂μ, p (autMk V x) := fun h => ae_up hp.fd h
  refine ⟨fun φ hφ hinv ⟨C, hC⟩ => ?_, fun F ψ ψ' h h' e e' => ?_, fun F F' ψ e e' => ?_, fun F ψ g e => ?_,
    fun F F' ψ ψ' a e e' => ?_, fun F F' ψ ψ' e e' => ?_⟩
  · let f : AutQ V → ℂ := Quotient.lift φ fun a b hab => by
      have := hinv _ (QuotientGroup.rightRel_apply.1 hab) a
      rw [inv_mul_cancel_right] at this
      exact this.symm
    have hf : Measurable f := measurable_from_quotient.2 hφ.measurable
    have hL : MemLp f 2 (nuQ V μ 𝓕) :=
      MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall fun q => by
        induction q using Quotient.inductionOn with
        | h x => exact hC x)
    exact ⟨hL.toLp f, up hL.coeFn_toLp⟩
  · refine (h.ae_eq_iff_eq μ h').1 ?_
    filter_upwards [e, e'] with x h1 h2
    rw [← h1, h2]
  · refine Lp.ext ?_
    refine (ae_map_iff hm.aemeasurable
      ((Lp.stronglyMeasurable F).measurableSet_eq_fun (Lp.stronglyMeasurable F'))).2 (ae_restrict_of_ae ?_)
    filter_upwards [e, e'] with x h1 h2
    rw [h1, h2]
  · have e2 := (measurePreserving_mul_right μ g).quasiMeasurePreserving.ae e
    filter_upwards [hr.val g F, e2] with x h1 h2
    rw [h1, h2]; rfl
  · filter_upwards [up (Lp.coeFn_add (a • F) F'), up (Lp.coeFn_smul a F), e, e'] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4]; rfl
  · have hI : Integrable (fun q => ⟪F q, F' q⟫_ℂ) (nuQ V μ 𝓕) := L2.integrable_inner F F'
    have hae : (fun x => ⟪F (autMk V x), F' (autMk V x)⟫_ℂ) =ᵐ[μ.restrict 𝓕] fun x => star (ψ x) * ψ' x := by
      refine ae_restrict_of_ae ?_
      filter_upwards [e, e'] with x h1 h2
      rw [h1, h2]
      simp [mul_comm]
    refine ⟨((integrable_map_measure hI.aestronglyMeasurable hm.aemeasurable).1 hI).congr hae, ?_⟩
    rw [L2.inner_def, ← integral_congr_ae hae]
    exact integral_map hm.aemeasurable hI.aestronglyMeasurable

end GlobalTheory.HolDict.RepresentativeL2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BtOrderIsHopfOrderNoetherian
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.PolyArch

theorem roots_eig_any (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (γ : G.C) (w : ℂ)
    (hw : (minpoly G.F γ).eval₂ v.embedding w = 0) : ∃ x : Fin G.n → ℂ, x ≠ 0 ∧ G.psi v γ *ᵥ x = w • x := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hτ : algebraMap G.F ℂ = v.embedding := rfl
  let ψF : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ :=
    { G.psi v with
      commutes' := fun x => by
        show G.psi v (algebraMap G.F G.C x) = _
        rw [G.psi_F, Matrix.algebraMap_eq_diagonal]
        rfl }
  let Ψ : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) ψF (fun a _ => Algebra.commute_algebraMap_left a _)
  haveI : Nontrivial (Matrix (Fin G.n) (Fin G.n) ℂ) := by
    haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
    infer_instance
  have hinj : Function.Injective Ψ := RingHom.injective (Ψ : ℂ ⊗[G.F] G.C →+* Matrix (Fin G.n) (Fin G.n) ℂ)
  set Γ := G.psi v γ with hΓ
  have hΨ : ∀ k : ℕ, Ψ (1 ⊗ₜ (γ ^ k)) = Γ ^ k := by
    intro k
    calc Ψ (1 ⊗ₜ (γ ^ k)) = Algebra.ofId ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) 1 * ψF (γ ^ k) :=
          Algebra.TensorProduct.lift_tmul _ _ _ _ _
      _ = Γ ^ k := by rw [map_one, one_mul, map_pow]; rfl
  have hli0 := Module.Flat.linearIndependent_one_tmul (S := ℂ) (linearIndependent_pow (K := G.F) γ)
  have hli := hli0.map' Ψ.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
  have hli' : LinearIndependent ℂ (fun i : Fin (minpoly G.F γ).natDegree => Γ ^ (i : ℕ)) := by
    have e : (⇑Ψ.toLinearMap ∘ fun i : Fin (minpoly G.F γ).natDegree => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) =
        fun i : Fin (minpoly G.F γ).natDegree => Γ ^ (i : ℕ) := by
      funext i
      exact hΨ i
    rw [e] at hli
    exact hli
  have hint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hd0 : 0 < (minpoly G.F γ).natDegree := minpoly.natDegree_pos hint
  have hpm : (minpoly G.F γ).Monic := minpoly.monic hint
  set Q := (minpoly G.F γ).map (algebraMap G.F ℂ) with hQ
  have hQm : Q.Monic := hpm.map _
  have hQdeg : Q.natDegree = (minpoly G.F γ).natDegree := by rw [hQ, hpm.natDegree_map]
  have hQΓ : Polynomial.aeval Γ Q = 0 := by
    rw [hQ, Polynomial.aeval_map_algebraMap]
    have h : Polynomial.aeval (ψF γ) (minpoly G.F γ) = 0 := by
      rw [Polynomial.aeval_algHom_apply]
      simp [minpoly.aeval]
    exact h
  have hroot : Q.IsRoot w := by
    rw [Polynomial.IsRoot, hQ, Polynomial.eval_map]; exact hw
  by_contra hne
  push_neg at hne
  have hdet : (Γ - algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ) w).det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hne x hx0
    rw [Matrix.sub_mulVec, sub_eq_zero] at hx
    rw [hx, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]
  set R := Q /ₘ (Polynomial.X - Polynomial.C w) with hRdef
  have hQR : (Polynomial.X - Polynomial.C w) * R = Q := Polynomial.mul_divByMonic_eq_iff_isRoot.2 hroot
  have hRΓ : Polynomial.aeval Γ R = 0 := by
    have h1 := hQΓ
    rw [← hQR, map_mul] at h1
    have hu : IsUnit (Polynomial.aeval Γ (Polynomial.X - Polynomial.C w)) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Matrix.isUnit_iff_isUnit_det]
      exact isUnit_iff_ne_zero.2 hdet
    exact (hu.mul_right_eq_zero).1 h1
  have hRd : R.natDegree = (minpoly G.F γ).natDegree - 1 := by
    rw [hRdef, Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C w), hQdeg, Polynomial.natDegree_X_sub_C]
  have hR0 : R ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQR
    exact hQm.ne_zero hQR.symm
  have hsum : ∑ i : Fin (minpoly G.F γ).natDegree, R.coeff i • Γ ^ (i : ℕ) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => R.coeff i • Γ ^ i), ← hRΓ, Polynomial.aeval_eq_sum_range, hRd,
      Nat.sub_add_cancel hd0]
  have hc := Fintype.linearIndependent_iff.1 hli' (fun i => R.coeff i) hsum
    ⟨(minpoly G.F γ).natDegree - 1, by omega⟩
  exact hR0 (Polynomial.leadingCoeff_eq_zero.1 (by rw [Polynomial.leadingCoeff, hRd]; exact hc))

end GlobalTheory.LKCx.PolyArch

namespace GlobalTheory.LKCx

end GlobalTheory.LKCx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfMonicAevalPowersLinearIndependent
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory

theorem charpoly_eq_of_monic_aeval_linearIndependent :
    ∀ (K : Type) [CommRing K] (n : ℕ) (X : Matrix (Fin n) (Fin n) K) (P : Polynomial K),
      P.Monic → P.natDegree = n → Polynomial.aeval X P = 0 →
      LinearIndependent K (fun i : Fin n => X ^ (i : ℕ)) → X.charpoly = P := by
  intro K _ n X P hP hdeg hX hli
  rcases subsingleton_or_nontrivial K with hK | hK
  · exact Subsingleton.elim _ _
  have hc : X.charpoly.Monic := Matrix.charpoly_monic X
  have hcd : X.charpoly.natDegree = n := by
    simpa using Matrix.charpoly_natDegree_eq_dim X
  have hcdeg : X.charpoly.degree = n := by
    rw [Polynomial.degree_eq_natDegree hc.ne_zero, hcd]
  have hPdeg : P.degree = n := by
    rw [Polynomial.degree_eq_natDegree hP.ne_zero, hdeg]
  have hDdeg : (X.charpoly - P).degree < n := by
    have h := Polynomial.degree_sub_lt (p := X.charpoly) (q := P)
      (by rw [hcdeg, hPdeg]) hc.ne_zero (by rw [hc.leadingCoeff, hP.leadingCoeff])
    rwa [hcdeg] at h
  have hDaeval : Polynomial.aeval X (X.charpoly - P) = 0 := by
    rw [map_sub, Matrix.aeval_self_charpoly, hX, sub_zero]
  rw [← sub_eq_zero]
  by_contra hD0
  have hnat : (X.charpoly - P).natDegree < n :=
    (Polynomial.natDegree_lt_iff_degree_lt hD0).mpr hDdeg
  have hsum : ∑ i : Fin n, (X.charpoly - P).coeff (i : ℕ) • X ^ (i : ℕ) = 0 := by
    have h := Polynomial.aeval_eq_sum_range' hnat X
    rw [hDaeval, Finset.sum_range (fun i => (X.charpoly - P).coeff i • X ^ i)] at h
    exact h.symm
  have hcoeff := Fintype.linearIndependent_iff.mp hli
    (fun i : Fin n => (X.charpoly - P).coeff (i : ℕ)) hsum
  apply hD0
  ext k
  rw [Polynomial.coeff_zero]
  by_cases hk : k < n
  · exact hcoeff ⟨k, hk⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hnat (not_lt.mp hk))

end GlobalTheory
end

