module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveClosedPointIsCentreOfPlace
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem centre_place : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
    ∀ c : C, c ≠ x (IsLocalRing.closedPoint K) → ∃ (v : Place k K) (b : Sp v.O ⟶ C), spMap v.O.subtype ≫ b = x ∧ b (IsLocalRing.closedPoint v.O) = c := by
  intro k K _ _ _ _ _ C _ x hx c hc
  obtain ⟨hC, hg, hstr⟩ := hx
  haveI : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hC.1 hC.2.2
  haveI := hC.1
  haveI : Smooth (strHom k (X := C)) := SmoothOfRelativeDimension.smooth 1 _
  haveI : GlobalTheory.IsNormalScheme C := isNormalScheme_of_smooth (strHom k C)
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  haveI := hg.2
  set p : Sp K := IsLocalRing.closedPoint K with hp
  have hη : x p = genericPoint C := by
    have hd : Dense (Set.range x) := hg.1.denseRange
    have hr : Set.range x = {x p} := by
      ext y
      exact ⟨by rintro ⟨q, rfl⟩; rw [Subsingleton.elim q p]; rfl, by rintro rfl; exact ⟨p, rfl⟩⟩
    rw [hr] at hd
    exact (IsGenericPoint.eq (isGenericPoint_def.2 hd.closure_eq) (genericPoint_spec C))
  have hco : Order.coheight c = 1 := by
    have hne : Order.coheight c ≠ 0 := by
      intro h0
      have hm : IsMax c := Order.coheight_eq_zero.1 h0
      have h3 : genericPoint C ⤳ c := genericPoint_specializes c
      apply hc
      rw [hη]
      exact ((show c ⤳ genericPoint C from hm (show c ≤ genericPoint C from h3)).antisymm h3).eq
    have hle : (Order.coheight c : WithBot ℕ∞) ≤ 1 := by
      haveI : Nonempty C := ⟨c⟩
      have hd := GlobalTheory.LieSemineg.dim_curve (k := k) (C := C) hC.1
      have h1 := (Order.coheight_le_krullDim c).trans (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C))).ge
      rw [topologicalKrullDim] at hd
      rw [hd] at h1
      exact h1
    have hle' : Order.coheight c ≤ 1 := by exact_mod_cast hle
    exact le_antisymm hle' (ENat.one_le_iff_ne_zero.2 hne)
  haveI hdvr := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hco

  set A := C.presheaf.stalk c
  let P : IsDedekindDomain.HeightOneSpectrum A := IsDiscreteValuationRing.maximalIdeal A
  let ic := C.presheaf.stalkCongr (Inseparable.of_eq hη.symm)
  let ψ : C.functionField →+* K := (ic.hom ≫ Scheme.stalkClosedPointTo x).hom
  have hψ : Function.Bijective ψ := by
    refine ⟨RingHom.injective ψ, ?_⟩
    have h1 : Function.Surjective ic.hom.hom :=
      ((ConcreteCategory.isIso_iff_bijective ic.hom).1 inferInstance).2
    have h2 : Function.Surjective (Scheme.stalkClosedPointTo x).hom := by
      have h3 := x.stalkMap_surjective p
      have h4 : Function.Surjective (stalkClosedPointIso (CommRingCat.of K)).hom.hom :=
        ((ConcreteCategory.isIso_iff_bijective (stalkClosedPointIso (CommRingCat.of K)).hom).1 inferInstance).2
      exact h4.comp h3
    exact h2.comp h1
  let e : C.functionField ≃+* K := RingEquiv.ofBijective ψ hψ
  let φ : A →+* K := ψ.comp (algebraMap A C.functionField)
  have hφ : spMap φ ≫ C.fromSpecStalk c = x := by
    have h1 : φ = (C.presheaf.stalkSpecializes (hη ▸ genericPoint_specializes c : x p ⤳ c) ≫ Scheme.stalkClosedPointTo x).hom := by
      show ψ.comp (C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes trivial)).hom = _
      change (C.presheaf.stalkSpecializes _ ≫ ic.hom ≫ Scheme.stalkClosedPointTo x).hom = _
      rw [TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
      erw [TopCat.Presheaf.stalkSpecializes_comp]
    rw [h1]
    change Spec.map (CommRingCat.ofHom _) ≫ _ = x
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk x
  have hval : ∀ a : A, (P.valuation C.functionField) (e.symm (φ a)) = P.intValuation a := by
    intro a
    have : e.symm (φ a) = algebraMap A C.functionField a := e.symm_apply_apply _
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap P a

  have hk : ∀ t : k, algebraMap k K t = φ (C.presheaf.germ ⊤ c trivial (algebraMap k Γ(C, ⊤) t)) := by
    have h1 : x ≫ strHom k C = spMap ((φ.comp (C.presheaf.germ ⊤ c trivial).hom).comp (algebraMap k Γ(C, ⊤))) := by
      rw [← hφ, Category.assoc, strHom, ← Category.assoc (C.fromSpecStalk c), Scheme.fromSpecStalk_toSpecΓ]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
    have h2 := Spec.map_injective (hstr.symm.trans h1)
    intro t
    exact congrArg (fun f => f.hom t) h2
  let vK : Valuation K (WithZero (Multiplicative ℤ)) := (P.valuation C.functionField).comap e.symm.toRingHom
  have hvφ : ∀ a, vK (φ a) = P.intValuation a := fun a => hval a
  have hunit : ∀ a : A, IsUnit a → P.intValuation a = 1 := by
    intro a ha
    refine le_antisymm (P.intValuation_le_one a) (not_lt.1 fun h => ?_)
    exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ((P.intValuation_lt_one_iff_mem a).1 h) ha)
  let v : Place k K := ⟨vK, fun g => by
      obtain ⟨y, hy⟩ := P.valuation_surjective C.functionField g
      exact ⟨e y, by
        change P.valuation C.functionField (e.symm (e y)) = g
        rw [e.symm_apply_apply]; exact hy⟩,
    fun t ht => by
      rw [hk, hvφ]
      exact hunit _ (((Ne.isUnit ht).map (algebraMap k Γ(C, ⊤))).map _)⟩
  have hle : ∀ a : A, φ a ∈ v.O := fun a => by
    show vK (φ a) ≤ 1
    rw [hvφ]; exact P.intValuation_le_one a
  let ψO : A →+* v.O := φ.codRestrict v.O hle
  have hPm : P.asIdeal = IsLocalRing.maximalIdeal A := rfl
  haveI : IsLocalHom ψO := ⟨fun a ha => by
    by_contra hna
    have hm : a ∈ P.asIdeal := by rw [hPm]; exact hna
    have hlt : vK (φ a) < 1 := by rw [hvφ]; exact (P.intValuation_lt_one_iff_mem a).2 hm
    obtain ⟨u, hu⟩ := ha
    let w : v.O := ((u⁻¹ : v.Oˣ) : v.O)
    have hinv : vK (w : K) ≤ 1 := w.2
    have h1 : φ a * (w : K) = 1 := by
      have := congrArg (fun z : v.O => (z : K)) u.mul_inv
      have e1 : φ a = ((u : v.O) : K) := by rw [hu]; rfl
      rw [e1]
      exact this
    have h2 := congrArg vK h1
    rw [map_mul, map_one] at h2
    have : vK (φ a) * vK (w : K) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' hinv) hlt
    exact absurd h2 this.ne⟩
  refine ⟨v, spMap ψO ≫ C.fromSpecStalk c, ?_, ?_⟩
  · rw [← Category.assoc, ← hφ]
    congr 1
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  · have : spMap ψO (IsLocalRing.closedPoint v.O) = IsLocalRing.closedPoint A :=
      IsLocalRing.comap_closedPoint ψO
    change C.fromSpecStalk c (spMap ψO (IsLocalRing.closedPoint v.O)) = c
    rw [this, Scheme.fromSpecStalk_closedPoint]

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledCoordsThetaTransformProductEqTensorConj
section
namespace DoublingThetaSums
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.DblTheta

section Gen

variable {R : Type} [CommRing R] [Invertible (2 : R)]

theorem schr_boxFun_elim (ψ : AddChar R ℂ) {κ κ' : Type} [Fintype κ] [Fintype κ'] (x₁ y₁ : κ → R) (x₂ y₂ : κ' → R)
    (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    GlobalTheory.WeilM.schr ψ (Sum.elim x₁ x₂, Sum.elim y₁ y₂) (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
      GlobalTheory.WeilM.boxFun (GlobalTheory.WeilM.schr ψ (x₁, y₁) φ₁) (GlobalTheory.WeilM.schr ψ (x₂, y₂) φ₂) := by
  funext z
  have e₁ : (z + Sum.elim x₁ x₂) ∘ Sum.inl = z ∘ Sum.inl + x₁ := rfl
  have e₂ : (z + Sum.elim x₁ x₂) ∘ Sum.inr = z ∘ Sum.inr + x₂ := rfl
  have e₃ : z ⬝ᵥ Sum.elim y₁ y₂ + ⅟(2 : R) * (Sum.elim x₁ x₂ ⬝ᵥ Sum.elim y₁ y₂) =
      ((z ∘ Sum.inl) ⬝ᵥ y₁ + ⅟(2 : R) * (x₁ ⬝ᵥ y₁)) + ((z ∘ Sum.inr) ⬝ᵥ y₂ + ⅟(2 : R) * (x₂ ⬝ᵥ y₂)) := by
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    ring
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.boxFun, e₁, e₂, e₃]
  rw [AddChar.map_add_eq_mul]
  ring

end Gen

section Sums

variable (F : Type) [Field F] [NumberField F]

theorem thetaSum_boxFun {κ κ' : Type} [Fintype κ] [Fintype κ'] {A : (κ → AdeleRing (𝓞 F) F) → ℂ}
    {B : (κ' → AdeleRing (𝓞 F) F) → ℂ} (hA : A ∈ GlobalTheory.WeilM.schA F κ) (hB : B ∈ GlobalTheory.WeilM.schA F κ') :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.boxFun A B) = GlobalTheory.WeilM.thetaSum F A * GlobalTheory.WeilM.thetaSum F B := by
  unfold GlobalTheory.WeilM.thetaSum
  rw [tsum_mul_tsum_of_summable_norm (GlobalTheory.WeilM.summable_norm_of_mem_schA F hA)
    (GlobalTheory.WeilM.summable_norm_of_mem_schA F hB), ← (Equiv.sumArrowEquivProdArrow κ κ' F).tsum_eq]
  exact tsum_congr fun ξ => rfl

theorem thetaSum_schr_neg [Invertible (2 : AdeleRing (𝓞 F) F)] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hu : ∀ a, ‖ψ a‖ = 1) {κ : Type} [Fintype κ] (x y : κ → AdeleRing (𝓞 F) F)
    (φ : (κ → AdeleRing (𝓞 F) F) → ℂ) :
    GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (x, -y) φ) =
      starRingEnd ℂ (GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr ψ (-x, -y) (fun u => starRingEnd ℂ (φ (-u))))) := by
  have hc : ∀ t, starRingEnd ℂ (ψ t) = ψ (-t) := fun t => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hu t)]
  have key : ∀ ξ : κ → F,
      GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) =
        starRingEnd ℂ (GlobalTheory.WeilM.schr ψ (-x, -y) (fun u => starRingEnd ℂ (φ (-u)))
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) := by
    intro ξ
    have ha : (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) =
        -(fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) := by
      funext i; simp
    rw [ha]
    generalize (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = a
    simp only [GlobalTheory.WeilM.schr, map_mul, Complex.conj_conj, hc]
    have h1 : -a + x = -(a + -x) := by abel
    have h2 : -a ⬝ᵥ -y + ⅟(2 : AdeleRing (𝓞 F) F) * (x ⬝ᵥ -y) =
        -(a ⬝ᵥ -y + ⅟(2 : AdeleRing (𝓞 F) F) * (-x ⬝ᵥ -y)) := by
      simp only [neg_dotProduct, dotProduct_neg]
      ring
    rw [h1, h2]
  unfold GlobalTheory.WeilM.thetaSum
  calc _ = ∑' ξ : κ → F, GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((-ξ) i)) :=
        ((Equiv.neg (κ → F)).tsum_eq
          (fun ξ : κ → F => GlobalTheory.WeilM.schr ψ (x, -y) φ (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)))).symm
    _ = _ := tsum_congr key
    _ = _ := (Complex.conj_tsum _).symm

end Sums

theorem thetaTr_ddr_boxFun : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  intro D ψ hψ S T JA JB ξ κ _ co φ₁ h₁ φ₂ h₂
  funext x
  have he : (GlobalTheory.DblSchr.ddr co).e x =
      (Sum.elim (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL S T x)).1 (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).1,
        Sum.elim (co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resL S T x)).2 (-(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).2)) := rfl
  have hn : co.e (-GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x) =
      (-(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).1, -(co.e (GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.resR S T x)).2) := by
    rw [map_neg]; rfl
  have hs : ∀ (w : (κ → AF D.host.F) × (κ → AF D.host.F)) (φ : (κ → AF D.host.F) → ℂ),
      φ ∈ GlobalTheory.WeilM.schA D.host.F κ → GlobalTheory.WeilM.schr ψ w φ ∈ GlobalTheory.WeilM.schA D.host.F κ :=
    fun w φ hφ => GlobalTheory.SchrSchA.schr_mem_schA_of_isStdChar D ψ hψ κ w φ hφ
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta]
  rw [he, hn, schr_boxFun_elim, thetaSum_boxFun _ (hs _ _ h₁) (hs _ _ h₂),
    thetaSum_schr_neg _ ψ hψ.1.2.1]

end GlobalTheory.CompanionTheory.DblTheta

end

end

end DoublingThetaSums
section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.Adopt.doubledCoordsThetaTransform_product_eq_tensor_conj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
      ∀ φ₁ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ φ₂ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        GlobalTheory.WeilSchrodinger.thetaTr D.host.F (GlobalTheory.DblSchr.ddr co) ψ (GlobalTheory.WeilM.boxFun φ₁ φ₂) =
          GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.delta S T (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  first | exact @DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun | exact DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun | (intros; apply DoublingThetaSums.GlobalTheory.CompanionTheory.DblTheta.thetaTr_ddr_boxFun <;> assumption)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumHeisenbergEigenDoubledLattice
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.DblVacEigen

section Alg

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E)
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]


omit [DecidableEq α] in
theorem hTens_dbl (JA : Matrix α α E) (JB : Matrix β β E) (x₁ x₂ y₁ y₂ : Matrix α β E) :
    hTens c JA (dbl JB) (Matrix.fromCols x₁ x₂) (Matrix.fromCols y₁ y₂) = hTens c JA JB x₁ y₁ - hTens c JA JB x₂ y₂ := by
  simp only [hTens, dbl, Fintype.sum_sum_type, Matrix.fromCols_apply_inl, Matrix.fromCols_apply_inr,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, Matrix.neg_apply, mul_zero, zero_mul, add_zero, zero_add, mul_neg, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib, sub_eq_add_neg, Finset.sum_const_zero]


omit [DecidableEq α] [DecidableEq β] in
theorem hTens_transpose (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix β α E) :
    hTens c JA JB xᵀ yᵀ = hTens c JB JA x y := by
  unfold hTens
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.transpose_apply]
  ring

end Alg

end GlobalTheory.DblVacEigen

namespace GlobalTheory.DblVacEigen

variable {F : Type} [Field F] [NumberField F]

theorem dot_congr_at {κ : Type} [Fintype κ] (v : Pl (F := F)) {y : κ → AF F} (hy : At (evFin F v) y) {z z' : κ → AF F}
    (h : ∀ i, evFin F v (z i) = evFin F v (z' i)) : z ⬝ᵥ y = z' ⬝ᵥ y := by
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := congrFun (hy (z i - z' i) (by rw [map_sub, h i, sub_self])) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e
  rw [sub_mul] at e
  exact sub_eq_zero.mp e

theorem eigen_pointwise {κ : Type} [Fintype κ] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ) {φ : (κ → Fv F v) → ℂ}
    (hφ : φ ∈ SB (κ → Fv F v)) (p : (κ → AF F) × (κ → AF F)) (hp1 : At (evFin F v) p.1) (hp2 : At (evFin F v) p.2)
    (c : ℂ) (h : Acts (evFin F v) (schr ψ p) φ (c • φ)) (z : κ → AF F) :
    ψ (z ⬝ᵥ p.2 + ⅟(2 : AF F) * (p.1 ⬝ᵥ p.2)) * φ (fun i => evFin F v ((z + p.1) i)) =
      c * φ (fun i => evFin F v (z i)) := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have hr := hR φ hφ
  let Δ : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (z i))
  have hΔ : At (evFin F v) Δ := fun u hu => funext fun i => GlobalTheory.LatVac.at_liftV v _ u hu
  have hevΔ : ∀ i, evFin F v (Δ i) = evFin F v (z i) := fun i => GlobalTheory.LatVac.evFin_liftV v _
  have e := congrFun (h R hr) Δ
  have hR2 : R Δ = R 0 := by simpa using hr.1 0 Δ hΔ
  have hR1 : R (Δ + p.1) = R 0 := by rw [hr.1 Δ p.1 hp1, hR2]
  simp only [schr, tens, Pi.smul_apply, smul_eq_mul] at e
  rw [hR1, hR2, dot_congr_at v hp2 hevΔ] at e
  have hev : (fun i => evFin F v ((Δ + p.1) i)) = fun i => evFin F v ((z + p.1) i) := by
    funext i; simp only [Pi.add_apply, map_add (f := _), hevΔ]
  have hev' : (fun i => evFin F v (Δ i)) = fun i => evFin F v (z i) := funext hevΔ
  rw [hev, hev'] at e
  exact mul_right_cancel₀ hR0 (by linear_combination e)

theorem acts_box {κ κ' : Type} [Fintype κ] [Fintype κ'] (v : Pl (F := F)) (ψ : AddChar (AF F) ℂ)
    {φ₁ : (κ → Fv F v) → ℂ} {φ₂ : (κ' → Fv F v) → ℂ} (X₁ Y₁ : κ → AF F)
    (X₂ Y₂ : κ' → AF F) (h11 : At (evFin F v) X₁) (h21 : At (evFin F v) X₂) (c₁ c₂ : ℂ)
    (h₁ : ∀ z, ψ (z ⬝ᵥ Y₁ + ⅟(2 : AF F) * (X₁ ⬝ᵥ Y₁)) * φ₁ (fun i => evFin F v ((z + X₁) i)) =
      c₁ * φ₁ (fun i => evFin F v (z i)))
    (h₂ : ∀ z, ψ (z ⬝ᵥ Y₂ + ⅟(2 : AF F) * (X₂ ⬝ᵥ Y₂)) * φ₂ (fun i => evFin F v ((z + X₂) i)) =
      c₂ * φ₂ (fun i => evFin F v (z i))) :
    Acts (evFin F v) (schr ψ (Sum.elim X₁ X₂, Sum.elim Y₁ Y₂)) (boxFun φ₁ φ₂)
      ((c₁ * c₂) • boxFun φ₁ φ₂) := by
  intro r hr
  have hX : At (evFin F v) (Sum.elim X₁ X₂ : κ ⊕ κ' → AF F) := by
    intro u hu; funext i
    cases i with
    | inl i => exact congrFun (h11 u hu) i
    | inr i => exact congrFun (h21 u hu) i
  funext x
  have hd1 : x ⬝ᵥ Sum.elim Y₁ Y₂ = (x ∘ Sum.inl) ⬝ᵥ Y₁ + (x ∘ Sum.inr) ⬝ᵥ Y₂ := by
    simp [dotProduct, Fintype.sum_sum_type]
  have hd2 : Sum.elim X₁ X₂ ⬝ᵥ Sum.elim Y₁ Y₂ = X₁ ⬝ᵥ Y₁ + X₂ ⬝ᵥ Y₂ :=
    by simp [dotProduct, Fintype.sum_sum_type]
  simp only [schr, tens, Pi.smul_apply, smul_eq_mul]
  rw [hr.1 x _ hX, hd1, hd2,
    show (x ∘ Sum.inl) ⬝ᵥ Y₁ + (x ∘ Sum.inr) ⬝ᵥ Y₂ + ⅟(2 : AF F) * (X₁ ⬝ᵥ Y₁ + X₂ ⬝ᵥ Y₂) =
      ((x ∘ Sum.inl) ⬝ᵥ Y₁ + ⅟(2 : AF F) * (X₁ ⬝ᵥ Y₁)) + ((x ∘ Sum.inr) ⬝ᵥ Y₂ + ⅟(2 : AF F) * (X₂ ⬝ᵥ Y₂))
      by ring, AddChar.map_add_eq_mul]
  have e1 := h₁ (x ∘ Sum.inl)
  have e2 := h₂ (x ∘ Sum.inr)
  simp only [boxFun, Function.comp_def, Pi.add_apply, Sum.elim_inl, Sum.elim_inr] at e1 e2 ⊢
  rw [show ∀ a e b f s : ℂ, a * e * ((b * f) * s) = (a * b) * (e * f) * s from fun _ _ _ _ _ => by ring, e1, e2]
  ring

end GlobalTheory.DblVacEigen

namespace GlobalTheory.DblVacEigen

theorem doubled_vac_eigen : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J)) (Fin a × Fin (a + a'))),
    (∀ x : Matrix (Fin a) (Fin (a + a')) (AE F E), d'.e xᵀ = G.M.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))) ((Fin a × Fin (a + a')) ⊕ (Fin a × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1 : AE F E) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) d' dd →
    ∀ θ : 𝓞 E, (θ : E) + σ θ = 1 →
    (∀ γ ∈ latAtV G.V G.W v, Acts (evFin F v) (G.M.co.rho B.ψ γ) (G.M.vac v)
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) • G.M.vac v)) →
    (∀ w₁ ∈ latAtV G.V G.W v, ∀ w₂ ∈ latAtV G.V G.W v,
      Acts (evFin F v) (dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ)) (boxFun (G.M.vac v) (fun x => star (G.M.vac v x)))
        (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
          (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ)) • (boxFun (G.M.vac v) (fun x => star (G.M.vac v x))))) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w _ _ d' hd' dd hdd θ _ hvac w₁ hw₁ w₂ hw₂
  have hSB := (hT.geo.hM.vac v).1
  have hψ : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hT.base.std
  have hstar : ∀ t, star (B.ψ t) = B.ψ (-t) := by
    intro t
    rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ t]
    simp
  have hAt : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V G.W v).1
  have hco : ∀ γ ∈ latAtV G.V G.W v, At (evFin F v) (G.M.co.e γ).1 ∧ At (evFin F v) (G.M.co.e γ).2 := by
    intro γ hγ
    have e : ∀ u, evFin F v u = 0 → u • G.M.co.e γ = 0 := fun u hu => by
      rw [← map_smul, hAt γ hγ u hu, map_zero]
    exact ⟨fun u hu => congrArg Prod.fst (e u hu), fun u hu => congrArg Prod.snd (e u hu)⟩
  have h1 := eigen_pointwise v B.ψ hSB (G.M.co.e w₁) (hco w₁ hw₁).1 (hco w₁ hw₁).2 _ (hvac w₁ hw₁)
  have h2 := eigen_pointwise v B.ψ hSB (G.M.co.e w₂) (hco w₂ hw₂).1 (hco w₂ hw₂).2 _ (hvac w₂ hw₂)
  have h2' : ∀ z, B.ψ (z ⬝ᵥ (-(G.M.co.e w₂).2) + ⅟(2 : AF F) * ((G.M.co.e w₂).1 ⬝ᵥ (-(G.M.co.e w₂).2))) *
      (fun x => star (G.M.vac v x)) (fun i => evFin F v ((z + (G.M.co.e w₂).1) i)) =
      star (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₂ w₂)) * (fun x => star (G.M.vac v x)) (fun i => evFin F v (z i)) := by
    intro z
    have e := congrArg star (h2 z)
    simp only [star_mul, hstar] at e
    rw [hstar, show z ⬝ᵥ (-(G.M.co.e w₂).2) + ⅟(2 : AF F) * ((G.M.co.e w₂).1 ⬝ᵥ (-(G.M.co.e w₂).2)) =
      -(z ⬝ᵥ (G.M.co.e w₂).2 + ⅟(2 : AF F) * ((G.M.co.e w₂).1 ⬝ᵥ (G.M.co.e w₂).2)) by
        rw [dotProduct_neg, dotProduct_neg]; ring]
    linear_combination e
  have hbox := acts_box v B.ψ (φ₁ := G.M.vac v) (φ₂ := fun x => star (G.M.vac v x)) (G.M.co.e w₁).1 (G.M.co.e w₁).2 (G.M.co.e w₂).1 (-(G.M.co.e w₂).2)
    (hco w₁ hw₁).1 (hco w₂ hw₂).1 _ _ h1 h2'
  have hrho : dd.rho B.ψ (Matrix.fromCols w₁ᵀ w₂ᵀ) = schr B.ψ (Sum.elim (G.M.co.e w₁).1 (G.M.co.e w₂).1,
      Sum.elim (G.M.co.e w₁).2 (-(G.M.co.e w₂).2)) := by
    rw [Darboux.rho, hdd, hd', hd']
  have hS : symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J))
      (Matrix.fromCols w₁ᵀ w₂ᵀ) (Matrix.fromCols w₁ᵀ w₂ᵀ) = symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₁ w₁ - symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₂ w₂ := by
    unfold symp
    rw [hTens_dbl, hTens_transpose, hTens_transpose, mul_sub, map_sub]
  have hc : B.ψ (⅟(2 : AF F) * (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₁ w₁ - symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₂ w₂)) = B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₁ w₁) * star (B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) w₂ w₂)) := by
    rw [hstar, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  rw [hrho, hS, hc]
  exact hbox

end GlobalTheory.DblVacEigen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ R : (κ → AF F) → ℂ, R 0 ≠ 0 ∧ ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ R := by
  first | exact @GlobalTheory.RestWitness.exists_rest | exact GlobalTheory.RestWitness.exists_rest | (intros; apply GlobalTheory.RestWitness.exists_rest <;> assumption)
end

