module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartTiedLevelChain
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedInvMulLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleSteps
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0308
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesCoverExistsIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0440
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0441

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicMatrixCongruenceMoveRationalFrameStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicMatrixCongruence_move_rational_frame : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (κ x k : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (f g : GL (Fin N) E), (∀ r s, IntAtA (F := F) P ((k : Matrix (Fin N) (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) r s)) → (∀ r s, IntAtA (F := F) P (((k⁻¹ : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) : Matrix (Fin N) (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) r s)) → (∀ r s, IntAtA (F := F) P (((k⁻¹ * x * k : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) : Matrix (Fin N) (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) r s)) → (∀ r s, IntAtA (F := F) P ((((k⁻¹ * x * k)⁻¹ : GL (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) : Matrix (Fin N) (Fin N) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) r s)) → GlobalTheory.TwU.CongAt P n (κ⁻¹ * x) → GlobalTheory.TwU.NearAt P n (k⁻¹ * x * k) g → GlobalTheory.TwU.CongAt P n (k⁻¹ * GlobalTheory.TwU.ratA F f) → GlobalTheory.TwU.CongAt P n ((GlobalTheory.TwU.ratA F f)⁻¹ * k) → GlobalTheory.TwU.NearAt P n ((GlobalTheory.TwU.ratA F f)⁻¹ * κ * GlobalTheory.TwU.ratA F f) g := by
  first | exact @GlobalTheory.CongMove.nearAt_conj_ratA | exact GlobalTheory.CongMove.nearAt_conj_ratA | (intros; apply GlobalTheory.CongMove.nearAt_conj_ratA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraicConstantsDescendToNormalIntegralScheme
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConstDescent

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.Cartier

theorem exists_fnOf_eq_of_algebraic {F : Type} [Field F] {X : Scheme.{0}} [IsIntegral X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp F) (U : X.Opens) (hU : genericPoint X ∈ U)
    {a : X.functionField} (ha : ∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (Cartier.constFn p) a = 0) :
    ∃ s : Γ(X, U), fnOf U hU s = a := by
  haveI : Nonempty U := ⟨⟨_, hU⟩⟩
  letI := (algX p U).toAlgebra
  letI : Algebra F X.functionField := (Cartier.constFn p).toAlgebra
  haveI : IsScalarTower F Γ(X, U) X.functionField :=
    IsScalarTower.of_algebraMap_eq' (fnOf_comp_algX p U hU).symm
  obtain ⟨P, hP, hPa⟩ := ha
  have hint : IsIntegral F a := (show IsAlgebraic F a from
    ⟨P, hP, by rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]; exact hPa⟩).isIntegral
  obtain ⟨s, hs⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := Γ(X, U))
    (A := X.functionField)).1 hint.tower_top
  exact ⟨s, hs⟩

theorem appLE_comp_algX {F : Type} [CommRing F] {W V : Scheme.{0}} (pW : W ⟶ Sp F) (π : V ⟶ W) :
    (π.appLE ⊤ ⊤ le_top).hom.comp (algX pW ⊤) = algX (π ≫ pW) ⊤ := by
  have e := Scheme.Hom.appLE_comp_appLE π pW ⊤ ⊤ ⊤ le_top le_top
  exact congrArg (fun f => (CommRingCat.Hom.hom f).comp
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom) e

theorem descent : ∀ (F : Type) [Field F] (W V : Scheme.{0}) [IsIntegral W] [IsIntegral V]
    [GlobalTheory.IsNormalScheme W] (pW : W ⟶ Sp F) (pV : V ⟶ Sp F) (π : V ⟶ W), π ≫ pW = pV →
    (∀ b : V.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pV) b = 0) →
      b ∈ (GlobalTheory.Cartier.constFn pV).range) →
    ∀ a : W.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn pW) a = 0) →
      a ∈ (GlobalTheory.Cartier.constFn pW).range := by
  intro F _ W V _ _ _ pW pV π hπ hV a ha
  subst hπ
  have hW : genericPoint W ∈ (⊤ : W.Opens) := trivial
  have hV' : genericPoint V ∈ (⊤ : V.Opens) := trivial

  let φ : Γ(W, ⊤) →+* V.functionField := (fnOf ⊤ hV').comp (π.appLE ⊤ ⊤ le_top).hom
  have hφ : φ.comp (algX pW ⊤) = Cartier.constFn (π ≫ pW) := by
    simp only [φ, RingHom.comp_assoc, appLE_comp_algX]
    rfl
  obtain ⟨s, hs⟩ := exists_fnOf_eq_of_algebraic pW ⊤ hW ha
  obtain ⟨P, hP, hPa⟩ := ha
  have h0 : P.eval₂ (algX pW ⊤) s = 0 := fnOf_injective ⊤ trivial (by
    rw [Polynomial.hom_eval₂, fnOf_comp_algX pW ⊤ hW, hs, hPa, map_zero])
  have hb : P.eval₂ (Cartier.constFn (π ≫ pW)) (φ s) = 0 := by
    rw [← hφ, ← Polynomial.hom_eval₂, h0, map_zero]
  obtain ⟨c, hc⟩ := hV _ ⟨P, hP, hb⟩
  refine ⟨c, ?_⟩
  by_contra hne
  have hne' : a - Cartier.constFn pW c ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have ht : fnOf ⊤ hW (s - algX pW ⊤ c) = a - Cartier.constFn pW c := by
    rw [map_sub, hs, ← fnOf_comp_algX pW ⊤ hW, RingHom.comp_apply]
  have hφt : φ (s - algX pW ⊤ c) = 0 := by
    rw [map_sub, ← RingHom.comp_apply φ, hφ, hc, sub_self]
  have hinv : ∃ Q : Polynomial F, Q ≠ 0 ∧ Q.eval₂ (Cartier.constFn pW) (a - Cartier.constFn pW c)⁻¹ = 0 := by
    letI : Algebra F W.functionField := (Cartier.constFn pW).toAlgebra
    have h1 : IsAlgebraic F a :=
      ⟨P, hP, by rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra]; exact hPa⟩
    have h2 : IsAlgebraic F (a - Cartier.constFn pW c) :=
      h1.sub (isAlgebraic_algebraMap (A := W.functionField) c)
    obtain ⟨Q, hQ, hQx⟩ := h2.inv
    exact ⟨Q, hQ, by rw [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] at hQx; exact hQx⟩
  obtain ⟨u, hu⟩ := exists_fnOf_eq_of_algebraic pW ⊤ hW hinv
  have htu : (s - algX pW ⊤ c) * u = 1 := fnOf_injective ⊤ trivial (by
    rw [map_mul, ht, hu, map_one, mul_inv_cancel₀ hne'])
  have h3 := congrArg φ htu
  rw [map_mul, hφt, zero_mul, map_one] at h3
  exact zero_ne_one h3

end GlobalTheory.ConstDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesEqUnionThreeParts
section
noncomputable section

namespace GlobalTheory.Mem.R3

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.Col2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : Top.TwDat X.B} {Wt : Set X.B.places.Pl}

def Dat.IwasawaPlaceIndex (z : Dat X I hX T Wt) : Set X.B.places.Pl :=
  {w | ∃ j, ∃ w' ∈ ({X.toD7.plEq w, Formalism.DivisionValues.conjPl (X.toD7.plEq w)} : Set (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))),
    (s0Of z.R z.F).Iw j (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0 w' ≠ 0}

def Dat.W1jw (z : Dat X I hX T Wt) : Set X.B.places.Pl :=
  {w | ∃ j, ∃ w' ∈ ({X.toD7.plEq w, Formalism.DivisionValues.conjPl (X.toD7.plEq w)} : Set (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))),
    Formalism.DivisionValues.jw (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).HT j
              (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) w'
      (((famR X I hX (usedOf I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j
        (famR X I hX (usedOf I T Wt) z.Xg z.tr).A.μ0) ≠ 0}

def placesWithNonzeroContentOrConj (D : D7) (F0 : HeightOneSpectrum (𝓞 D.what₂.LL) → Fin D.R.m → ℝ) : Set D.what₂.places.Pl :=
  {w | ∃ j, ∃ w' ∈ ({D.plEq w, Formalism.DivisionValues.conjPl (D.plEq w)} : Set (HeightOneSpectrum (𝓞 D.what₂.LL))), F0 w' j ≠ 0}

theorem Dat.auxiliaryPlaces_eq_union_three_parts (z : Dat X I hX T Wt) (F0 : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → Fin X.toD7.R.m → ℝ) :
    z.W1 F0 = z.IwasawaPlaceIndex ∪ z.W1jw ∪ placesWithNonzeroContentOrConj X.toD7 F0 := by
  ext w
  simp only [Dat.W1, Dat.IwasawaPlaceIndex, Dat.W1jw, placesWithNonzeroContentOrConj, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨j, w', hw', h | h | h⟩
    · exact Or.inl (Or.inl ⟨j, w', hw', h⟩)
    · exact Or.inl (Or.inr ⟨j, w', hw', h⟩)
    · exact Or.inr ⟨j, w', hw', h⟩
  · rintro ((⟨j, w', hw', h⟩ | ⟨j, w', hw', h⟩) | ⟨j, w', hw', h⟩)
    · exact ⟨j, w', hw', Or.inl h⟩
    · exact ⟨j, w', hw', Or.inr (Or.inl h)⟩
    · exact ⟨j, w', hw', Or.inr (Or.inr h)⟩

theorem Dat.mem_auxiliaryPlaces_iff_three_parts (z : Dat X I hX T Wt) (F0 : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → Fin X.toD7.R.m → ℝ)
    (w : X.B.places.Pl) : w ∈ z.W1 F0 ↔ (w ∈ z.IwasawaPlaceIndex ∨ w ∈ z.W1jw) ∨ w ∈ placesWithNonzeroContentOrConj X.toD7 F0 :=
  Set.ext_iff.mp (z.auxiliaryPlaces_eq_union_three_parts F0) w

end GlobalTheory.Mem.R3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartReadsAtClassGL
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT.FrameMove

open GlobalTheory.Mem.Col2.LevFun GlobalTheory.Mem.Col2.Splice

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inv_mul_ratA_apply {n : ℕ} (g : GL (Fin n) (AfE F E)) (γ : GL (Fin n) E) (r s : Fin n) :
    ((g⁻¹ * GlobalTheory.TwU.ratA F γ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s =
      pullV g (fun t => (γ : Matrix (Fin n) (Fin n) E) t s) r := by
  unfold pullV
  rw [Units.val_mul, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rfl

theorem val_sub_lt_of_liftFr [StarRing E] {hc : CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (w : SG) (r s : Fin n) :
    Valued.v (adAt F w.1 (pullV g (p.deco.1.liftFr w (Pi.single s 1)) r) -
      (1 : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)) r s) < 1 := by
  classical
  have hL := GlobalTheory.TopStep.liftFr_spec p.deco.2 w
  have hs := single_mem_stdAt (E := E) (n := n) w.1 s
  have hx : p.deco.1.liftFr w (Pi.single s 1) ∈ p.deco.1.at w.1 := (hL.1 _).2 hs
  obtain ⟨t, ht, htx⟩ := (mem_locP _ _ _).1 hx
  have h1 := h.be w _ htx r
  rw [p.deco.2.be_smul w t _ hx, hL.2 _ hs, redV_single, adAt_pullV_osmul] at h1
  have h2 : HasRes w.1 (adAt F w.1 (pullV g (p.deco.1.liftFr w (Pi.single s 1)) r))
      (Ideal.Quotient.mk w.1.asIdeal (if r = s then 1 else 0)) := by
    refine hasRes_of_mul ht ?_
    convert h1 using 1
    by_cases e : r = s
    · subst e; simp
    · simp [e]
  have h3 := hasRes_sub_lt h2
  convert h3 using 3
  by_cases e : r = s
  · subst e; simp
  · simp [e, Matrix.one_apply]

theorem val_mul_sub_one_le {P : HeightOneSpectrum (𝓞 E)} {n N : ℕ} {A B : Matrix (Fin n) (Fin n) (P.adicCompletion E)}
    (hA : ∀ r s, Valued.v (A r s - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (hB : ∀ r s, Valued.v (B r s - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)))
    (r s : Fin n) :
    Valued.v ((A * B) r s - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  first
  | exact @_root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le
  | exact _root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le
  | (apply _root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.MulSubOneValuation.mul_sub_one_le ..)

theorem le_exp_neg_one_of_lt_one' {γ : WithZero (Multiplicative ℤ)} (h : γ < 1) : γ ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne γ 0 with h0 | h0
  · rw [h0]; exact zero_le'
  rw [← WithZero.exp_log h0] at h ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem seamGL_apply {D : D7} {Xf : Fields} (sd : Seam D Xf) {n : ℕ} (f : Sp Xf.E n ≃ₗ[Xf.E] Sp Xf.E n) (t s : Fin n) :
    ((GlobalTheory.TwU.seamGL sd f : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) t s = sd.iE (f (Pi.single s 1) t) := by
  have h : ((GlobalTheory.TwU.seamGL sd f : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      (LinearMap.toMatrix' f.toLinearMap).map (sd.iE : Xf.E →+* D.host.E) := rfl
  rw [h, Matrix.map_apply, LinearMap.toMatrix'_apply]
  rfl

theorem adAt_pullV_fr [StarRing E] {hc : CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}
    {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (P : Q) (r s : Fin n) :
    adAt F P.1 (pullV g (p.fr P (Pi.single s 1)) r) = (1 : Matrix (Fin n) (Fin n) (P.1.adicCompletion E)) r s := by
  have e1 : GlobalTheory.Mem.ColAd.locM P.1 (g⁻¹ * g) = 1 := by rw [inv_mul_cancel, GlobalTheory.Mem.ColAd.locM_one]
  rw [← e1, GlobalTheory.Mem.ColAd.locM_mul, Matrix.mul_apply]
  unfold pullV
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mulVec, dotProduct, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, adAt_inclE, ← h.fr P t s]
  rfl

theorem frame_near : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (fb : SBof I a → GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), FrNear I l Z a (k (chOf c)) fb → ∀ P : SBof I a, GlobalTheory.TwU.NearAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (((K (chOf c)).y ⟨c, rfl⟩).1 * GlobalTheory.TwU.ratA (I.rec7 l Z).host.F (fb P)) (GlobalTheory.TwU.seamGL (sm I l Z) (frsF I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P)) := by
  classical
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c fb hfb P
  have hpt := hR.pt c
  have hd := fun z => (_root_.GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary.main I hOk l Z a ((I.rec7 l Z).R.N i) ((I.cst a).D P) P z).2.2
  unfold GlobalTheory.TwU.NearAt
  rw [hd]
  have hfb2 := (hd _).1 (hfb P).2
  have e : ∀ {G : Type} [Group G] (y k A C : G), (y * A)⁻¹ * C = (A⁻¹ * k) * ((y * k)⁻¹ * C) := by
    intros; group
  have key := e (G := GL (Fin ((I.rec7 l Z).R.N i)) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)) ((K (chOf c)).y ⟨c, rfl⟩).1
    (k (chOf c)) (GlobalTheory.TwU.ratA _ (fb P))
    (GlobalTheory.TwU.ratA _ (GlobalTheory.TwU.seamGL (sm I l Z) (frsF I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P)))
  rw [key]
  intro r s
  show Valued.v (GlobalTheory.Mem.ColAd.locM P.1 (_ * _) r s - _) ≤ _
  erw [GlobalTheory.Mem.ColAd.locM_mul]
  refine val_mul_sub_one_le hfb2 ?_ r s
  clear r s
  intro r s
  show Valued.v (adAt B.host.F P.1 (_) - _) ≤ _
  rw [inv_mul_ratA_apply]
  have hfr := frsF_eq_ptFr I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P
  have hcol : (fun t => ((GlobalTheory.TwU.seamGL (sm I l Z) (frsF I.sel (I.tup a) ((I.stp u a i).rep c).1.1 P) :
      GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) :
        Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E) t s) =
      ptFr ((I.stp u a i).rep c).1.1 P.1 (Pi.single s 1) :=
    funext fun t => by rw [seamGL_apply]; exact congrArg (fun f => f (Pi.single s 1) t) hfr
  rw [hcol]
  by_cases hG : P.1 ∈ (B.primes X).vGs
  · rw [(hOk.idx_ok a).depthG P hG]
    have e2 : ptFr ((I.stp u a i).rep c).1.1 P.1 = (extTo I.SQ ((I.stp u a i).rep c).1.1).deco.1.liftFr ⟨P.1, hG⟩ := by
      unfold ptFr
      rw [dite_eq_left hG]
      rfl
    rw [e2]
    exact le_exp_neg_one_of_lt_one' (val_sub_lt_of_liftFr hpt ⟨P.1, hG⟩ r s)
  · have hQ : P.1 ∈ I.Q a := (Finset.mem_union.1 P.2).resolve_left hG
    have hSQ : P.1 ∈ I.SQ := Finset.mem_biUnion.2 ⟨a, Finset.mem_univ _, hQ⟩
    have e3 : ptFr ((I.stp u a i).rep c).1.1 P.1 = (extTo I.SQ ((I.stp u a i).rep c).1.1).fr ⟨P.1, hSQ⟩ := rfl
    have h0 := adAt_pullV_fr hpt ⟨P.1, hSQ⟩ r s
    rw [e3]
    erw [h0, sub_self, map_zero]
    exact zero_le'

end GlobalTheory.Mem.Col2.AdT.FrameMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartsTupleTrivQ
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw


set_option maxHeartbeats 8000000 in
theorem match_base_trivQ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 B.host.F))) (i : ℕ), i ≤ B.R.m → ∀ (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (Lb0 : Ch0 → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U0 : Ch0 → Subgroup (GA B (B.R.N i))) (chi0 : ∀ β, U0 β →* ℂˣ) (y0 : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)) (st0 : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k0 : Ch0 → GA B (B.R.N i)), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.Reads u I.mu0 i chOf0 Lb0 U0 chi0 y0 st0 k0 → ∃ (g : Chart I u a i → Ch0) (k : Chart I u a i → GA B (B.R.N i)), AdmK I u a i k ∧ (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) ∧ ∀ β, ∃ c, chartOf I u a i c = β ∧ ∃ c0, chOf0 c0 = g β ∧ ∀ x : GA B (B.R.N i), (∀ v ∈ Q, bc (prV (E := B.host.E) v) x = 1) → (∀ κ, LocMv I u a i c ((k β)⁻¹ * x * k β) κ → ∃ κ0, LocMv I u I.mu0 i c0 ((k0 (g β))⁻¹ * x * k0 (g β)) κ0 ∧ (I.stp u a i).chr c.1 κ = (I.stp u I.mu0 i).chr c0.1 κ0) ∧ (∀ κ0, LocMv I u I.mu0 i c0 ((k0 (g β))⁻¹ * x * k0 (g β)) κ0 → ∃ κ, LocMv I u a i c ((k β)⁻¹ * x * k β) κ) := by
  intro B X I hI hP l u a Q i hi Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 h1 h2 hQ hR0
  obtain ⟨c0f, t, ht1, ht2, ht3, hM⟩ := GlobalTheory.Mem.Col2.TC.ChTw.Match.match_idx I hI hP l u a Q i hi h1 h2 hQ
  refine ⟨fun β => chOf0 (c0f β), fun β => k0 (chOf0 (c0f β)) * t β,
    GlobalTheory.Mem.Col2.TC.ChTw.admissibleBasePoint_chart_mul_twist I hI u a i Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 hR0 _ t ht1 ht2 ht3, ?_, ?_⟩
  · intro β v hv
    obtain ⟨hT, hg⟩ := GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad I hI l u a v hv
    show bc (prV (E := B.host.E) v) (k0 (chOf0 (c0f β)) * t β) = 1
    rw [map_mul, hR0.k_off (chOf0 (c0f β)) v hT (GlobalTheory.Mem.Col2.TC.not_underQ_mu0 I hI v) (Or.inl rfl), ht2 β v (Or.inr hg), mul_one]
  intro β
  obtain ⟨c, hc, hs⟩ := hM β
  refine ⟨c, hc, c0f β, rfl, ?_⟩
  intro x hx
  have e : (k0 (chOf0 (c0f β)) * t β)⁻¹ * x * (k0 (chOf0 (c0f β)) * t β) =
      (t β)⁻¹ * ((k0 (chOf0 (c0f β)))⁻¹ * x * k0 (chOf0 (c0f β))) * t β := by group
  rw [e]
  refine hs _ fun v hv => ?_
  rw [map_mul, map_mul, hx v hv, mul_one, map_inv, inv_mul_cancel]


set_option maxHeartbeats 8000000 in
theorem charts_match_trivQ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (K0 : ∀ β : Ch0, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf0 c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.ReadsK l Z u I.mu0 i hi chOf0 K0 → ∃ (g : Chart I u a i → Ch0) (k : Chart I u a i → GA B (B.R.N i)), AdmK I u a i k ∧ (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) ∧ ∀ (K : ∀ β : Chart I u a i, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // chartOf I u a i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.Reads u a i (chartOf I u a i) (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chartOf I u a i c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chartOf I u a i c)).stabI ⟨c, rfl⟩ s).1) k → ∀ β, (∀ κ : (K β).lev.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → ∃ h' : κ.1 ∈ (K0 (g β)).lev.U, (K β).lev.chi κ = (K0 (g β)).lev.chi ⟨κ.1, h'⟩) ∧ ∀ κ' : (K0 (g β)).lev.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ'.1 = 1) → κ'.1 ∈ (K β).lev.U := by
  intro B X I hI hP l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hR0
  obtain ⟨k0, hk0⟩ := hR0
  obtain ⟨g, k, hk, hkQ, hM⟩ := match_base_trivQ I hI hP l u a Q i hi Ch0 chOf0 _ _ _ _ _ k0 h1 h2 hQ hk0
  refine ⟨g, k, hk, hkQ, ?_⟩
  intro K hK β
  obtain ⟨c, hc, c0, hc0, hx⟩ := hM β
  subst hc
  have hgram := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have huni : ∀ {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (B.T u) (I.rec7 l Z).R.f bad) (x : GA B (B.R.N i)), x ∈ S.U → x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i) := by
    intro bad S x hx
    have h := ((S.U_eq x).1 hx).1
    rw [hgram] at h
    exact h
  have hnQ0 : ∀ v, ¬ I.UnderQ I.mu0 v := by
    rintro v ⟨P, hP, -⟩
    rw [ColIn.twistPrimes_reference_tuple_eq_empty] at hP
    exact absurd hP (Finset.notMem_empty _)
  refine ⟨fun κ hκ => ?_, fun κ' hκ' => ?_⟩
  · obtain ⟨κ1, hl1⟩ := GlobalTheory.Mem.Col2.TC.ChTw.locMv_of_mem I hI l u a i hi _ _ _ _ _ _ k hK c κ.1 (huni _ κ.1 κ.2)
      (fun v hv => hκ v ((hQ v).2 hv)) κ.2
    obtain ⟨κ0, hl0, hchr⟩ := (hx κ.1 hκ).1 κ1 hl1
    obtain ⟨hm0, hc0'⟩ := reads_of_locMv I hI hk0 c0 κ.1 κ0 (by rw [hc0]; exact hl0)
    obtain ⟨hm, hcc⟩ := reads_of_locMv I hI hK c κ.1 κ1 hl1
    have key : ∀ β0 (e : chOf0 c0 = β0), ∃ h' : κ.1 ∈ (K0 β0).lev.U,
        (((K0 β0).lev.chi ⟨κ.1, h'⟩ : ℂˣ) : ℂ) = B.embLL (((I.stp u I.mu0 i).chr c0.1 κ0 : B.LLˣ) : B.LL) := by
      intro β0 e
      subst e
      exact ⟨hm0, hc0'⟩
    obtain ⟨h', e'⟩ := key _ hc0
    refine ⟨h', Units.ext ?_⟩
    rw [e', ← hchr]
    exact hcc
  · have hm0 : κ'.1 ∈ (K0 (chOf0 c0)).lev.U := by rw [hc0]; exact κ'.2
    obtain ⟨κ0, hl0⟩ := GlobalTheory.Mem.Col2.TC.ChTw.locMv_of_mem I hI l u I.mu0 i hi _ _ _ _ _ _ k0 hk0 c0 κ'.1 (huni _ κ'.1 hm0)
      (fun v hv => absurd hv (hnQ0 v)) hm0
    rw [hc0] at hl0
    obtain ⟨κ, hl⟩ := (hx κ'.1 hκ').2 κ0 hl0
    exact (reads_of_locMv I hI hK c κ'.1 κ hl).1


set_option maxHeartbeats 8000000 in
theorem charts_tuple_trivQ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (K0 : ∀ β : Ch0, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf0 c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.ReadsK l Z u I.mu0 i hi chOf0 K0 → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (g : Ch → Ch0), (∃ k : Ch → GA B (B.R.N i), I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) ∧ ∀ β, (∀ v, v ∉ Q → (K β).lev.Uloc v = (K0 (g β)).lev.Uloc v) ∧ (∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1) ∧ ∀ (κ : (K β).lev.U) (κ' : (K0 (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = (K0 (g β)).lev.chi κ' := by
  intro B X I hok hpins l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hR
  obtain ⟨g, k, hk, hkQ, hC⟩ := charts_match_trivQ I hok hpins l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hR
  obtain ⟨K, hKB⟩ := GlobalTheory.Mem.Col2.ChExM.exists_charts I hok hpins l Z u a Q i hi h1 h2 hQ k hk
  have hK := hKB.1
  have hfin := hKB.2
  have hCK := hC K hK
  haveI := finite_chart I l u a i
  refine ⟨Chart I u a i, inferInstance, chartOf I u a i, K, g, ⟨k, hK, hkQ⟩, fun β => ⟨?_, hfin β, ?_⟩⟩
  · intro v hv
    refine GlobalTheory.stepLevel_uloc_eq_of_agree (K β).lev (K0 (g β)).lev (Q : Set _) (fun x hx => ⟨fun hxK => ?_, fun hx0 => ?_⟩) v hv
    · exact ((hCK β).1 ⟨x, hxK⟩ hx).1
    · exact (hCK β).2 ⟨x, hx0⟩ hx
  · intro κ κ' he hq
    obtain ⟨h', e⟩ := (hCK β).1 κ hq
    exact e.trans (congrArg (K0 (g β)).lev.chi (Subtype.ext he))

end GlobalTheory.Mem.Col2.TC.ChTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteSeriesThreeOfHyp
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory

theorem discreteSeries_three_of_hypotheses (hC : GlobalTheory.Published.DiscreteSeriesCoverExists) :
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.DiscreteSeriesUpqUnique → (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ) ∧ (∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')), Formalism.MainNotions.S.IsDS ε lam σ → Formalism.MainNotions.S.IsDS ε lam σ' → ∃ U : H ≃ₗᵢ[ℂ] H', ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ v, U (σ g v) = σ' g (U v)) ∧ (∀ (p q : ℕ) (T : GrpData p q) (lam : Ix p q → ℚ), IsParam lam → ∃ R : DSRep T, HasParam R lam) := by
  intro hE hU
  refine ⟨fun n ε lam hl => ?_, fun n ε lam hl H H' _ _ _ _ σ σ' hσ hσ' => hU n ε lam hl H H' σ σ' hσ hσ', hC⟩
  obtain ⟨H, i1, i2, σ, h1, h2, h3, h4, h5, h6, h7⟩ := hE n ε lam hl
  exact ⟨H, i1, i2, σ, h1, h2, h3, h4, h5, h6, h7⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHalfSelectionSplitPlacesBaseStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_half_selection_split_places_base : ∀ B : Base, ∃ (Pv : HeightOneSpectrum (𝓞 B.host.F) → HeightOneSpectrum (𝓞 B.host.E)) (d : PlacesOverCommonPrime B.host), Formalism.L2.Col.IsSel B.fields Pv ∧ (∀ v, Pv v ∈ aboveF (L := B.host.E) B.host.F v) ∧ Half B Pv ∧ (∀ v hv, Pv v = d.P v hv) ∧ ∀ v hv, Pv v = d.P' v hv := by
  first | exact @GlobalTheory.Mem.Top.Bl.exists_half_selection_split_places | exact GlobalTheory.Mem.Top.Bl.exists_half_selection_split_places | (intros; apply GlobalTheory.Mem.Top.Bl.exists_half_selection_split_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelChainOverTopSpacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelChain_over_top_spaces : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ (b : Bool) (m : D.what₂.Tup → Mat1 D.what₂.LL G) (s : D.what₂.Tup → Sp1 D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) G) (tA : ∀ μ, Tie1 D.what₂.embLL (m μ) (s μ)) (hA : ∀ t, m (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t), ∃ c : ChD D.what₂.Tup Φ D.R.m fun μ => (s μ).A, Nonempty (ChT y F.lv2 b rep (Top := fun μ => (s μ).A) (fun t x => ((tA (y.tup t)).cast (hA t)).j x) c) := by
  first | exact @GlobalTheory.Mem.R3.Rw.ChainLevel.chain_exists | exact GlobalTheory.Mem.R3.Rw.ChainLevel.chain_exists | (intros; apply GlobalTheory.Mem.R3.Rw.ChainLevel.chain_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftSpacesOverDefiniteFormsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_spaces_over_definite_forms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ (m : D.what₂.Tup → ℕ → Mat1 D.what₂.LL G) (s : D.what₂.Tup → ℕ → Sp1 D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) G) (tL : ∀ μ j, Tie1 D.what₂.embLL (m μ j) (s μ j)) (hL : ∀ (i : Fin D.R.m) t, m (y.tup t) ((i : ℕ) + 1) = lMat A3.A F.lv2.P0 F.lv2.ψ0 i t), ∃ l : LfD D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) D.what₂.Tup Φ fun μ j => (s μ j).A, Nonempty (LfT y F.lv2 rep (Mt := fun μ j => (s μ j).A) (fun i t x => ((tL (y.tup t) ((i : ℕ) + 1)).cast (hL i t)).j x) l) := by
  first | exact @GlobalTheory.LiftSpaces.exists_lift_spaces | exact GlobalTheory.LiftSpaces.exists_lift_spaces | (intros; apply GlobalTheory.LiftSpaces.exists_lift_spaces <;> assumption)
end

