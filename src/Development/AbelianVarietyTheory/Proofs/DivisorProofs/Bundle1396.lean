module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0937
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0157
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1226
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoidAlgebraActionViaRingActionApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunctionThetaTransformRationalCoordsCM
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ThetaTransformF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff

theorem charR_hasDerivAt : ∀ (χ : ℝ → ℂ), Continuous χ → (∀ s t, χ (s + t) = χ s * χ t) → χ 0 = 1 →
    ∀ s, HasDerivAt χ (deriv χ 0 * χ s) s := GlobalTheory.T.hasDerivAt_of_continuous_real_to_complex_exponential

theorem biChar_contDiff : ∀ (k : ℕ) (Q : (Fin k → ℝ) → ℝ → ℂ), Continuous (Function.uncurry Q) →
    (∀ t s s', Q t (s + s') = Q t s * Q t s') → (∀ t t' s, Q (t + t') s = Q t s * Q t' s) → (∀ t, Q t 0 = 1) →
    ContDiff ℝ ∞ (fun t => deriv (Q t) 0) := GlobalTheory.T.contDiff_deriv_zero_of_continuous_bicharacter

section Phase

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}

def phase (ψ : AddChar (AF F) ℂ) (M : ℝ →+ VA F N) (w : VA F N) (s : ℝ) : ℂ := ψ (⅟(2 : AF F) * symV w (M s))

theorem symV_add_left (w w' u : VA F N) : symV (w + w') u = symV w u + symV w' u := by
  simp only [symV, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring

theorem symV_add_right (w u u' : VA F N) : symV w (u + u') = symV w u + symV w u' := by
  simp only [symV, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]; ring

theorem symV_zero_right (w : VA F N) : symV w 0 = 0 := by simp [symV]

theorem continuous_symV : Continuous fun p : VA F N × VA F N => symV p.1 p.2 := by
  unfold symV dotProduct
  fun_prop

theorem phase_add (M : ℝ →+ VA F N) (w : VA F N) (s s' : ℝ) :
    phase ψ M w (s + s') = phase ψ M w s * phase ψ M w s' := by
  simp only [phase, map_add (f := _), symV_add_right, mul_add, AddChar.map_add_eq_mul]

theorem phase_add_left (M : ℝ →+ VA F N) (w w' : VA F N) (s : ℝ) :
    phase ψ M (w + w') s = phase ψ M w s * phase ψ M w' s := by
  simp only [phase, symV_add_left, mul_add, AddChar.map_add_eq_mul]

theorem phase_zero (M : ℝ →+ VA F N) (w : VA F N) : phase ψ M w 0 = 1 := by
  simp [phase, symV_zero_right]

theorem continuous_phase (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) :
    Continuous fun p : VA F N × ℝ => phase ψ M p.1 p.2 := by
  have h1 : Continuous fun p : VA F N × ℝ => (p.1, M p.2) := by fun_prop
  have h2 : Continuous fun p : VA F N × ℝ => symV p.1 (M p.2) :=
    Continuous.comp (g := fun q : VA F N × VA F N => symV q.1 q.2) (f := fun p : VA F N × ℝ => (p.1, M p.2)) continuous_symV h1
  have h3 : Continuous fun p : VA F N × ℝ => ⅟(2 : AF F) * symV p.1 (M p.2) := continuous_const.mul h2
  exact hψ.comp h3

end Phase

end GlobalTheory.ThetaTransformF

end

noncomputable section

namespace GlobalTheory.ThetaTransformF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff

section Crit

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}

theorem continuous_phase_right (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) (w : VA F N) :
    Continuous (phase ψ M w) := by
  have h : Continuous fun s : ℝ => ((w, s) : VA F N × ℝ) := by fun_prop
  exact Continuous.comp (g := fun p : VA F N × ℝ => phase ψ M p.1 p.2) (f := fun s : ℝ => ((w, s) : VA F N × ℝ))
    (continuous_phase hψ hM) h

theorem phase_hasDerivAt (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) (w : VA F N) (s : ℝ) :
    HasDerivAt (phase ψ M w) (deriv (phase ψ M w) 0 * phase ψ M w s) s :=
  charR_hasDerivAt _ (continuous_phase_right hψ hM w) (phase_add M w) (phase_zero M w) s

theorem contDiff_phase_deriv (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) {k : ℕ}
    {L : (Fin k → ℝ) →+ VA F N} (hL : Continuous L) (u : VA F N) :
    ContDiff ℝ ∞ fun t => deriv (phase ψ M (u + L t)) 0 := by
  have e : (fun t => deriv (phase ψ M (u + L t)) 0) =
      fun t => deriv (phase ψ M u) 0 + deriv (phase ψ M (L t)) 0 := by
    funext t
    have hf : phase ψ M (u + L t) = fun s => phase ψ M u s * phase ψ M (L t) s := funext (phase_add_left M u (L t))
    have hd := ((phase_hasDerivAt hψ hM u 0).mul (phase_hasDerivAt hψ hM (L t) 0)).deriv
    simp only [phase_zero, mul_one, one_mul] at hd
    rw [hf]
    exact hd
  rw [e]
  have hQ : Continuous (Function.uncurry fun t s => phase ψ M (L t) s) := by
    have h : Continuous fun p : (Fin k → ℝ) × ℝ => ((L p.1, p.2) : VA F N × ℝ) := by fun_prop
    exact Continuous.comp (g := fun p : VA F N × ℝ => phase ψ M p.1 p.2)
      (f := fun p : (Fin k → ℝ) × ℝ => ((L p.1, p.2) : VA F N × ℝ)) (continuous_phase hψ hM) h
  exact contDiff_const.add (biChar_contDiff k (fun t s => phase ψ M (L t) s) hQ
    (fun t s s' => phase_add M (L t) s s') (fun t t' s => by simp only [map_add (f := _)]; exact phase_add_left M _ _ s)
    (fun t => phase_zero M (L t)))

theorem hasDerivAt_lineV (hψ : Continuous ψ) {M : ℝ →+ VA F N} (hM : Continuous M) {f : VA F N → ℂ}
    {w : VA F N} {c : ℂ} (hd : HasDerivAt (fun s : ℝ => heisV ψ (M s) f w) c 0) :
    HasDerivAt (fun s : ℝ => f (w + M s)) (c + -deriv (phase ψ M w) 0 * f w) 0 := by
  have hp := phase_hasDerivAt hψ hM w 0
  have hne : ∀ s, phase ψ M w s ≠ 0 := fun s h0 => by
    have := AddChar.map_add_eq_mul ψ (⅟(2 : AF F) * symV w (M s)) (-(⅟(2 : AF F) * symV w (M s)))
    rw [add_neg_cancel, AddChar.map_zero_eq_one] at this
    have h0' : ψ (⅟(2 : AF F) * symV w (M s)) = 0 := h0
    rw [h0', zero_mul] at this
    exact one_ne_zero this
  have e : (fun s : ℝ => f (w + M s)) = fun s => heisV ψ (M s) f w / phase ψ M w s := by
    funext s
    rw [heisV]
    exact (mul_div_cancel_left₀ _ (hne s)).symm
  rw [e]
  refine (hd.div hp (hne 0)).congr_deriv ?_
  have h1 : heisV ψ (M 0) f w = f w := by
    rw [heisV, map_zero, symV_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]
  rw [h1, phase_zero, mul_one]
  field_simp
  ring

theorem contDiff_of_heisV_closed (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (V : Set (VA F N → ℂ))
    (hc : ∀ f ∈ V, Continuous f)
    (hd : ∀ f ∈ V, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ f' ∈ V, ∀ w,
      HasDerivAt (fun t : ℝ => heisV ψ (M t) f w) (f' w) 0) :
    ∀ f ∈ V, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ VA F N), Continuous L → (∀ t, fin (L t).1 = 0 ∧ fin (L t).2 = 0) →
      ∀ w, ContDiff ℝ ∞ fun t => f (w + L t) := by
  intro f hf k L hL hLf u
  let P : ((Fin k → ℝ) → ℂ) → Prop := fun G => ∃ f ∈ V, G = fun t => f (u + L t)
  refine GlobalTheory.Unf.MatCoef.contDiff_of_partials P ?_ ?_ _ ⟨f, hf, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    have h : Continuous fun t => u + L t := by fun_prop
    exact (hc f hf).comp h
  · rintro _ ⟨f, hf, rfl⟩ i
    let E : ℝ →ₗ[ℝ] (Fin k → ℝ) := LinearMap.toSpanSingleton ℝ (Fin k → ℝ) (Pi.single i 1)
    let M : ℝ →+ VA F N := L.comp E.toAddMonoidHom
    have hM : Continuous M := hL.comp E.continuous_of_finiteDimensional
    obtain ⟨f', hf', hD⟩ := hd f hf M ⟨hM, fun s => hLf _⟩
    refine ⟨2, ![fun _ => 1, fun t => -deriv (phase ψ M (u + L t)) 0],
      ![fun t => f' (u + L t), fun t => f (u + L t)], fun j => ?_, fun j => ?_, fun t => ?_⟩
    · fin_cases j
      · exact contDiff_const
      · exact (contDiff_phase_deriv hψ hM hL u).neg
    · fin_cases j
      · exact ⟨f', hf', rfl⟩
      · exact ⟨f, hf, rfl⟩
    · have e : (fun s : ℝ => f (u + L (t + s • Pi.single i 1))) = fun s => f ((u + L t) + M s) := by
        funext s
        have : E s = s • Pi.single i 1 := rfl
        rw [map_add (f := _), add_assoc, ← this]
        rfl
      rw [e]
      convert hasDerivAt_lineV hψ hM (hD (u + L t)) using 1
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul]

end Crit

end GlobalTheory.ThetaTransformF

end

noncomputable section

namespace GlobalTheory.ThetaTransformF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ
open scoped ContDiff

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Invertible (2 : AF F)]
  {σ : E →ₐ[F] E} {nS nT N : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ} {e : WOF F E nS nT ≃ₗ[AF F] VA F N}

theorem symplOHF_eq (he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (e w) (e w')) (w w' : WOF F E nS nT) :
    symplOHF σ JS JT ξ₀ w w' = ⅟(2 : AF F) * symV (e w) (e w') := by
  rw [symplOHF, he, invOf_two_eq]

theorem heisOF_comp (he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (e w) (e w')) (u : WOF F E nS nT)
    (f : VA F N → ℂ) : heisOF σ JS JT ξ₀ ψ u (f ∘ e) = heisV ψ (e u) f ∘ e := by
  funext w
  simp only [heisOF, heisV, Function.comp_apply, symplOHF_eq he, map_add (f := _)]

end Main


open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in
theorem isThetaFunOF_thV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N),
          Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ hstd N e he hrat Φ hΦ
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hstd.1
  obtain ⟨hc, -, hfin, hinf⟩ := coordF nT nS N e
  have hcont : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), Continuous (thV B.ψ Φ) := fun Φ hΦ =>
    _root_.GlobalTheory.ThetaTransform.continuous_thV F N B.ψ hR hψ Φ (_root_.GlobalTheory.SchwartzDecay.decay_of_mem_schA F N Φ hΦ)
  refine ⟨fun γ w => ?_, ?_, (hcont Φ hΦ).comp hc, ?_⟩
  · obtain ⟨y, z, h⟩ := hrat γ
    simp only [Function.comp_apply, map_add (f := _), symplOHF_eq he, h]
    exact quasiV_thV B.ψ hψ.2.2.1 Φ y z (e w)
  · obtain ⟨U, hUo, hU⟩ := _root_.GlobalTheory.WeilLevel.schA_level F N B.ψ hR hψ Φ hΦ
    refine ⟨U.comap e.toLinearMap.toAddMonoidHom, hUo.preimage hc, fun u hu h0 => ?_⟩
    rw [heisOF_comp he, ← thV_schr, hU (e u) hu ((hinf u).1 h0).1 ((hinf u).1 h0).2]
  · intro k L hL hL0 w
    have h := contDiff_of_heisV_closed B.ψ hψ.1 {g | ∃ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), g = thV B.ψ Φ}
      (by rintro _ ⟨Φ, hΦ, rfl⟩; exact hcont Φ hΦ)
      (by
        rintro _ ⟨Φ, hΦ, rfl⟩ M hM
        obtain ⟨Φ', hΦ', hd⟩ := _root_.GlobalTheory.ThetaTransform.hasDerivAt_heisV_line F N B.ψ hR hψ Φ hΦ M hM
        exact ⟨_, ⟨Φ', hΦ', rfl⟩, hd⟩)
      _ ⟨Φ, hΦ, rfl⟩ k (e.toLinearMap.toAddMonoidHom.comp L) (hc.comp hL) (fun t => (hfin _).1 (hL0 t)) (e w)
    simpa [Function.comp_def] using h

end GlobalTheory.ThetaTransformF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqOfPointsOfGerm
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)
open scoped CategoryTheory.Obj NumberField
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IwLevel

namespace GlobalTheory.IwLevel.KerDet

theorem isClosed_pt {k : Type} [Field k] {X : Scheme.{0}} (s : X ⟶ Sp k) [IsFinite s] (x : X) :
    IsClosed ({x} : Set X) := by
  rw [← closure_subset_iff_isClosed]
  intro w hw
  have h : x ⤳ w := specializes_iff_mem_closure.mpr hw
  have e : s w = s x := Subsingleton.elim (α := Spec (CommRingCat.of k)) _ _
  have hd := (s.isDiscrete_preimage_singleton (s x)).to_subtype
  have hs : (⟨x, rfl⟩ : s ⁻¹' {s x}) ⤳ ⟨w, e⟩ := Topology.IsInducing.subtypeVal.specializes_iff.mp h
  exact congrArg Subtype.val hs.eq.symm

theorem exists_section {k L : Type} [Field k] [IsAlgClosed k] [Field L] {X : Scheme.{0}} (s : X ⟶ Sp k)
    [IsFinite s] (u : Sp L ⟶ X) : ∃ a : Sp k ⟶ X, a ≫ s = 𝟙 _ ∧ u = (u ≫ s) ≫ a := by
  obtain ⟨⟨x, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField L X).symm.surjective u
  have hx := isClosed_pt s x
  refine ⟨pointOfClosedPoint s x hx, pointOfClosedPoint_comp s x hx, ?_⟩
  change Spec.map φ ≫ X.fromSpecResidueField x =
    ((Spec.map φ ≫ X.fromSpecResidueField x) ≫ s) ≫ Spec.map (residueFieldIsoBase s x hx).hom ≫
      X.fromSpecResidueField x
  simp only [Category.assoc]
  rw [← SpecMap_residueFieldIsoBase_inv_assoc s x hx, ← Spec.map_comp_assoc (residueFieldIsoBase s x hx).hom,
    Iso.hom_inv_id, Spec.map_id, Category.id_comp]

theorem exists_stalk_factor {X : Scheme.{0}} {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ X) (x : X)
    (hx : f (IsLocalRing.closedPoint R) = x) : ∃ ψ : X.presheaf.stalk x ⟶ R, f = Spec.map ψ ≫ X.fromSpecStalk x := by
  obtain ⟨⟨y, φ, hφ⟩, rfl⟩ := (SpecToEquivOfLocalRing X R).symm.surjective f
  have hy : y = x := by
    rw [← hx]
    change y = (Spec.map φ ≫ X.fromSpecStalk y) _
    exact ((Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg (X.fromSpecStalk y) Spec_closedPoint).trans Scheme.fromSpecStalk_closedPoint)).symm
  subst hy
  exact ⟨φ, rfl⟩

variable {k : Type} [Field k]

def InK {A B : Over (Sp k)} [GrpObj B] (π : A ⟶ B) {T : Scheme.{0}} (y : T ⟶ A.left) : Prop :=
  ∃ z : T ⟶ Sp k, z ≫ (η[B]).left = y ≫ π.left

theorem inK_iff {A B : Over (Sp k)} [GrpObj B] (π : A ⟶ B) {T : Scheme.{0}} (y : T ⟶ A.left) :
    InK π y ↔ y ≫ π.left = (y ≫ A.hom) ≫ (η[B]).left := by
  have hη : (η[B]).left ≫ B.hom = 𝟙 _ := by simpa using Over.w (η[B])
  refine ⟨fun ⟨z, hz⟩ => ?_, fun h => ⟨_, h.symm⟩⟩
  have e : z = y ≫ A.hom := by
    have := congrArg (· ≫ B.hom) hz
    simp only [Category.assoc, hη, Category.comp_id, Over.w π] at this
    exact this
  rw [← hz, e]

theorem comp_eq_one_iff {A B : Over (Sp k)} [GrpObj B] (π : A ⟶ B) {T : Over (Sp k)} (Y : T ⟶ A) :
    Y ≫ π = 1 ↔ InK π Y.left := by
  have hT : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)
  rw [inK_iff, Over.w Y, ← hT]
  constructor
  · intro h; exact congrArg (fun q => q.left) h
  · intro h; exact Over.OverMorphism.ext h

end GlobalTheory.IwLevel.KerDet

namespace GlobalTheory.IwLevel.KerDet

variable {k : Type} [Field k]

theorem toUnit_left (T : Over (Sp k)) : (toUnit T).left = T.hom := by simpa using Over.w (toUnit T)

theorem one_left {A T : Over (Sp k)} [GrpObj A] : (1 : T ⟶ A).left = T.hom ≫ (η[A]).left := by
  rw [← toUnit_left]; rfl

variable [IsAlgClosed k]

theorem local_step {A B B' : Over (Sp k)} [GrpObj A] [GrpObj B] [GrpObj B'] (π : A ⟶ B) (π' : A ⟶ B')
    [IsMonHom π] [IsMonHom π'] [IsFinite π.left]
    (h1 : ∀ a : 𝟙_ (Over (Sp k)) ⟶ A, a ≫ π = 1 → a ≫ π' = 1)
    (x₀ : A.left) (hx₀ : x₀ ∈ Set.range (η[A]).left.base)
    (h2 : ∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'),
      InK π (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) →
      InK π' (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀))
    {R : CommRingCat.{0}} [IsLocalRing R] (y : Spec R ⟶ A.left) (hy : InK π y) : InK π' y := by
  let c : Sp (IsLocalRing.ResidueField R) ⟶ Spec R := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  haveI : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue R)).hom :=
    inferInstanceAs (IsLocalHom (IsLocalRing.residue R))
  have hc : c (IsLocalRing.closedPoint (IsLocalRing.ResidueField R)) = IsLocalRing.closedPoint R :=
    Spec_closedPoint
  obtain ⟨z, hz⟩ := hy
  let ũ : Sp (IsLocalRing.ResidueField R) ⟶ pullback π.left (η[B]).left :=
    pullback.lift (c ≫ y) (c ≫ z) (by rw [Category.assoc, Category.assoc, hz])
  obtain ⟨a', ha's, hu⟩ := exists_section (pullback.snd π.left (η[B]).left) ũ
  let a0 := a' ≫ pullback.fst π.left (η[B]).left
  have hη : (η[B]).left ≫ B.hom = 𝟙 _ := by simpa using Over.w (η[B])
  have ha0 : a0 ≫ A.hom = 𝟙 _ := by
    simp only [a0, Category.assoc]
    rw [← Over.w π, pullback.condition_assoc, hη, Category.comp_id, ha's]
  let a : 𝟙_ (Over (Sp k)) ⟶ A := Over.homMk a0 ha0
  have ha : a ≫ π = 1 := (comp_eq_one_iff π a).2 ⟨a' ≫ pullback.snd _ _, by
    simp only [a, a0, Over.homMk_left, Category.assoc, pullback.condition]⟩
  have ha' : a ≫ π' = 1 := h1 a ha
  have e1 : c ≫ y = (ũ ≫ pullback.snd _ _) ≫ a0 := by
    simp only [a0]; rw [← Category.assoc, ← hu]; exact (pullback.lift_fst _ _ _).symm
  have hu' : c ≫ y = ((c ≫ y) ≫ A.hom) ≫ a0 := by
    have e2 : (c ≫ y) ≫ A.hom = ũ ≫ pullback.snd _ _ := by
      rw [e1, Category.assoc, ha0]; exact Category.comp_id _
    rw [e2]; exact e1
  let T' : Over (Sp k) := Over.mk (y ≫ A.hom)
  let Y : T' ⟶ A := Over.homMk y rfl
  let Ta : T' ⟶ A := toUnit T' ≫ a
  let D : T' ⟶ A := Y / Ta
  have hYπ : Y ≫ π = 1 := (comp_eq_one_iff π Y).2 ⟨z, hz⟩
  have hDπ : D ≫ π = 1 := by
    simp only [D, Ta]
    rw [GrpObj.div_comp, hYπ, Category.assoc, ha, MonObj.comp_one, div_one]
  let C : Over.mk ((c ≫ y) ≫ A.hom) ⟶ T' := Over.homMk c (by simp [T'])
  have hCY : C ≫ Y = C ≫ Ta := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Ta, toUnit_left, Over.homMk_left, C, Y, T', Over.mk_hom]
    rw [← Category.assoc c, ← Category.assoc c]
    exact hu'
  have hCD : C ≫ D = 1 := by
    simp only [D]; rw [GrpObj.comp_div, hCY, div_self']
  have hD0 : c ≫ D.left = ((c ≫ y) ≫ A.hom) ≫ (η[A]).left := by
    have := congrArg (fun q => q.left) hCD
    simp only [Over.comp_left, one_left] at this
    exact this
  have hDx : D.left (IsLocalRing.closedPoint R) = x₀ := by
    obtain ⟨p, hp⟩ := hx₀
    rw [← hc]
    change (c ≫ D.left) _ = x₀
    rw [hD0, ← hp]
    change (η[A]).left (((c ≫ y) ≫ A.hom) _) = (η[A]).left p
    exact congrArg (η[A]).left (Subsingleton.elim (α := Spec (CommRingCat.of k)) _ _)
  obtain ⟨ψ, hψ⟩ := exists_stalk_factor D.left x₀ hDx
  have hDK : InK π D.left := (comp_eq_one_iff π D).1 hDπ
  have hDK' : InK π' D.left := by
    rw [hψ] at hDK ⊢
    exact h2 R ψ.hom hDK
  have hDπ' : D ≫ π' = 1 := (comp_eq_one_iff π' D).2 hDK'
  have hYπ' : Y ≫ π' = 1 := by
    rw [← div_mul_cancel Y Ta, MonObj.mul_comp, hDπ', Category.assoc, ha', MonObj.comp_one, _root_.one_mul]
  exact (comp_eq_one_iff π' Y).1 hYπ'

end GlobalTheory.IwLevel.KerDet

namespace GlobalTheory.IwLevel.KerDet

variable {k : Type} [Field k] [IsAlgClosed k]

theorem inK_of_inK {A B B' : Over (Sp k)} [GrpObj A] [GrpObj B] [GrpObj B'] (π : A ⟶ B) (π' : A ⟶ B')
    [IsMonHom π] [IsMonHom π'] [IsFinite π.left]
    (h1 : ∀ a : 𝟙_ (Over (Sp k)) ⟶ A, a ≫ π = 1 → a ≫ π' = 1)
    (x₀ : A.left) (hx₀ : x₀ ∈ Set.range (η[A]).left.base)
    (h2 : ∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'),
      InK π (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) →
      InK π' (Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀))
    {T : Scheme.{0}} (y : T ⟶ A.left) (hy : InK π y) : InK π' y := by
  rw [inK_iff] at hy ⊢
  refine ReciprocityTheory.ChartRestriction.G.TB.JGPf.ext_of_fromSpecStalk _ _ fun t => ?_
  have h := local_step π π' h1 x₀ hx₀ h2 (T.fromSpecStalk t ≫ y) ((inK_iff π _).2 (by
    simp only [Category.assoc]; rw [hy, Category.assoc]))
  rw [inK_iff] at h
  simpa only [Category.assoc] using h

end GlobalTheory.IwLevel.KerDet

namespace GlobalTheory.IwLevel

end GlobalTheory.IwLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KinfFinite
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspKinfFin

theorem kinf_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∀ (ψ : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspOn σ J Xf Yf S K ψ → ∀ g₀ : GAd σ J,
        (∀ k : GlobalTheory.CuspRep.Kinf E d, g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀ ∈ K) →
        FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : GlobalTheory.CuspRep.Kinf E d => fun g : GlobalTheory.CuspRep.GA E d => ψ (ι (g * GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀))) := by
  intro F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ K _ S l d h ι _ _ _ _ _ ψ hψ g₀ hK
  classical
  let T : (GAd σ J → ℂ) →ₗ[ℂ] (GlobalTheory.CuspRep.GA E d → ℂ) :=
    { toFun := fun φ g => φ (ι g * g₀)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hV := hψ.1.kfin
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun g => ψ (g * k))).map T) ?_
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  refine ⟨fun x => ψ (x * (g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀)), Submodule.subset_span ⟨⟨_, hK k⟩, rfl⟩, ?_⟩
  funext g
  show ψ (ι g * g₀ * (g₀⁻¹ * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) * g₀)) = _
  simp only [map_mul, mul_assoc, mul_inv_cancel_left]

end GlobalTheory.CuspKinfFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoidAlgebraActionViaRingActionApplyStatement
section
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_ksSub_quotient_augmentation_of_two_roots : ∀ {k O C Idx H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O] [Fintype Idx] [FiniteDimensional k H] (σ : O →+* Module.End k H) (χ : Idx → C →+* k), Function.Injective χ → ∀ (Fil : Submodule k H), (∀ a, ∀ x ∈ Fil, σ a x ∈ Fil) → ∀ (ω : C) (r₀ r₁ : k), r₀ ≠ r₁ → (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0 → (∀ i, χ i ω = r₀) → ∀ (hG : ∀ a, ∀ x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1), σ a x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)) (hZ : ∀ a, ∀ x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)), σ a x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1))), jSub σ χ ⊤ ≤ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) → ∀ (i : Idx), let G := Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1); let Z := jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)); let σW := qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx); finrank k ((G ⧸ Z.comap G.subtype) ⧸ mSub σW (χ i) ⊤) + finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) = finrank k (H ⧸ mSub σ (χ i) ⊤) := by
  first | (exact @GlobalTheory.HTRho.FilDim.finrank_fildim) | (exact GlobalTheory.HTRho.FilDim.finrank_fildim) | (intros; apply GlobalTheory.HTRho.FilDim.finrank_fildim  <;> assumption)
end

