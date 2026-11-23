module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.APlusComm
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0260
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0283

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDimensionalCoeffSpan
section
namespace GlobalTheory.CoefficientSpanFiniteDimensional

theorem dual_apply_eq_sum {W ι : Type} [AddCommGroup W] [Module ℂ W] [Fintype ι] (b : Module.Basis ι ℂ W)
    (ℓ : Module.Dual ℂ W) (w : W) (A : W →ₗ[ℂ] W) :
    ℓ (A w) = ∑ j, ∑ i, (b.repr w j * ℓ (b i)) * b.repr (A (b j)) i := by
  conv_lhs => rw [← b.sum_repr w]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul]
  conv_lhs => rw [← b.sum_repr (A (b j))]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem finiteDimensional_coeffSpan {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ ↥(GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  classical
  let b := Module.finBasis ℂ W
  let e : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) → (K → ℂ) :=
    fun p k => b.repr (ρ k (b p.2)) p.1
  haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range e)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range e)) (Submodule.span_le.mpr ?_)
  rintro f ⟨ℓ, w, rfl⟩
  have h : (fun k => ℓ (ρ k w)) = ∑ j, ∑ i, (b.repr w j * ℓ (b i)) • e (i, j) := by
    funext k
    rw [dual_apply_eq_sum b ℓ w (ρ k)]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e]
  rw [h]
  exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, j), rfl⟩)

end GlobalTheory.CoefficientSpanFiniteDimensional
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartLocalToFiniteAdelicComponentSelfStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitePart_localToFiniteAdelic_component_self : ∀ {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : Gv V v), (Formalism.IndefR.Lev.finE V (locFin V v g : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) v) = (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram g).val.map (Algebra.TensorProduct.comm D.host.F (Fv D.host.F v) D.host.E) := by
  first | exact @GlobalTheory.FinLocSelf.finE_locFin_map_prV | exact GlobalTheory.FinLocSelf.finE_locFin_map_prV | (intros; apply GlobalTheory.FinLocSelf.finE_locFin_map_prV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FixedOfForallLocalSubgroupFixedFiniteAdelic
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

noncomputable section

namespace GlobalTheory.TrIdem

theorem fixed_of_forall_finLoc_mem : ∀ (D : D7) (V : HSp D) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ (K' : ∀ v, Subgroup (GLoc D.sp.cm.sig V.gram v)), (∀ v, K' v ≤ Kv V v) → ∀ x : W, (∀ v, ∀ k ∈ K' v, σ (locFin V v k) x = x) → ∀ g : GfC V, (∀ v, finLoc V v g ∈ K' v) → σ g x = x := by
  intro D V W _ _ σ hσ K' hK' x hx g hg
  have fl_self : ∀ a (y : GLoc D.sp.cm.sig V.gram a), finLoc V a (locFin V a y) = y :=
    fun a y => proj_emb_self _ _ a y
  have fl_ne : ∀ v a, v ≠ a → ∀ (y : GLoc D.sp.cm.sig V.gram a), finLoc V v (locFin V a y) = 1 :=
    fun v a h y => proj_emb_ne _ _ h y
  let St : Subgroup (GfC V) :=
    { carrier := {k | σ k x = x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have e : σ a⁻¹ (σ a x) = x := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha] at e }
  have hSt : IsOpen (St : Set (GfC V)) := hσ x
  let U : Subgroup (GA D V) := St.comap (toFin V)
  have hU : IsOpen (U : Set (GA D V)) := hSt.preimage (continuous_toFin V)
  obtain ⟨S, hS⟩ := GlobalTheory.PlaceGen.exists_levelOff_le D.sp.cm.sig V.gram (frameLat V) U hU
  have key : ∀ k : GfC V, (∀ v ∈ S, finLoc V v k = 1) → (∀ v, v ∉ S → finLoc V v k ∈ Kv V v) → σ k x = x := by
    intro k h1 h2
    have hk : (k : GA D V) ∈ levelOff D.sp.cm.sig V.gram (frameLat V) S := mem_levelOff.2 ⟨k.2, h1, h2⟩
    have h := hS hk
    have e : toFin V (k : GA D V) = k := toFin_coe k
    change σ (toFin V (k : GA D V)) x = x at h
    rwa [e] at h
  have step : ∀ T : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∀ k : GfC V, (∀ v, finLoc V v k ∈ K' v) →
      (∀ v ∈ S, v ∉ T → finLoc V v k = 1) → σ k x = x := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro k hk h1
      exact key k (fun v hv => h1 v hv (Finset.notMem_empty v)) (fun v _ => hK' v (hk v))
    | insert a T ha ih =>
      intro k hk h1
      set k' := locFin V a (finLoc V a k)⁻¹ * k with hk'
      have hfix : σ k' x = x := by
        refine ih k' (fun v => ?_) (fun v hv hvT => ?_)
        · by_cases h : v = a
          · subst h
            simp [k', map_mul, fl_self]
          · simp only [k', map_mul, fl_ne v a h, one_mul]
            exact hk v
        · by_cases h : v = a
          · subst h
            simp [k', map_mul, fl_self]
          · simp only [k', map_mul, fl_ne v a h, one_mul]
            exact h1 v hv (by simp [h, hvT])
      have hkk : k = locFin V a (finLoc V a k) * k' := by
        simp [k', ← mul_assoc, ← map_mul]
      rw [hkk, map_mul, Module.End.mul_apply, hfix]
      exact hx a _ (hk a)
  exact step S g hg (fun v hv hvS => absurd hv hvS)

end GlobalTheory.TrIdem
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPureTensors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FockPureTensor

section Generic

variable {ι κ V : Type} [DecidableEq κ] [AddCommGroup V] [Module ℂ V] {Pu : (κ → V) → V → Prop}


omit [DecidableEq κ] in
def IsMultiLin (Pu : (κ → V) → V → Prop) : Prop :=
  ∀ (x y z : κ → V) (f g : V) (q : κ) (c : ℂ), Pu x f → Pu y g → (∀ p, p ≠ q → y p = x p) → (∀ p, p ≠ q → z p = x p) →
    z q = c • x q + y q → Pu z (c • f + g)

theorem IsMultiLin.upd (h : IsMultiLin Pu) {x : κ → V} {q : κ} {a b f g : V} (c : ℂ)
    (h1 : Pu (Function.update x q a) f) (h2 : Pu (Function.update x q b) g) :
    Pu (Function.update x q (c • a + b)) (c • f + g) := by
  refine h _ _ _ f g q c h1 h2 (fun p hp => ?_) (fun p hp => ?_) ?_
  · simp [hp]
  · simp [hp]
  · simp

theorem IsMultiLin.upd_smul (h : IsMultiLin Pu) {x : κ → V} {q : κ} {a f : V} (c : ℂ)
    (h1 : Pu (Function.update x q a) f) : Pu (Function.update x q (c • a)) (c • f) := by
  have h0 : Pu (Function.update x q 0) 0 := by
    simpa using h.upd (-1) h1 h1
  simpa using h.upd c h1 h0

theorem poly_step (h : IsMultiLin Pu) (L L₀ : MvPolynomial ι ℂ →ₗ[ℂ] V) (q : κ) (s : Set ι)
    (hX : ∀ y ∈ s, ∀ x R Q, Pu (Function.update x q (L₀ Q)) (L R) →
      Pu (Function.update x q (L₀ (MvPolynomial.X y * Q))) (L (MvPolynomial.X y * R)))
    {P : MvPolynomial ι ℂ} (hP : P ∈ MvPolynomial.supported ℂ s) :
    ∀ x R Q, Pu (Function.update x q (L₀ Q)) (L R) → Pu (Function.update x q (L₀ (P * Q))) (L (P * R)) := by
  have hP' : P ∈ Algebra.adjoin ℂ (MvPolynomial.X '' s) := by
    rwa [← MvPolynomial.supported_eq_adjoin_X]
  clear hP
  induction hP' using Algebra.adjoin_induction with
  | mem P hPs =>
    obtain ⟨y, hy, rfl⟩ := hPs
    exact hX y hy
  | algebraMap r =>
    intro x R Q hRQ
    rw [← Algebra.smul_def, ← Algebra.smul_def, map_smul, map_smul]
    exact h.upd_smul r hRQ
  | add P₁ P₂ _ _ ih₁ ih₂ =>
    intro x R Q hRQ
    simpa [add_mul] using h.upd 1 (ih₁ x R Q hRQ) (ih₂ x R Q hRQ)
  | mul P₁ P₂ _ _ ih₁ ih₂ =>
    intro x R Q hRQ
    simpa [mul_assoc] using ih₁ x (P₂ * R) (P₂ * Q) (ih₂ x R Q hRQ)

theorem prod_step {α β : Type} [DecidableEq (α ⊕ β)] {Pu : (α ⊕ β → V) → V → Prop} (h : IsMultiLin Pu) (L L₀ : MvPolynomial ι ℂ →ₗ[ℂ] V)
    (s : β → Set ι)
    (hX : ∀ τ, ∀ y ∈ s τ, ∀ x R Q, Pu (Function.update x (.inr τ) (L₀ Q)) (L R) →
      Pu (Function.update x (.inr τ) (L₀ (MvPolynomial.X y * Q))) (L (MvPolynomial.X y * R)))
    {P : β → MvPolynomial ι ℂ} (hP : ∀ τ, P τ ∈ MvPolynomial.supported ℂ (s τ)) {x : α ⊕ β → V}
    (hx : Pu x (L 1)) (hx0 : ∀ τ, x (.inr τ) = L₀ 1) (t : Finset β) :
    Pu (Sum.elim (fun v => x (.inl v)) fun τ => if τ ∈ t then L₀ (P τ) else L₀ 1) (L (∏ τ ∈ t, P τ)) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have e : (Sum.elim (fun v => x (.inl v)) fun τ => if τ ∈ (∅ : Finset β) then L₀ (P τ) else L₀ 1) = x := by
      funext p
      rcases p with v | τ
      · rfl
      · simp [hx0]
    rw [e, Finset.prod_empty]
    exact hx
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha]
    set G := (Sum.elim (fun v => x (.inl v)) fun τ => if τ ∈ t then L₀ (P τ) else L₀ 1) with hG
    have hGa : G (.inr a) = L₀ 1 := by simp [hG, ha]
    have hfix : Function.update G (.inr a) (L₀ 1) = G := by
      rw [← hGa, Function.update_eq_self]
    have key := poly_step h L L₀ (.inr a) (s a) (hX a) (hP a) G (∏ τ ∈ t, P τ) 1 (by rw [hfix]; exact ih)
    have e : Function.update G (.inr a) (L₀ (P a * 1)) =
        Sum.elim (fun v => x (.inl v)) (fun τ => if τ ∈ insert a t then L₀ (P τ) else L₀ 1) := by
      funext p
      rcases p with v | τ
      · simp [hG]
      · by_cases hτ : τ = a
        · subst hτ
          simp
        · simp [hG, hτ]
    rw [← e]
    exact key

private theorem foldr_mem_of_invariant {X ι : Type} (A : ι → X → X) (Pth : X → Prop)
    (hth : ∀ i x, Pth x → Pth (A i x)) (l : List ι) {x : X} (hx : Pth x) :
    Pth (l.foldr (fun i g => A i g) x) := by
  induction l with
  | nil => exact hx
  | cons a l ih => exact hth a _ ih

private theorem foldr_eq_of_perm_of_commute {X ι : Type} (A : ι → X → X) (Pth : X → Prop)
    (hth : ∀ i x, Pth x → Pth (A i x)) (hc : ∀ i j x, Pth x → A i (A j x) = A j (A i x))
    {l l' : List ι} (hp : l.Perm l') {x : X} (hx : Pth x) :
    l.foldr (fun i g => A i g) x = l'.foldr (fun i g => A i g) x := by
  induction hp with
  | nil => rfl
  | cons a _ ih => simp only [List.foldr_cons, ih]
  | swap a b l => exact hc b a _ (foldr_mem_of_invariant A Pth hth l hx)
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem opPow_single_one_add {X ι : Type} (A : ι → (X → ℂ) → (X → ℂ)) (Pth : (X → ℂ) → Prop)
    (hth : ∀ i x, Pth x → Pth (A i x)) (hc : ∀ i j x, Pth x → A i (A j x) = A j (A i x))
    (y : ι) (u : ι →₀ ℕ) {x : X → ℂ} (hx : Pth x) :
    opPow A (Finsupp.single y 1 + u) x = A y (opPow A u x) := by
  unfold opPow
  have hp : ((Finsupp.toMultiset (Finsupp.single y 1 + u)).toList).Perm (y :: (Finsupp.toMultiset u).toList) := by
    rw [← Multiset.coe_eq_coe, Multiset.coe_toList, ← Multiset.cons_coe, Multiset.coe_toList,
      map_add, Finsupp.toMultiset_single, one_nsmul, Multiset.singleton_add]
  rw [foldr_eq_of_perm_of_commute A Pth hth hc hp hx]
  rfl

private theorem constr_opPow_X_mul {X σ : Type} (A : σ → (X → ℂ) → (X → ℂ)) (Pth : (X → ℂ) → Prop)
    (hadd : ∀ f f', Pth f → Pth f' → Pth (f + f')) (hsm : ∀ (c : ℂ) f, Pth f → Pth (c • f))
    (hth : ∀ i f, Pth f → Pth (A i f)) (hc : ∀ i j f, Pth f → A i (A j f) = A j (A i f))
    (hA : ∀ i f f', Pth f → Pth f' → A i (f + f') = A i f + A i f')
    (hAs : ∀ i (c : ℂ) f, Pth f → A i (c • f) = c • A i f)
    {g : X → ℂ} (hg : Pth g) (y : σ) (Q : MvPolynomial σ ℂ) :
    ((MvPolynomial.basisMonomials σ ℂ).constr ℂ fun k => opPow A k g) (MvPolynomial.X y * Q) =
      A y (((MvPolynomial.basisMonomials σ ℂ).constr ℂ fun k => opPow A k g) Q) := by
  set Φ := (MvPolynomial.basisMonomials σ ℂ).constr ℂ fun k => opPow A k g with hΦ
  have hmono : ∀ m a, Φ (MvPolynomial.monomial m a) = a • opPow A m g := by
    intro m a
    have e : MvPolynomial.monomial m a = a • MvPolynomial.basisMonomials σ ℂ m := by
      simp [MvPolynomial.smul_monomial]
    rw [e, map_smul, hΦ, Module.Basis.constr_basis]
  have hpow : ∀ m, Pth (opPow A m g) := fun m => by
    unfold opPow
    exact foldr_mem_of_invariant A Pth hth _ hg
  have hall : ∀ P, Pth (Φ P) := fun P =>
    MvPolynomial.induction_on' P (fun m a => by rw [hmono]; exact hsm a _ (hpow m))
      (fun p q hp hq => by rw [map_add (f := _)]; exact hadd _ _ hp hq)
  refine MvPolynomial.induction_on' Q (fun u a => ?_) (fun p q hp hq => ?_)
  · rw [MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, hmono, hmono,
      opPow_single_one_add A Pth hth hc y u hg, hAs y a _ (hpow u)]
  · rw [mul_add, map_add (f := _), map_add (f := _), hp, hq, hA y _ _ (hall p) (hall q)]

end Generic

section Theta

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f₀ : WO S T → ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem pureTensorO_X_mul (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) (y : FVar D T.rank S.rank) :
    pureTensorO ψ θ S T sS sT BS BT g (MvPolynomial.X y * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT y (pureTensorO ψ θ S T sS sT BS BT g Q) := by
  have hψ := base_std hb
  have hθ := base_inf hb
  have hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ) := hb.1
  have hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ) := hb.2.1
  unfold pureTensorO pureTensorL aPlusAll
  exact constr_opPow_X_mul
    (fun k : FVar D T.rank S.rank => aPlus (heisO ψ S T) θ k.1 (cplxO (sS k.1) (sT k.1)) (unitMap (BS k.1) (BT k.1) k.2.1 k.2.2))
    (IsThetaFunO ψ S T)
    (fun f f' hf hf' => GlobalTheory.OrientedHeis.theta_add hf hf')
    (fun c f hf => GlobalTheory.OrientedHeis.theta_smul c hf)
    (fun k f hf => GlobalTheory.FockSubst.aPlus_th (hψ := hψ) (hθ := hθ) (τ := k.1) (J := _) (z := _) hf)
    (fun i j f hf => GlobalTheory.FockSubst.aPlus_comm (hψ := hψ) (hθ := hθ) (τ := i.1) (z := _) (hS := hS) (hT := hT)
      (τ' := j.1) (z' := _) hf)
    (fun k f f' hf hf' => GlobalTheory.FockSubst.aPlus_add (hψ := hψ) (hθ := hθ) (τ := k.1) (J := _) (z := _) hf hf')
    (fun k c f hf => GlobalTheory.FockSubst.aPlus_smul (hψ := hψ) (hθ := hθ) (τ := k.1) (J := _) (z := _) c hf)
    hg y Q

theorem isPure_aPlus (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕)
    (y : Place D → WO S T → ℂ) (τ : D.what₂.Tau) (a g : WO S T → ℂ)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (h : IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (Function.update y (.inr τ) a) g) :
    IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
      (Function.update y (.inr τ) (Formalism.IndefR.Datum.aPlus (heisO ψ S T) θ τ J z a))
      (Formalism.IndefR.Datum.aPlus (heisO ψ S T) θ τ J z g) := by
  have hlin := _root_.GlobalTheory.PureLinear.isPure_linear_and_dRho D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ
  have hML : IsMultiLin (IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀) := hlin.1
  have hd : ∀ w : Matrix (Fin T.rank) (Fin S.rank) ℂ,
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
        (Function.update y (.inr τ) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ w a))
        (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ w g) := by
    intro w
    refine hlin.2 _ _ g τ w h (fun p hp => ?_) ?_
    · simp [hp]
    · simp
  have h4 := hML.upd_smul ((fockScale D τ : ℂ)⁻¹) (hML.upd (-Complex.I) (hd (J z)) (hd z))
  rw [GlobalTheory.FockSubst.aPlus_eq, GlobalTheory.FockSubst.aPlus_eq,
    add_comm (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z a), add_comm (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z g)]
  exact h4

end Theta

theorem fockPure : ∀ D : D7, FockPure D := by
  intro D
  unfold FockPure
  intro ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 BS BT pS pT hb hμ _ _ x f hx hx0 P hP
  have hth0 : IsThetaFunO ψ S T f₀ := base_theta hb
  have hthf : IsThetaFunO ψ S T f := hx.2.1
  have hlin := _root_.GlobalTheory.PureLinear.isPure_linear_and_dRho D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ
  have hone : ∀ g : WO S T → ℂ, pureTensorO ψ θ S T sS sT BS BT g 1 = g := by
    intro g
    have e1 : (1 : MvPolynomial (FVar D T.rank S.rank) ℂ) = MvPolynomial.basisMonomials (FVar D T.rank S.rank) ℂ 0 := by
      rw [MvPolynomial.coe_basisMonomials]
      rfl
    unfold pureTensorO pureTensorL
    rw [e1, Module.Basis.constr_basis]
    unfold opPow
    simp
  have hX : ∀ τ, ∀ y ∈ (fun τ : D.what₂.Tau => {y : FVar D T.rank S.rank | y.1 = τ}) τ,
      ∀ x' R Q, IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
          (Function.update x' (.inr τ) (pureTensorO ψ θ S T sS sT BS BT f₀ Q)) (pureTensorO ψ θ S T sS sT BS BT f R) →
        IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀
          (Function.update x' (.inr τ) (pureTensorO ψ θ S T sS sT BS BT f₀ (MvPolynomial.X y * Q)))
          (pureTensorO ψ θ S T sS sT BS BT f (MvPolynomial.X y * R)) := by
    intro τ y hy x' R Q h
    have hy' : y.1 = τ := hy
    subst hy'
    rw [pureTensorO_X_mul hb BS BT hth0 Q y, pureTensorO_X_mul hb BS BT hthf R y]
    exact isPure_aPlus hb hμ x' y.1 _ _ (cplxO (sS y.1) (sT y.1)) (unitMap (BS y.1) (BT y.1) y.2.1 y.2.2) h
  have key := prod_step hlin.1 (pureTensorO ψ θ S T sS sT BS BT f) (pureTensorO ψ θ S T sS sT BS BT f₀)
    (fun τ : D.what₂.Tau => {y : FVar D T.rank S.rank | y.1 = τ}) hX hP (x := x)
    (by rw [hone]; exact hx) (fun τ => by rw [hone]; exact hx0 τ) Finset.univ
  simpa using key

end GlobalTheory.FockPureTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKMapExtensionLevelCharacterCovariant
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GKExtLevel

theorem sobCont_sub_smul {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ₁ ℓ₂ : H →ₗ[ℂ] ℂ}
    (c : ℂ) (h₁ : Sobolev₂ Lie σ ℓ₁) (h₂ : Sobolev₂ Lie σ ℓ₂) : Sobolev₂ Lie σ (ℓ₁ - c • ℓ₂) := by
  obtain ⟨S₁, C₁, hS₁, hC₁⟩ := h₁
  obtain ⟨S₂, C₂, hS₂, hC₂⟩ := h₂
  refine ⟨S₁ ++ S₂, |C₁| + ‖c‖ * |C₂|, fun l hl X hX => ?_, fun w hw => ?_⟩
  · rcases List.mem_append.1 hl with h | h
    exacts [hS₁ l h X hX, hS₂ l h X hX]
  · have nn : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ (S.map fun l => ‖l.foldr (dRep σ) w‖).sum :=
      fun S => List.sum_nonneg fun x hx => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _
    have n1 := nn S₁
    have n2 := nn S₂
    rw [List.map_append, List.sum_append]
    have b1 := (hC₁ w hw).trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) n1)
    have b2 := (hC₂ w hw).trans (mul_le_mul_of_nonneg_right (le_abs_self C₂) n2)
    have e : ‖(ℓ₁ - c • ℓ₂) w‖ ≤ ‖ℓ₁ w‖ + ‖c‖ * ‖ℓ₂ w‖ := by
      rw [← norm_mul]
      simpa using norm_sub_le (ℓ₁ w) (c * ℓ₂ w)
    have h3 := mul_le_mul_of_nonneg_left b2 (norm_nonneg c)
    have p1 : 0 ≤ |C₁| * (S₂.map fun l => ‖l.foldr (dRep σ) w‖).sum := mul_nonneg (abs_nonneg _) n2
    have p2 : 0 ≤ ‖c‖ * |C₂| * (S₁.map fun l => ‖l.foldr (dRep σ) w‖).sum :=
      mul_nonneg (mul_nonneg (norm_nonneg _) (abs_nonneg _)) n1
    nlinarith

theorem lev : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M J χ μ 𝓕 T₀ →
    ∀ T : MMap M, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.Extends T T₀ →
    (∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
      ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x) →
    ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  intro hHC D θ _ V S M J χ μ 𝓕 T₀ hT₀ T hext hcont v k hk g
  have hsm : ∀ τ, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, w ∈ M.sm τ := fun τ w hw => by
    haveI := (M.ds τ).1
    exact Submodule.subset_span (GlobalTheory.Published.HarishChandraModules.smoothVec hHC (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 hw
      (M.fr_unit τ) (M.fr_gram τ))
  have key : ∀ s : Finset D.what₂.Tau, ∀ v : M.Vec, (∀ τ ∉ s, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) →
      T v (g * k) = χ k * T v g := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      rw [hext v (fun τ => ⟨v τ, hv τ (Finset.notMem_empty τ)⟩) (fun τ => rfl)]
      exact hT₀.2.2.2.2.2.1 _ k hk g
    | @insert τ s hτ ih =>
      intro v hv
      obtain ⟨ℓ₁, h₁, e₁⟩ := hcont τ v (g * k)
      obtain ⟨ℓ₂, h₂, e₂⟩ := hcont τ v g
      have h0 : ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, (ℓ₁ - χ k • ℓ₂) w = 0 := by
        intro w hw
        have hi := ih (Function.update v τ ⟨w, hsm τ w hw⟩) (fun τ' hτ' => by
          by_cases h : τ' = τ
          · subst h
            simpa using hw
          · rw [Function.update_of_ne h]
            exact hv τ' (by simp [h, hτ']))
        have a1 := e₁ ⟨w, hsm τ w hw⟩
        have a2 := e₂ ⟨w, hsm τ w hw⟩
        simp only at a1 a2
        rw [LinearMap.sub_apply, LinearMap.smul_apply, a1, a2, hi, smul_eq_mul, sub_self]
      have hz := _root_.GlobalTheory.KFiniteDense.eq_zero_of_kFin hHC D V S M τ _ (sobCont_sub_smul (χ k) h₁ h₂) h0 (v τ) (v τ).2
      have a1 := e₁ (v τ)
      have a2 := e₂ (v τ)
      rw [Function.update_eq_self] at a1 a2
      rw [LinearMap.sub_apply, LinearMap.smul_apply, a1, a2, smul_eq_mul, sub_eq_zero] at hz
      exact hz
  exact key Finset.univ v fun τ h => absurd (Finset.mem_univ τ) h

end GlobalTheory.GKExtLevel
end

