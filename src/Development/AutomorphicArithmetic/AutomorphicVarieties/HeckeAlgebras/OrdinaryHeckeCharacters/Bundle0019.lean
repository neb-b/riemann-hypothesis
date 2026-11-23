module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AuTeichEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DenseU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.MapOfRel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.WtBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CharpolyEqProd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1033
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0137
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.PointRepUnramifiedAtAuxiliaryPlace
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle0006
public import Mathlib.RingTheory.Teichmuller
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.UpOperatorEigenvalues.SplitW

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AbsH
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

set_option maxHeartbeats 1000000 in
private theorem absH (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hA : H.Ax)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ) (hθ : H.IsWt θ)
    (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop) (hAut : H.Aut ι P)
    (lam : Wt L l n) (hl : lam ∈ H.admitted) (hd : H.DenseWt θ lam) (a : H.Op → c.O) (K : H.Lev)
    {B : Type} [CommRing B] [Algebra c.O B] (D₀ : W.GDet n B H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Bˣ)
    (j : A →ₐ[c.O] B)
    (key : ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (φ : A →ₐ[c.O] T) (gen : H.Op → T),
      (∀ i, gen i - algebraMap c.O T (a i) ∈ maximalIdeal T) →
      ∀ (D : W.GDet n T H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Tˣ), D.IsCont (maximalIdeal T) →
      (∀ v i, Alg.AdicCont (maximalIdeal T) fun g => (ψ v i g : T)) →
      (∀ (w : H.Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ →
        D.chi (MonoidAlgebra.single (H.prj σ⁻¹) 1) =
          heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) →
      (∀ v i (s : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)) (y : Uo ((H.Sl v).adicCompletion L)),
        (g : G L Ω) = (s : G L Ω) → H.art v s = y →
        (ψ v i g * H.epsV T v g ^ (i : ℕ) : Tˣ) * φ (θ (eV n H.Sl v i y)) = 1) →
      (∀ v (j : Fin n) (s : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)), (g : G L Ω) = (s : G L Ω) → H.art v s = Hi.unif _ →
        ((∏ i with i ≤ j, ψ v i g * H.epsV T v g ^ (i : ℕ) : Tˣ) : T) = gen (.inr (v, j))) →
      ∀ Gd : (T →ₐ[c.O] Qbar l) → Prop, (∀ t : T, (∀ x, Gd x → x t = 0) → t = 0) →
      (∀ x, Gd x → ∃ ρ : H.Gq →* GL (Fin n) (Qbar l), P lam ρ ∧ D.map x.toRingHom = W.GDet.ofRep (W.mat ρ) ∧
        ∀ v, W.HasFlag (ρ.comp (H.dec v)) fun i => W.pushCh x.toRingHom (ψ v i)) →
      ∃ f : B →ₐ[c.O] T, D₀.map f.toRingHom = D ∧ (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = ψ v i) ∧ ∀ b, f (j b) = φ b) :
    ∃ J : Ideal B, H.IsJ θ a K D₀ ψ₀ j J := by
  by_cases hne : H.MK θ a K = ⊥
  · exact ⟨⊤, Or.inl ⟨hne, rfl⟩⟩
  haveI hF : Fact (CommOn (H.MK θ a K) (H.op A)) := ⟨((hiComm L Ω l n c _ hA A θ hθ K).2.2.2 a).1⟩
  obtain ⟨hCO, -, -, hres, -, hgen⟩ := hiAlg L Ω l n c _ hA A θ hθ a K hne
  obtain ⟨D, ψ, hU⟩ := coreDet hN L Ω l n c _ hA A θ hθ ι _ hAut lam hl hd a K
  have hO := coreH hN L Ω l n c _ hA A θ hθ ι _ hAut lam hl hd a K D ψ hU
  obtain ⟨f, h1, h2, h3⟩ := key (H.TK θ a K) (IsScalarTower.toAlgHom c.O A _) (H.gen θ a K) hres D ψ hU.cont hU.ψ_cont
    hU.frob hU.ψ_unit hU.ψ_unif (fun x => H.Good θ (x.toRingHom.comp (algebraMap A _)) lam) (hO.sep lam hl hd)
    fun x hx => by
      obtain ⟨ρ, -, -, e1, e2, e3⟩ := hO.pt lam hl x hx.2.1
      exact ⟨ρ, e1, e2, fun v => (e3 hx v).1⟩
  have h2' : (fun v i => W.pushCh f.toRingHom (ψ₀ v i)) = ψ := funext fun v => funext fun i => h2 v i
  have hU' : H.IsMap θ a K D₀ ψ₀ f := by
    unfold HSet.IsMap
    rw [h1, h2']
    exact hU
  exact ⟨RingHom.ker f, Or.inr ⟨hF, hCO, f, hne, hU',
    deformationRing_to_heckeAlgebra_surjective L Ω l n c _ hA A _ B (H.gen θ a K) D₀ ψ₀ f hU'.frob hU'.ψ_unif _ h3 hgen, h3, rfl⟩⟩

theorem UpperTheory.V.Hi.jEx :
    Af.HypothesesH → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : HD Q ι Λ) (K : (hset Q R.τ₀).Lev), ∃ J : Ideal B.B, R.IsJ B K J := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K
  have hN : GlobalTheory.Mem.LiteralAutomorphy.LitN := hP.litN
  have hA : (hset Q R.τ₀).Ax := axU hN l L Ω s n hn V Q c R.m R.τ₀
  have hAut := autU hP l L Ω s n hn V Q c r ι R.m R.τ₀ R.type
  let lam : Wt L l n := fun _ => ⟨0, fun _ _ _ => le_rfl⟩
  have hd : (hset Q R.τ₀).DenseWt R.θ lam := (denseU hN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta).2 lam
  refine absH hN (hset Q R.τ₀) hA Λ.Λ R.θ R.isWt ι _ hAut lam (Set.mem_univ _) hd R.a K B.u.D B.u.ψ (Λ.toPair B.u) ?_
  intro T _ _ _ φ gen hres D ψ hc hψ hfr hun huf Gd hsep hpt
  exact JEx.map_of_rel B Λ φ D ψ hc (heckeDeterminant_reduction_eq_residual l L Ω s n V Q c r ι Λ R hA T gen hres D hc hfr)
    (exists_ordinaryCharacters_heckeAlgebra l L Ω s n V Q c r ι Λ R hA T φ gen hres ψ hψ hun huf)
    (heckeDeterminant_satisfies_deformation_relations l L Ω s n hn V c r ι lam T D ψ Gd hsep hpt)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.IrrOfComp
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section SlopeTestRemainingChoices

open Formalism.MainNotions.N

private theorem unr_of {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (w : HeightOneSpectrum (𝓞 L)) :
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  haveI : IsGalois (Lp L) L := inferInstance
  have h := GlobalTheory.RayFromArtin.unramIn_of_ine (K := Lp L) (Ω := Ω) L (v := w.under (𝓞 (Lp L))) fun A hA σ hσ => by
    obtain ⟨g, rfl⟩ := s.unr A _ hA hσ
    ext x
    apply (algebraMap L Ω).injective
    exact (AlgEquiv.restrictNormal_commutes (W.resP L Ω g) L x).trans (g.commutes x)
  have hb : w.asIdeal.inertia Gal(L/Lp L) = ⊥ := by
    rw [eq_bot_iff]
    intro τ hτ
    exact h τ ⟨w.asIdeal, w.isPrime, ⟨rfl⟩, hτ⟩
  have h1 := UpperTheory.V.CF.ineCard.1 (Lp L) L w
  rw [hb, Subgroup.card_bot] at h1
  haveI := w.isPrime
  haveI := w.isMaximal
  haveI : (w.asIdeal.under (𝓞 (Lp L))).IsMaximal := Ideal.IsMaximal.under _ _
  exact Ideal.ramificationIdx_eq_one_iff.1 h1.symm

variable {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ}

private theorem inv_comp {φ : Γ' →* Γ} (hφ : Function.Surjective φ) (r : Γ →* GL (Fin n) k) (M : Submodule k (Fin n → k)) :
    IsInv (r.comp φ) M ↔ IsInv r M :=
  ⟨fun h g => by obtain ⟨g, rfl⟩ := hφ g; exact h g, fun h g => h (φ g)⟩

private theorem ss_comp {φ : Γ' →* Γ} (hφ : Function.Surjective φ) {r : Γ →* GL (Fin n) k} (h : IsSSRep r) :
    IsSSRep (r.comp φ) := fun M hM => by
  obtain ⟨M', h1, h2⟩ := h M ((inv_comp hφ r M).1 hM)
  exact ⟨M', (inv_comp hφ r M').2 h1, h2⟩

private theorem irr_of_comp (φ : Γ' →* Γ) {r : Γ →* GL (Fin n) k} (h : Af.IsIrr (r.comp φ)) : Af.IsIrr r :=
  ⟨h.1, fun _ _ _ => Submodule.mem_top, fun M hM hi => h.2.2 M hM fun g => hi (φ g)⟩

private theorem ss_of_irr {r : Γ →* GL (Fin n) k} (h : Af.IsIrr r) : IsSSRep r := fun M hM => by
  rcases h.2.2 M le_top hM with rfl | rfl
  · exact ⟨⊤, h.2.1, isCompl_bot_top⟩
  · refine ⟨⊥, fun g v hv => ?_, isCompl_top_bot⟩
    rw [(Submodule.mem_bot k).1 hv]
    simp

private theorem irr_iso {r r' : Γ →* GL (Fin n) k} (e : Af.RepIso r r') (h : Af.IsIrr r) : Af.IsIrr r' := by
  obtain ⟨P, hP⟩ := e
  refine ⟨h.1, fun _ _ _ => Submodule.mem_top, fun M _ hM => ?_⟩
  let E : (Fin n → k) ≃ₗ[k] (Fin n → k) := (Matrix.GeneralLinearGroup.toLin P).toLinearEquiv
  have hE : ∀ v, E v = (P : Matrix (Fin n) (Fin n) k).mulVec v := fun v => rfl
  have hi : IsInv r (M.comap (E : (Fin n → k) →ₗ[k] (Fin n → k))) := fun g v hv => by
    have := hM g _ hv
    change (r' g : Matrix (Fin n) (Fin n) k).mulVec ((P : Matrix (Fin n) (Fin n) k).mulVec v) ∈ M at this
    change (P : Matrix (Fin n) (Fin n) k).mulVec _ ∈ M
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, hP, inv_mul_cancel_right, Units.val_mul, ← Matrix.mulVec_mulVec] at this
  have hm : M = (M.comap (E : (Fin n → k) →ₗ[k] (Fin n → k))).map (E : (Fin n → k) →ₗ[k] (Fin n → k)) :=
    (Submodule.map_comap_eq_of_surjective E.surjective M).symm
  rcases h.2.2 _ le_top hi with h0 | h0
  · left; rw [hm, h0, Submodule.map_bot]
  · right; rw [hm, h0, Submodule.map_top, LinearEquiv.range]

private theorem iso_of_det {r r' : Γ →* GL (Fin n) k} (h : IsSSRep r) (h' : IsSSRep r')
    (e : W.GDet.ofRep (W.mat r) = W.GDet.ofRep (W.mat r')) : Af.RepIso r' r := by
  obtain ⟨P, hP⟩ := AlgebraTools.Det.bnRep (W.mat r) (W.mat r') h h' fun g => by
    rw [← (AlgebraTools.Det.repApi (W.mat r)).2.1 g, ← (AlgebraTools.Det.repApi (W.mat r')).2.1 g, e]
  refine ⟨P, fun g => ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  exact Units.ext (hP g).symm

private theorem factor {O A T K : Type} [CommRing O] [CommRing A] [CommRing T] [CommRing K] [Algebra O A] [Algebra O T]
    [Algebra O K] (f : A →ₐ[O] T) (hf : Function.Surjective f) (x : A →ₐ[O] K) (hx : RingHom.ker f ≤ RingHom.ker x) :
    ∃ y : T →ₐ[O] K, ∀ b, y (f b) = x b :=
  ⟨(Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb).comp (Ideal.quotientKerAlgEquivOfSurjective hf).symm.toAlgHom,
    fun b => by
      have : (Ideal.quotientKerAlgEquivOfSurjective hf).symm (f b) = Ideal.Quotient.mk _ b := by
        rw [AlgEquiv.symm_apply_eq]; rfl
      exact (congrArg (Ideal.Quotient.liftₐ (RingHom.ker f) x fun _ hb => hx hb) this).trans rfl⟩

private theorem map_comp {n : ℕ} {A T K Γ : Type} [CommRing A] [CommRing T] [CommRing K] [Group Γ] (D : W.GDet n A Γ)
    (f : A →+* T) (y : T →+* K) (x : A →+* K) (h : ∀ b, y (f b) = x b) : (D.map f).map y = D.map x := by
  obtain rfl : x = y.comp f := RingHom.ext fun b => (h b).symm
  rfl

end SlopeTestRemainingChoices

private theorem absPt {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ)
    (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] {R : Type} [CommRing R] [Algebra c.O R]
    (D₀ : W.GDet n R H.Gq) (j : A →ₐ[c.O] R) (f : R →ₐ[c.O] H.TK θ a K) (hf : Function.Surjective f)
    (hj : ∀ b, f (j b) = algebraMap A _ b) {P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop} {I : Ideal (H.TK θ a K)}
    {ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ} (out : H.Out θ a K P I (D₀.map f.toRingHom) ψ)
    (x : R →ₐ[c.O] Qbar l) (hx : RingHom.ker f ≤ RingHom.ker x) (lam : Wt L l n) (hl : lam ∈ H.admitted)
    (har : H.Arith θ (x.comp j).toRingHom lam) :
    ∃ ρ : H.Gq →* GL (Fin n) (Qbar l), Continuous ρ ∧ Formalism.MainNotions.N.IsSSRep ρ ∧ P lam ρ ∧
      D₀.map (x : R →+* Qbar l) = W.GDet.ofRep (W.mat ρ) := by
  obtain ⟨y, hy⟩ := factor f hf x hx
  have e1 : y.toRingHom.comp (algebraMap A _) = (x.comp j).toRingHom := RingHom.ext fun b =>
    (congrArg y (hj b)).symm.trans (hy _)
  obtain ⟨ρ, hc, hs, hP, hD, -⟩ := out.pt lam hl y (e1 ▸ har)
  exact ⟨ρ, hc, hs, hP, (map_comp D₀ f.toRingHom y.toRingHom x hy).symm.trans hD⟩

private theorem core (H : Af.HypothesesH) {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (hn : 1 ≤ n) {V : s.Lev} {Q : QData V} {c : Coef l}
    {r : Resid V.frame c.O n} {ι : Qbar l ≃+* ℂ} {B : UniversalOrdinaryDeterminantRing r} {Λ : LamObj r} {R : HD Q ι Λ} {K : (hset Q R.τ₀).Lev}
    {J : Ideal B.B} (hJ : R.IsJ B K J) (x : B.Pt) (h : s.Wt n) (hx : J ≤ RingHom.ker x) (ha : x.Arith h) :
    ∃ (lam : Wt L l n) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)), Continuous ρ ∧ Formalism.MainNotions.N.IsSSRep ρ ∧ PU r ι lam ρ ∧
      x.IsRep (ρ.comp V.pr) := by
  rcases hJ with ⟨_, rfl⟩ | ⟨i1, i2, f, -, hmap, hsurj, hlam, rfl⟩
  · exact absurd (hx (Submodule.mem_top (x := 1))) (by simp)
  obtain ⟨⟨lam, hl⟩, hb⟩ := wtBridge H.litN l L Ω s n hn V Q c R.m R.τ₀ r B Λ R.θ R.theta h ha.1
  have har := (hb lam hl x).1.1 ha
  have out := coreH H.litN L Ω l n c (hset Q R.τ₀) (axU H.litN l L Ω s n hn V Q c R.m R.τ₀) Λ.Λ R.θ R.isWt ι (PU r ι)
    (autU H l L Ω s n hn V Q c r ι R.m R.τ₀ R.type) lam (Set.mem_univ _)
    ((denseU H.litN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta).2 lam) R.a K _ _ hmap
  obtain ⟨ρ, hc, hs, hP, e3⟩ := absPt (hset Q R.τ₀) R.θ R.a K B.u.D (Λ.toPair B.u) f hsurj hlam out x hx lam (Set.mem_univ _) har
  refine ⟨lam, ρ, hc, hs, hP, ?_⟩
  replace e3 : x.D = W.GDet.ofRep (W.mat ρ) := e3
  change x.D.comap V.pr = _
  rw [e3]
  exact (AlgebraTools.Det.repApi (W.mat ρ)).2.2.2.2.2.2.1 V.pr
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.JDense
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem UpperTheory.V.Hi.dense_arithmetic_points {O A B T E : Type} [CommRing O] [CommRing A] [CommRing B] [CommRing T] [CommRing E]
    [Algebra O A] [Algebra O B] [Algebra O T] [Algebra O E] [Algebra A T] (lam : A →ₐ[O] B) (f : B →ₐ[O] T)
    (hf : ∀ a, f (lam a) = algebraMap A T a) (P : (A →+* E) → Prop) (G : (B →ₐ[O] E) → Prop)
    (hG : ∀ x : B →ₐ[O] E, P (x.comp lam).toRingHom → G x)
    (hsep : ∀ t : T, (∀ x : T →ₐ[O] E, P (x.toRingHom.comp (algebraMap A T)) → x t = 0) → t = 0) (b : B)
    (hb : ∀ x : B →ₐ[O] E, RingHom.ker f ≤ RingHom.ker x → G x → x b = 0) : b ∈ RingHom.ker f := by
  rw [RingHom.mem_ker]
  refine hsep (f b) fun x hx => hb (x.comp f) (fun y hy => ?_) (hG _ ?_)
  · rw [RingHom.mem_ker] at hy ⊢
    rw [AlgHom.comp_apply, hy, map_zero]
  · have e : ((x.comp f).comp lam).toRingHom = x.toRingHom.comp (algebraMap A T) :=
      RingHom.ext fun y => congrArg x (hf y)
    rw [e]
    exact hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.JrTeichEx
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section Abstract

open UpperTheory.V.W

private theorem jr_teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  haveI : CharP (O ⧸ maximalIdeal O) l := inferInstanceAs (CharP (ResidueField O) l)
  haveI : PerfectRing (ResidueField O) l := inferInstance
  let j : ResidueField O →+* Perfection (O ⧸ maximalIdeal O) l :=
    Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O) (RingHom.id (ResidueField O))
  have hj : ∀ x, Perfection.coeff (O ⧸ maximalIdeal O) l 0 (j x) = x := fun x => by
    have := (Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O)).symm_apply_apply (RingHom.id (ResidueField O))
    exact RingHom.congr_fun this x
  refine ⟨(Perfection.teichmuller l (maximalIdeal O)).comp j, fun x => ?_⟩
  exact (Perfection.mk_teichmuller (j x)).trans (hj x)

private theorem jr_isTeich {l : ℕ} [hl : Fact l.Prime] {F : GFrame l} (c : Coef l) {n : ℕ} (r : Resid F c.O n) :
    ∃ t, r.IsTeich t ∧ ∀ i g, r.chib i g = 1 → t i g = 1 := by
  obtain ⟨hc, hfin, hlm, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  haveI : Finite (ResidueField c.O) := hfin
  haveI : CharP (ResidueField c.O) l := by
    refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]
    exact hlm
  obtain ⟨τ, hτ⟩ := jr_teich_ex l c.O
  refine ⟨fun i => (Units.map τ).comp (r.chib i), fun i g => ⟨hτ _, ?_⟩, fun i g h => ?_⟩
  · rw [MonoidHom.comp_apply, ← map_pow, ← Nat.card_units, pow_card_eq_one', map_one]
  · rw [MonoidHom.comp_apply, h, map_one]

private theorem jr_abs {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (J : Ideal B.B) {ι : Type} (K : Type) [CommRing K] [Algebra O K]
    (x : ι → B.B →ₐ[O] K) (hJ : ∀ i, ∀ b ∈ J, x i b = 0) (sep : ∀ b, (∀ i, x i b = 0) → b ∈ J)
    (ρ : ι → F.G₀ →* GL (Fin n) K) (hD : ∀ i, B.u.D.map (x i : B.B →+* K) = GDet.ofRep (mat (ρ i)))
    (form : ∀ i, ∃ P, F.IsForm O n (ρ i) P)
    (flag : ∀ i v, HasFlag ((ρ i).comp (F.φ v)) fun j => pushCh (x i : B.B →+* K) (B.u.ψ v j))
    (type : ∀ i t, r.IsTeich t → ∀ u, ∃ g : GL (Fin n) K, ∀ y ∈ F.Iu u,
      ((g * ρ i y * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun j => algebraMap O K (t j y))
    (unr : r.V0ok → ∀ i, ∀ g ∈ F.I0, ρ i g = 1)
    (hT : ∃ t, r.IsTeich t ∧ ∀ i g, r.chib i g = 1 → t i g = 1)
    (fin : ((Ideal.Quotient.mk J).comp (Λ.toPair B.u : Λ.Λ →+* B.B)).Finite)
    (tf : ∀ a : Λ.Λ, a ≠ 0 → ∀ b : B.B, Λ.toPair B.u a * b ∈ J → b ∈ J) : B.RingProps Λ J := by
  let f : ι → (B.B ⧸ J) →ₐ[O] K := fun i => Ideal.Quotient.liftₐ J (x i) (hJ i)
  have hf : ∀ i, (f i : B.B ⧸ J →+* K).comp (Ideal.Quotient.mk J) = x i := fun i => rfl
  have hinj : ∀ a, (∀ i, f i a = 0) → a = 0 := fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 (sep b ha)
  have hD' : ∀ i, (B.DD J).map (f i : B.B ⧸ J →+* K) = GDet.ofRep (mat (ρ i)) := fun i => by
    rw [UniversalOrdinaryDeterminantRing.DD, (UpperTheory.V.AlgebraTools.Det.mapApi B.u.D _).2.2.2.2.2.2.1, hf, hD]
  have hflag : ∀ i v, HasFlag ((ρ i).comp (F.φ v)) fun j => pushCh (f i : B.B ⧸ J →+* K) (B.psiT J v j) := flag
  have hP : F.IsPolar O (B.DD J) := UpperTheory.V.AlgebraTools.Det.polarInj F O _ n _ (fun _ => K) f hinj fun i => by
    obtain ⟨P, hP⟩ := form i
    rw [hD' i]
    exact (UpperTheory.V.AlgebraTools.Det.formRep F O K n (ρ i) P hP).2.2
  have hker : ∀ g, (∀ i, ρ i g = 1) → (B.DD J).Kills (MonoidAlgebra.single g 1 - 1) ∧
      (B.DD J).Kills (F.star O _ n (MonoidAlgebra.single g 1) - 1) := fun g hg => by
    have hk : (B.DD J).Kills (MonoidAlgebra.single g 1 - 1) := by
      refine UpperTheory.V.AlgebraTools.Det.kerTest (fun _ => K) (fun i => (f i : B.B ⧸ J →+* K)) (fun i => mat (ρ i)) _ hinj hD' _ fun i => ?_
      rw [map_sub, map_sub, map_one, map_one, MonoidAlgebra.mapRingHom_single, map_one]
      simp [GDet.repAlg, mat, hg i]
    refine ⟨hk, ?_⟩
    have h1 := UpperTheory.V.AlgebraTools.Det.killsStar F O _ n _ hP _ hk
    have h2 : F.star O (B.B ⧸ J) n (MonoidAlgebra.single g 1 - 1) = F.star O _ n (MonoidAlgebra.single g 1) - 1 := by
      simp [GFrame.star]
    rwa [h2] at h1
  refine ⟨fin, tf, hP, fun v g => ?_, fun v g => ?_, fun u g hg => hker g fun i => ?_, fun t ht u => ?_,
    fun h g hg => hker g fun i => unr h i g hg⟩
  · ext k
    rw [← sub_eq_zero]
    apply hinj
    intro i
    have h1 := (UpperTheory.V.AlgebraTools.Det.mapApi (B.DD J) (f i : B.B ⧸ J →+* K)).1 (MonoidAlgebra.single (F.φ v g) 1)
    rw [hD' i, MonoidAlgebra.mapRingHom_single, map_one, (UpperTheory.V.AlgebraTools.Det.repApi (mat (ρ i))).2.1] at h1
    have h2 := (UpperTheory.V.AlgebraTools.Det.flagRel _ _ (hflag i v)).1 g
    have h3 : mat ((ρ i).comp (F.φ v)) g = mat (ρ i) (F.φ v g) := rfl
    rw [h3, h1] at h2
    have h4 : (∏ j, (X - C ((B.psiT J v j g : (B.B ⧸ J)ˣ) : B.B ⧸ J))).map (f i : B.B ⧸ J →+* K) =
        ∏ j, (X - C ((pushCh (f i : B.B ⧸ J →+* K) (B.psiT J v j) g : Kˣ) : K)) := by
      rw [Polynomial.map_prod]
      simp
    have h5 := congrArg (fun p => p.coeff k) (h2.trans h4.symm)
    simp only [Polynomial.coeff_map] at h5
    rw [map_sub, sub_eq_zero]
    exact h5
  · have hk : (B.DD J).Kills (F.oEl v (B.psiT J v) g) := by
      refine UpperTheory.V.AlgebraTools.Det.kerTest (fun _ => K) (fun i => (f i : B.B ⧸ J →+* K)) (fun i => mat (ρ i)) _ hinj hD' _ fun i => ?_
      have h1 : MonoidAlgebra.mapRingHom F.G₀ (f i : B.B ⧸ J →+* K) (F.oEl v (B.psiT J v) g) =
          F.oEl v (fun j => pushCh (f i : B.B ⧸ J →+* K) (B.psiT J v j)) g := by
        unfold GFrame.oEl
        rw [map_list_prod, List.map_ofFn]
        congr 2
        funext j
        simp [pushCh]
      rw [h1]
      exact UpperTheory.V.AlgebraTools.Det.oElRep F O K n (ρ i) v _ (hflag i v) g
    exact ⟨hk, UpperTheory.V.AlgebraTools.Det.killsStar F O _ n _ hP _ hk⟩
  · obtain ⟨t, ht, ht1⟩ := hT
    obtain ⟨Q, hQ⟩ := type i t ht u
    have h1 := hQ g hg.1
    have h2 : ∀ j, t j g = 1 := fun j => ht1 j g (Subgroup.mem_iInf.1 hg.2 j)
    simp only [h2, Units.val_one, map_one, Matrix.diagonal_one] at h1
    have h3 : Q * ρ i g * Q⁻¹ = 1 := Units.ext h1
    simpa using h3
  · refine (UpperTheory.V.AlgebraTools.Det.injTest (fun _ => K) (fun i => (f i : B.B ⧸ J →+* K)) hinj).1 _ _ fun i => ?_
    obtain ⟨Q, hQ⟩ := type i t ht u
    have h1 : ((B.DD J).comap (F.Iu u).subtype).map (f i : B.B ⧸ J →+* K) =
        ((B.DD J).map (f i : B.B ⧸ J →+* K)).comap (F.Iu u).subtype := rfl
    rw [h1, hD', (UpperTheory.V.AlgebraTools.Det.repApi _).2.2.2.2.2.2.1, (UpperTheory.V.AlgebraTools.Det.repApi _).2.2.2.2.2.1]
    refine (UpperTheory.V.AlgebraTools.Det.repApi _).2.2.2.2.2.2.2 _ Q fun y => ?_
    have h2 : (RingHom.mapMatrix (f i : B.B ⧸ J →+* K)).toMonoidHom.comp
        (diagRep fun j => pushCh (algebraMap O (B.B ⧸ J)) ((t j).comp (F.Iu u).subtype)) y =
        Matrix.diagonal fun j => algebraMap O K (t j y) := by
      change (Matrix.diagonal _).map (f i) = _
      rw [Matrix.diagonal_map (map_zero _)]
      congr 1
      funext j
      exact (f i).commutes _
    rw [h2, ← hQ y y.2, ← Units.val_mul, inv_mul_cancel_right]
    rfl

private theorem jr_surj {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) {T : Type} [CommRing T] [Algebra O T] [Algebra Λ.Λ T] (f : B.B →ₐ[O] T)
    (hsurj : Function.Surjective f) (hlam : ∀ b, f (Λ.toPair B.u b) = algebraMap Λ.Λ T b) (K : Type) [CommRing K] [Algebra O K]
    (good : (T →ₐ[O] K) → Prop) (sep : ∀ t, (∀ x, good x → x t = 0) → t = 0)
    (pt : ∀ x, good x → ∃ ρ : F.G₀ →* GL (Fin n) K, (B.u.D.map f.toRingHom).map x.toRingHom = GDet.ofRep (mat ρ) ∧
      (∃ P, F.IsForm O n ρ P) ∧
      (∀ v, HasFlag (ρ.comp (F.φ v)) fun j => pushCh x.toRingHom (pushCh f.toRingHom (B.u.ψ v j))) ∧
      (∀ t, r.IsTeich t → ∀ u, ∃ g : GL (Fin n) K, ∀ y ∈ F.Iu u,
        ((g * ρ y * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal fun j => algebraMap O K (t j y)) ∧
      (r.V0ok → B.u.D.map (x.comp f : B.B →+* K) = GDet.ofRep (mat ρ) → ∀ g ∈ F.I0, ρ g = 1))
    (hT : ∃ t, r.IsTeich t ∧ ∀ i g, r.chib i g = 1 → t i g = 1) (hfin : (algebraMap Λ.Λ T).Finite)
    (htf : ∀ b : Λ.Λ, b ≠ 0 → ∀ t : T, algebraMap Λ.Λ T b * t = 0 → t = 0) : B.RingProps Λ (RingHom.ker f) := by
  choose ρ hD hform hfl hty hun using fun x : {x // good x} => pt x.1 x.2
  have hD' : ∀ x : {x // good x}, B.u.D.map (x.1.comp f : B.B →+* K) = GDet.ofRep (mat (ρ x)) := fun x => by
    rw [← hD x]
    exact ((UpperTheory.V.AlgebraTools.Det.mapApi B.u.D f.toRingHom).2.2.2.2.2.2.1 x.1.toRingHom).symm
  refine jr_abs B Λ _ K (fun x : {x // good x} => x.1.comp f) (fun x b hb => ?_) (fun b hb => ?_) ρ hD' hform hfl hty
    (fun h x => hun x h (hD' x)) hT ?_ ?_
  · rw [AlgHom.comp_apply, (RingHom.mem_ker).1 hb, map_zero]
  · exact sep (f b) fun x hx => hb ⟨x, hx⟩
  · let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
    have he : (Ideal.Quotient.mk (RingHom.ker f)).comp (Λ.toPair B.u : Λ.Λ →+* B.B) =
        (e.symm : T →+* B.B ⧸ RingHom.ker f).comp (algebraMap Λ.Λ T) := by
      refine RingHom.ext fun b => ?_
      change _ = e.symm (algebraMap Λ.Λ T b)
      rw [AlgEquiv.eq_symm_apply, ← hlam]
      rfl
    rw [he]
    exact (RingHom.Finite.of_surjective _ e.symm.surjective).comp hfin
  · intro a ha b hb
    refine htf a ha (f b) ?_
    rw [← hlam, ← map_mul]
    exact hb

end Abstract

end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UpU
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [local instance 2000] UpperTheory.V.W.coefLocal
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.upU :
    Af.HypothesesH → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : HD Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → ∀ (x : B.Pt) (h : s.Wt n) (lam : Wt L l n), x.Arith h → WtOf h lam → ∀ (σ : Submodule ℂ (UA L n → ℂ)) (ρ : G L Ω →* GL (Fin n) (Qbar l)), IsAutRepU σ → Continuous ρ → Formalism.MainNotions.N.IsSSRep ρ → x.IsRep ρ → (∀ w, IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → Af.LocGlob ι ρ w τ) → (∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual) → (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsUnramU σ w) → (∃ τ : SmIrr (GLw n (s.w s.v0)), IsCompAlong σ (locU n (s.w s.v0)) ((cLoc (s.w s.v0)).comp (locU n (s.w s.v0)).subtype) τ.ρ ∧ fixd τ.ρ (Kc _ n 1) ≠ ⊥) → (∀ v : V.frame.Vl, ∃ (τ : SmIrr (GLw n (s.w v.1))) (ω : Fin n → ((s.w v.1).adicCompletion L)ˣ →* ℂˣ), IsCompAlong σ (locU n (s.w v.1)) ((cLoc (s.w v.1)).comp (locU n (s.w v.1)).subtype) τ.ρ ∧ Nonempty (τ.ρ.Equiv (PS ω)) ∧ ∀ i, OrdChar ι (artOf (s.hw v.1)) (ω i) (htW lam i) (x.psi v i)) → J ≤ RingHom.ker x := by
  exact UpperTheory.V.Hi.Up.main
end

