module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
public import GroundTheory.GlobalFields.CompletionAtPlace.Galois
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0762

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.LocCompROfAdmissibleReal
section
noncomputable section

namespace GlobalTheory.RealGal.LocCompRProof

open NumberField IsDedekindDomain Formalism.L2.Host Matrix GlobalTheory.PRep GlobalTheory.CuspRep.LocEx
open GlobalTheory.CuspRep (SmIrr Af locGL pLoc finGL)

section Gen

variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V]

def orb (κ : Representation ℂ K V) (x : V) : (K →₀ ℂ) →ₗ[ℂ] V := Finsupp.linearCombination ℂ fun k => κ k x

theorem orb_comm (κ : Representation ℂ K V) (T : Module.End ℂ V) (hT : ∀ k x, T (κ k x) = κ k (T x)) (x : V)
    (c : K →₀ ℂ) : orb κ (T x) c = T (orb κ x c) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hT]

theorem orb_act (κ : Representation ℂ K V) (x : V) (k : K) (c : K →₀ ℂ) :
    orb κ x (c.mapDomain (k * ·)) = κ k (orb κ x c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' h h' => rw [Finsupp.mapDomain_add, map_add (f := _), map_add (f := _), map_add (f := _), h, h']
  | single a b => simp [orb]

def annPart (κ : Representation ℂ K V) (φ : V) : Submodule ℂ V where
  carrier := {x | ∀ c, orb κ φ c = 0 → orb κ x c = 0}
  add_mem' := fun {x y} hx hy c hc => by
    have : orb κ (x + y) c = orb κ x c + orb κ y c := by
      simp only [orb, Finsupp.linearCombination_apply, Finsupp.sum, map_add (f := _), smul_add, Finset.sum_add_distrib]
    rw [this, hx c hc, hy c hc, add_zero]
  zero_mem' := fun c _ => by simp [orb, Finsupp.linearCombination_apply, Finsupp.sum]
  smul_mem' := fun a x hx c hc => by
    have := orb_comm κ (a • (1 : Module.End ℂ V)) (fun k x => by simp) x c
    simpa [hx c hc] using this

theorem exists_type (κ : Representation ℂ K V) (φ : V)
    (hφ : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => κ k φ))) :
    ∃ (d : ℕ) (ξ : K →* Matrix (Fin d) (Fin d) ℂ), ∀ x ∈ annPart κ φ, ∃ f : (Fin d → ℂ) →ₗ[ℂ] V,
      (∀ k v, f (ξ k *ᵥ v) = κ k (f v)) ∧ x ∈ LinearMap.range f ∧ ∀ v, ∃ c, f v = orb κ x c := by
  have hO : ∀ k, ∀ y ∈ LinearMap.range (orb κ φ), κ k y ∈ LinearMap.range (orb κ φ) := by
    rintro k _ ⟨c, rfl⟩
    exact ⟨_, orb_act κ φ k c⟩
  haveI : FiniteDimensional ℂ (LinearMap.range (orb κ φ)) := by
    rw [orb, Finsupp.range_linearCombination]; exact hφ
  let b := Module.finBasis ℂ (LinearMap.range (orb κ φ))
  obtain ⟨s, hs⟩ := (orb κ φ).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
  refine ⟨_, (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO), fun x hx => ?_⟩
  have key : ∀ c, orb κ x (s ((orb κ φ).rangeRestrict c)) = orb κ x c := fun c => by
    rw [← sub_eq_zero, ← map_sub]
    refine hx _ ?_
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val (LinearMap.congr_fun hs ((orb κ φ).rangeRestrict c))
  refine ⟨orb κ x ∘ₗ s ∘ₗ b.equivFun.symm.toLinearMap, fun k v => ?_,
    ⟨b.equivFun ((orb κ φ).rangeRestrict (Finsupp.single 1 1)), ?_⟩, fun v => ⟨_, rfl⟩⟩
  · obtain ⟨y, rfl⟩ := b.equivFun.surjective v
    obtain ⟨c, rfl⟩ := (orb κ φ).surjective_rangeRestrict y
    have h1 : (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp (sub κ _ hO) k *ᵥ b.equivFun ((orb κ φ).rangeRestrict c) =
        b.equivFun ((orb κ φ).rangeRestrict (c.mapDomain (k * ·))) := by
      have h2 : (orb κ φ).rangeRestrict (c.mapDomain (k * ·)) = sub κ _ hO k ((orb κ φ).rangeRestrict c) :=
        Subtype.ext (orb_act κ φ k c)
      rw [h2]
      exact LinearMap.toMatrix_mulVec_repr b b _ _
    rw [h1]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key, orb_act]
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, key]
    simp [orb]

end Gen

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ}

theorem smooth_fin (π : UpperTheory.V.TR.CuspSub F n) : IsSmooth π.finPart := fun v => by
  convert (π.cusp v.1 v.2).1.level using 1
  ext k
  exact Subtype.ext_iff

theorem smooth_loc (π : UpperTheory.V.TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) : IsSmooth (π.locRep w) := fun v =>
  (smooth_fin π v).preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)

theorem cpt_fin (π : UpperTheory.V.TR.CuspSub F n) (k : UpperTheory.V.TR.Kinf F n) (g : GL (Fin n) (Af F)) (y : π.V) :
    π.op (.cpt k) (π.finPart g y) = π.finPart g (π.op (.cpt k) y) := by
  refine Subtype.ext ?_
  change (UpperTheory.V.TR.rt F n (UpperTheory.V.TR.infGL F n (Unitary.toUnits k)) * UpperTheory.V.TR.rt F n (finGL F n g)) y.1 =
    (UpperTheory.V.TR.rt F n (finGL F n g) * UpperTheory.V.TR.rt F n (UpperTheory.V.TR.infGL F n (Unitary.toUnits k))) y.1
  rw [← map_mul, ← map_mul, UpperTheory.V.TR.infGL_comm]

theorem fin_loc (π : UpperTheory.V.TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) {k : GL (Fin n) (Af F)}
    (hk : GeneralLinearGroup.map (pLoc F w) k = 1) (g : GL (Fin n) (w.adicCompletion F)) (y : π.V) :
    π.finPart k (π.locRep w g y) = π.locRep w g (π.finPart k y) := by
  simp only [UpperTheory.V.TR.CuspSub.locRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, GlobalTheory.CuspRep.LocUniq.comm_locGL w hk]

theorem bot_or_top (π : UpperTheory.V.TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) (W : Submodule ℂ π.V)
    (h1 : ∀ g, ∀ x ∈ W, π.locRep w g x ∈ W)
    (h2 : ∀ T : Module.End ℂ π.V, (∀ g x, T (π.locRep w g x) = π.locRep w g (T x)) → ∀ x ∈ W, T x ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have hi := Submodule.map_injective_of_injective π.V.injective_subtype
  have hop : ∀ o, ∀ x ∈ W, π.op o x ∈ W := fun o x hx => by
    cases o with
    | fin k =>
      have h3 := h1 (GeneralLinearGroup.map (pLoc F w) k) _ (h2
        (π.finPart ((locGL F n w (GeneralLinearGroup.map (pLoc F w) k))⁻¹ * k))
        (fin_loc π w (map_pLoc_inv_mul w k)) x hx)
      rwa [UpperTheory.V.TR.CuspSub.locRep, MonoidHom.comp_apply, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at h3
    | cpt k => exact h2 _ (fun g y => cpt_fin π k _ y) x hx
    | lie X => exact h2 _ (fun g y => Subtype.ext (LinearMap.congr_fun (UpperTheory.V.TR.lie_rt_fin X (locGL F n w g)) y.1)) x hx
  rcases π.irred (W.map π.V.subtype) (Submodule.map_subtype_le _ _) (by
    rintro o _ ⟨x, hx, rfl⟩
    exact ⟨_, hop o x hx, rfl⟩) with h | h
  · exact Or.inl (hi (h.trans (Submodule.map_bot _).symm))
  · exact Or.inr (hi (h.trans (Submodule.map_subtype_top _).symm))

theorem isotypic (π : UpperTheory.V.TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) (σ : SmIrr (GL (Fin n) (w.adicCompletion F)))
    (h : π.IsLocComp w σ) : UpperTheory.V.Af.LocIsotypic π.finPart w σ := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 π.ne_bot, ?_⟩
  refine (bot_or_top π w _ (fun g x hx => ?_) (fun T hT x hx => ?_)).resolve_left fun e => ?_
  · refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap (π.locRep w g) _) fun f => ?_) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem f ⟨σ.ρ g v, f.2 g v⟩
  · refine Submodule.mem_comap.1 ((iSup_le (a := Submodule.comap T _) fun f => ?_) hx)
    rintro _ ⟨v, rfl⟩
    exact Submodule.mem_iSup_of_mem ⟨T ∘ₗ f.1, fun g v => by
      rw [LinearMap.comp_apply, f.2]; exact hT g _⟩ ⟨v, rfl⟩
  · obtain ⟨f, h0, hf⟩ := h
    exact h0 (LinearMap.range_eq_bot.1 ((iSup_eq_bot.1 e) ⟨f, hf⟩))

def cptPart (π : UpperTheory.V.TR.CuspSub F n) : Representation ℂ (UpperTheory.V.TR.Kinf F n) π.V :=
  sub (UpperTheory.V.TR.cptRep F n) π.V fun k => π.stable (.cpt k)

theorem exists_comp (h : UpperTheory.V.Published.AdmissibleReal) (π : UpperTheory.V.TR.CuspSub F n) (w : HeightOneSpectrum (𝓞 F)) :
    ∃ σ, π.IsLocComp w σ := by
  obtain ⟨φ₀, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  set φ : π.V := ⟨φ₀, hφ⟩
  have h0' : φ ≠ 0 := fun e => h0 (congrArg Subtype.val e)
  set L := stab π.finPart φ
  have hL : IsOpen (L : Set (GL (Fin n) (Af F))) := smooth_fin π _
  obtain ⟨K, ho, hc, hK⟩ := exists_compact_open w _ hL
  have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptPart π k φ)) := by
    have := (π.cusp φ₀ hφ).1.kfin
    refine FiniteDimensional.of_injective ((π.V.subtype ∘ₗ Submodule.subtype _).codRestrict
      (Submodule.span ℂ (Set.range fun k => UpperTheory.V.TR.cptRep F n k φ₀)) fun v => ?_)
      fun v v' e => Subtype.ext (Subtype.ext (by have e' := congrArg Subtype.val e; exact e'))
    refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap π.V.subtype _)).2 ?_ v.2)
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨k, rfl⟩
  obtain ⟨d, ξ, hξ⟩ := exists_type (cptPart π) φ hfd
  have hcomm : ∀ g k x, π.finPart g (cptPart π k x) = cptPart π k (π.finPart g x) := fun g k x => (cpt_fin π k g x).symm
  let U : Submodule ℂ π.V := annPart (cptPart π) φ ⊓
    fixed π.finPart (L ⊓ (GeneralLinearGroup.map (n := Fin n) (pLoc F w)).ker)
  obtain ⟨σ, hσ, -⟩ := exists_irred (smooth_loc π w) ho (fun W hW e => by
      rcases bot_or_top π w (nullPart (π.locRep w) K) (fun g x hx => nullPart_act _ K g hx)
        (fun T hT x hx => nullPart_comm _ K T hT hx) with h2 | h2
      · exact le_bot_iff.1 (h2 ▸ le_nullPart (smooth_loc π w) hc W hW e)
      · exact absurd (eq_zero_of_mem_nullPart (smooth_loc π w) hc (mem_fix.2 hK) (h2 ▸ Submodule.mem_top)) h0')
    U (fun g x hx => ⟨fun c hc => by
        rw [UpperTheory.V.TR.CuspSub.locRep, MonoidHom.comp_apply, orb_comm _ _ (hcomm _), hx.1 c hc, map_zero],
      mem_fix.2 fun k hk => by rw [fin_loc π w hk.2, mem_fix.1 hx.2 k hk]⟩)
    ((Submodule.ne_bot_iff _).2 ⟨φ, ⟨fun _ hc => hc, mem_fix.2 fun k hk => hk.1⟩, h0'⟩) (fun K' hK' => by
      obtain ⟨W, hW, hWf⟩ := h F n π (L ⊓ (K' ⊓ L.comap (locGL F n w)).comap (GeneralLinearGroup.map (pLoc F w)))
        (hL.inter ((hK'.inter (hL.preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w))).preimage
          (continuous_map_pLoc w))) d ξ
      refine Submodule.finiteDimensional_of_le (S₂ := W) fun x hx => ?_
      obtain ⟨f, hf, hx1, hf2⟩ := hξ x hx.1.1
      refine hWf f hf (fun k hk v => ?_) hx1
      have h1 := mem_fix.1 hx.1.2 _ ⟨L.mul_mem (L.inv_mem hk.2.2) hk.1, map_pLoc_inv_mul w k⟩
      have h2 := mem_fix.1 hx.2 _ hk.2.1
      have h3 : π.finPart k x = x := by
        rw [← mul_inv_cancel_left (locGL F n w (GeneralLinearGroup.map (pLoc F w) k)) k, map_mul,
          Module.End.mul_apply, h1]
        exact h2
      obtain ⟨c, hc⟩ := hf2 v
      rw [hc, ← orb_comm _ _ (hcomm k), h3])
  exact ⟨σ, hσ⟩

end GlobalTheory.RealGal.LocCompRProof

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.RealGal.locCompR_of_admissibleReal : AdmissibleReal → LocCompR := fun h _ _ _ _ _ π w =>
  ⟨GlobalTheory.RealGal.LocCompRProof.exists_comp h π w, GlobalTheory.RealGal.LocCompRProof.isotypic π w⟩

end
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RamificationIdxEqOneAndInertiaDegEqOne
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PlaceIsoDec

open scoped Pointwise

theorem exists_isPlaceOver_mid {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 L), IsPlaceOver A w := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω (x : L) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap L Ω (x : L)) :=
      (x.isIntegral_coe.map (algebraMap L Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  let P : Ideal (𝓞 L) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω (x : L)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.under (𝓞 K) := by
    ext x
    rw [← hA x, Ideal.under, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply K L Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP⟩

theorem liesOver_of_isPlaceOver {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra K L] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
    (hv : IsPlaceOver A v) (hw : IsPlaceOver A w) : w.asIdeal.LiesOver v.asIdeal := by
  refine ⟨?_⟩
  ext x
  rw [← hv x, Ideal.under, Ideal.mem_comap, ← hw, IsScalarTower.algebraMap_apply K L Ω]
  rfl

theorem valuation_smul_lt_one_iff {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (σ : Ω ≃ₐ[F] Ω)
    (A : ValuationSubring Ω) (z : Ω) :
    (σ • A).valuation z < 1 ↔ A.valuation (σ.symm z) < 1 := by
  have hmem : ∀ y, y ∈ σ • A ↔ σ.symm y ∈ A := fun y => by
    conv_lhs => rw [show y = σ (σ.symm y) by simp]
    rw [← AlgEquiv.smul_def]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  rw [valuation_lt_one_iff', valuation_lt_one_iff', hmem, hmem, map_inv₀, map_eq_zero_iff _ σ.symm.injective]

end GlobalTheory.PlaceIsoDec

namespace GlobalTheory.PlaceIsoDec

open scoped Pointwise

variable {F K L Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra F K] [Algebra F L] [Algebra K L] [Algebra F Ω] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower F K L] [IsScalarTower F L Ω] [IsScalarTower K L Ω] [IsScalarTower F K Ω]

theorem fixes_of_mem_stabilizer [IsAlgClosure F Ω] [IsAlgClosure L Ω]
    {A : ValuationSubring Ω} {P : HeightOneSpectrum (𝓞 L)} (hP : IsPlaceOver A P)
    (hD : Dec (F := F) A ≤ (res F Ω K).range)
    (τ : L ≃ₐ[F] L) (hτ : τ • P.asIdeal = P.asIdeal) (x : K) :
    τ (algebraMap K L x) = algebraMap K L x := by
  haveI : Normal F Ω := IsAlgClosure.normal F Ω
  set σ : Ω ≃ₐ[F] Ω := τ.liftNormal Ω with hσ
  have hσL : ∀ y : L, σ (algebraMap L Ω y) = algebraMap L Ω (τ y) := fun y =>
    AlgEquiv.liftNormal_commutes τ Ω y
  have hσL' : ∀ y : L, σ.symm (algebraMap L Ω y) = algebraMap L Ω (τ.symm y) := fun y => by
    rw [AlgEquiv.symm_apply_eq, hσL, AlgEquiv.apply_symm_apply]
  have hσA : IsPlaceOver (σ • A) P := fun y => by
    rw [valuation_smul_lt_one_iff, hσL', ← hτ, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    exact hP (τ⁻¹ • y)
  obtain ⟨ρ, hρ⟩ := exists_smul_eq_of_isPlaceOver (F := L) hσA hP
  set g : Ω ≃ₐ[F] Ω := ρ.restrictScalars F * σ with hg
  have hgA : g ∈ Dec (F := F) A := by
    show g • A = A
    rw [hg, mul_smul]
    exact hρ
  obtain ⟨h, hh⟩ := hD hgA
  have e1 : g (algebraMap K Ω x) = algebraMap K Ω x := by
    rw [← hh]
    exact h.commutes x
  have e2 : g (algebraMap K Ω x) = algebraMap L Ω (τ (algebraMap K L x)) := by
    rw [IsScalarTower.algebraMap_apply K L Ω]
    show ρ (σ (algebraMap L Ω _)) = _
    rw [hσL]
    exact ρ.commutes _
  exact (algebraMap L Ω).injective (by rw [← e2, e1, IsScalarTower.algebraMap_apply K L Ω])

end GlobalTheory.PlaceIsoDec

namespace GlobalTheory.PlaceIsoDec

open scoped Pointwise

variable {F K L Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω]
    [Algebra F K] [Algebra F L] [Algebra K L] [Algebra F Ω] [Algebra K Ω] [Algebra L Ω]
    [IsScalarTower F K L] [IsScalarTower F L Ω] [IsScalarTower K L Ω] [IsScalarTower F K Ω]

theorem ramificationIdx_eq_one_and_inertiaDeg_eq_one [IsAlgClosure F Ω] [IsAlgClosure L Ω] [IsGalois F L]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 K)}
    {P : HeightOneSpectrum (𝓞 L)} (hv : IsPlaceOver A v) (hw : IsPlaceOver A w) (hP : IsPlaceOver A P)
    (hD : Dec (F := F) A ≤ (res F Ω K).range) :
    w.asIdeal.ramificationIdx (𝓞 F) = 1 ∧ w.asIdeal.inertiaDeg (𝓞 F) = 1 := by
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois F K L
  haveI : w.asIdeal.LiesOver v.asIdeal := liesOver_of_isPlaceOver hv hw
  haveI : P.asIdeal.LiesOver w.asIdeal := liesOver_of_isPlaceOver hw hP
  haveI : P.asIdeal.LiesOver v.asIdeal := liesOver_of_isPlaceOver hv hP
  have hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) P.asIdeal) =
      Nat.card (MulAction.stabilizer (L ≃ₐ[F] L) P.asIdeal) := by
    refine Nat.card_congr (Equiv.ofBijective
      (fun σ ↦ ⟨(σ : L ≃ₐ[K] L).restrictScalars F, σ.2⟩) ⟨?_, ?_⟩)
    · intro σ τ h
      exact Subtype.ext (AlgEquiv.restrictScalars_injective F (congrArg Subtype.val h))
    · rintro ⟨τ, hτ⟩
      have hfix := fixes_of_mem_stabilizer (K := K) hP hD τ hτ
      exact ⟨⟨{ τ.toRingEquiv with commutes' := hfix }, hτ⟩, Subtype.ext (AlgEquiv.ext fun _ ↦ rfl)⟩
  have h1 := GroundTheory.Global.card_decompositionGroup v P
  have h2 := GroundTheory.Global.card_decompositionGroup w P
  rw [hcard] at h2
  rw [Ideal.ramificationIdx_tower (R := 𝓞 F) w.asIdeal P.asIdeal,
    Ideal.inertiaDeg_tower (R := 𝓞 F) w.asIdeal P.asIdeal, h2] at h1
  have hpos : 0 < P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K) := by
    rw [← h2]
    exact Nat.card_pos
  have key : w.asIdeal.ramificationIdx (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 F) *
      (P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K)) =
      1 * (P.asIdeal.ramificationIdx (𝓞 K) * P.asIdeal.inertiaDeg (𝓞 K)) := by
    rw [one_mul]
    conv_rhs => rw [h1]
    ring
  exact mul_eq_one.1 (Nat.eq_of_mul_eq_mul_right hpos key)

end GlobalTheory.PlaceIsoDec

namespace GlobalTheory.PlaceIsoDec


open GroundTheory.Global.SemiLocal in
theorem exists_placeIso_of_dec_le_range : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → Dec (F := F) A ≤ (res F Ω K).range → ∃ (w : HeightOneSpectrum (𝓞 K)) (_ : IsPlaceOver A w) (i : v.adicCompletion F ≃+* w.adicCompletion K), PlaceIso A v A w (RingEquiv.refl Ω) (algebraMap F K) i := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ v A hv hD
  obtain ⟨w, hw⟩ := GlobalTheory.PlaceIsoDec.exists_isPlaceOver_mid (L := K) hv
  haveI : Module.Finite F K := Module.Finite.of_restrictScalars_finite ℚ F K
  haveI : NumberField (IntermediateField.normalClosure F K Ω) := NumberField.of_module_finite F (IntermediateField.normalClosure F K Ω)
  haveI : IsAlgClosure (IntermediateField.normalClosure F K Ω) Ω :=
    ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.tower_top (K := F) (IntermediateField.normalClosure F K Ω)⟩
  obtain ⟨P, hP⟩ := GlobalTheory.PlaceIsoDec.exists_isPlaceOver_mid (L := IntermediateField.normalClosure F K Ω) hv
  obtain ⟨he, hf⟩ := GlobalTheory.PlaceIsoDec.ramificationIdx_eq_one_and_inertiaDeg_eq_one (K := K) hv hw hP hD
  haveI : w.asIdeal.LiesOver v.asIdeal := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hv hw
  have hrank : Module.finrank (v.adicCompletion F) (w.adicCompletion K) = 1 := by
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg K v w, he, hf]
  have hsurj : Function.Surjective (completionMap v w) := by
    intro y
    have hy : y ∈ (⊥ : Subalgebra (v.adicCompletion F) (w.adicCompletion K)) := by
      rw [Subalgebra.bot_eq_top_of_finrank_eq_one hrank]
      trivial
    obtain ⟨x, hx⟩ := Algebra.mem_bot.1 hy
    exact ⟨x, hx⟩
  refine ⟨w, hw, RingEquiv.ofBijective (completionMap v w) ⟨(completionMap v w).injective, hsurj⟩,
    ⟨fun _ => Iff.rfl, fun x => IsScalarTower.algebraMap_apply F K Ω x, continuous_completionMap v w, fun x => ?_⟩⟩
  exact (completionMap_algebraMap v w x).trans (IsScalarTower.algebraMap_apply F K _ x)

end GlobalTheory.PlaceIsoDec
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RecAlgNormDiag
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
open Polynomial

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SatFrobLit

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem val_inv_eq (n : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((1 - (n : ℝ)) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (a : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, mul_comm]
  congr 2
  push_cast
  ring

end GlobalTheory.SatFrobLit


end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.SymmMultisetCentreUnique
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Glob

theorem symm_multiset_centre_unique : ∀ (s : Multiset ℤ) (x y : ℤ), s ≠ 0 → s = s.map (x - ·) → s = s.map (y - ·) → x = y := by
  intro s x y hs hx hy
  have key : ∀ z : ℤ, s = s.map (z - ·) → 2 * s.sum = (Multiset.card s : ℤ) * z := by
    intro z hz
    have h1 : (s.map (z - ·)).sum = (Multiset.card s : ℤ) * z - s.sum := by
      rw [Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, Multiset.map_id']
      simp [nsmul_eq_mul]
    have h2 : s.sum = (Multiset.card s : ℤ) * z - s.sum := by
      conv_lhs => rw [hz]
      exact h1
    linarith
  have hc : (Multiset.card s : ℤ) ≠ 0 := by
    exact_mod_cast (mt Multiset.card_eq_zero.mp hs)
  have := (key x hx).symm.trans (key y hy)
  exact mul_left_cancel₀ hc this

end GlobalTheory.Glob
end

