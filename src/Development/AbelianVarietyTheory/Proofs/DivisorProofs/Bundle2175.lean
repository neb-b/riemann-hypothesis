module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2125
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1952
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueElemOfNaturalFamilyOpenCoverPoints
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt.NatGlue

variable (R : Type) [CommRing R] {D : Type} [CommRing D] [Algebra R D]

def locMap (s : D) : D →ₐ[R] Localization.Away s := IsScalarTower.toAlgHom R D _

theorem locMap_apply (s x : D) : locMap R s x = algebraMap D (Localization.Away s) x := rfl

def locR (a b : D) : Localization.Away a →ₐ[R] Localization.Away (a * b) :=
  ⟨IsLocalization.Away.awayToAwayRight a b, fun r ↦ by
    have := IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away a) (P := Localization.Away (a * b))
      a b (algebraMap R D r)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact this⟩

def locL (a b : D) : Localization.Away b →ₐ[R] Localization.Away (a * b) :=
  ⟨IsLocalization.Away.awayToAwayLeft b a, fun r ↦ by
    have := IsLocalization.Away.awayToAwayLeft_eq (S := Localization.Away b) (P := Localization.Away (a * b))
      b a (algebraMap R D r)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    exact this⟩

theorem locR_apply (a b : D) (x : Localization.Away a) :
    locR R a b x = IsLocalization.Away.awayToAwayRight a b x := rfl

theorem locL_apply (a b : D) (x : Localization.Away b) :
    locL R a b x = IsLocalization.Away.awayToAwayLeft b a x := rfl

theorem locR_comp (a b : D) : (locR R a b).comp (locMap R a) = locMap R (a * b) := by
  ext x
  rw [AlgHom.comp_apply, locR_apply, locMap_apply, locMap_apply]
  exact IsLocalization.Away.awayToAwayRight_eq a b x

theorem locL_comp (a b : D) : (locL R a b).comp (locMap R b) = locMap R (a * b) := by
  ext x
  rw [AlgHom.comp_apply, locL_apply, locMap_apply, locMap_apply]
  exact IsLocalization.Away.awayToAwayLeft_eq b a x

theorem awayMap_comp {E : Type} [CommRing E] [Algebra R E] (φ : D →ₐ[R] E) (s : D) :
    (IsScalarTower.toAlgHom R E (Localization.Away (φ s))).comp φ = (Localization.awayMapₐ φ s).comp (locMap R s) := by
  ext x
  rw [AlgHom.comp_apply, AlgHom.comp_apply, IsScalarTower.toAlgHom_apply, locMap_apply]
  first
    | exact (IsLocalization.Away.map_eq (S := Localization.Away s) (P := Localization.Away (φ s)) s x).symm
    | simp [Localization.awayMapₐ, IsLocalization.Away.mapₐ, IsLocalization.Away.map, IsLocalization.map_eq]
    | (show _ = IsLocalization.map _ (φ : D →+* E) _ _; exact (IsLocalization.map_eq _ _).symm)

theorem existsUnique_of_natural : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
    ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (y : Pt X D)
    (τ : ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E),
    (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E)
      (θ : E →ₐ[R] E'), Sm W (D := E) (spOver ψ ≫ y) → τ E' (θ.comp ψ) = θ (τ E ψ)) →
    ∃! d : D, ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      Sm W (D := E) (spOver ψ ≫ y) → τ E ψ = ψ d := by
  intro R _ X K W hW D _ _ y τ hτ

  let S : Set D := {s | ∃ i, ∀ p : PrimeSpectrum D, p ∈ PrimeSpectrum.basicOpen s → y.left.base p ∈ W i}
  have hS : Ideal.span S = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff', eq_top_iff]
    intro p _
    have hp : y.left.base p ∈ ⨆ i, W i := by rw [hW]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
    obtain ⟨_, ⟨s, rfl⟩, hps, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (a := p) (u := (y.left ⁻¹ᵁ W i).carrier) hi (y.left ⁻¹ᵁ W i).isOpen
    simp only [TopologicalSpace.Opens.mem_iSup]
    exact ⟨s, ⟨i, fun q hq ↦ hsub hq⟩, hps⟩
  have hψ : ∀ s ∈ S, Sm W (D := Localization.Away s) (spOver (locMap R s) ≫ y) := by
    rintro s ⟨i, hi⟩
    refine ⟨i, fun q _ ↦ hi _ ?_⟩
    show PrimeSpectrum.comap (algebraMap D (Localization.Away s)) q ∈ PrimeSpectrum.basicOpen s
    rw [PrimeSpectrum.mem_basicOpen]
    intro h
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit s))
  have hcomp : ∀ a b : S,
      IsLocalization.Away.awayToAwayRight (P := Localization.Away (a.1 * b.1)) a.1 b.1 (τ (Localization.Away a.1) (locMap R a.1)) =
      IsLocalization.Away.awayToAwayLeft (P := Localization.Away (a.1 * b.1)) b.1 a.1 (τ (Localization.Away b.1) (locMap R b.1)) := by
    intro a b
    have h1 := hτ _ _ (locMap R a.1) (locR R a.1 b.1) (hψ a.1 a.2)
    have h2 := hτ _ _ (locMap R b.1) (locL R a.1 b.1) (hψ b.1 b.2)
    rw [locR_comp] at h1
    rw [locL_comp] at h2
    rw [← locR_apply R, ← locL_apply R, ← h1, ← h2]
  obtain ⟨d, hd, hu⟩ := Localization.existsUnique_algebraMap_eq_of_span_eq_top S hS
    (fun a ↦ τ (Localization.Away a.1) (locMap R a.1)) hcomp
  refine ⟨d, ?_, fun d' hd' ↦ hu d' fun a ↦ (hd' _ (locMap R a.1) (hψ a.1 a.2)).symm⟩
  intro E _ _ φ hφ
  have hS' : Ideal.span ((φ : D →+* E) '' S) = ⊤ := by
    rw [← Ideal.map_span, hS, Ideal.map_top]
  apply Localization.algebraMap_injective_of_span_eq_top _ hS'
  funext b
  obtain ⟨b, s, hs, rfl⟩ := b
  have h1 := hτ _ _ φ (IsScalarTower.toAlgHom R E (Localization.Away (φ s))) hφ
  have h2 := hτ _ _ (locMap R s) (Localization.awayMapₐ φ s) (hψ s hs)
  rw [awayMap_comp, h2, ← hd ⟨s, hs⟩, ← locMap_apply R, ← AlgHom.comp_apply, ← awayMap_comp] at h1
  exact h1.symm

end GlobalTheory.PtExt.NatGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.ThetaOne

open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

variable {V₁ : Type} [CommRing V₁] [IsDomain V₁]

abbrev toF (F : Type) [Field F] [Algebra (FractionRing V₁) F] : V₁ →+* F :=
  (algebraMap (FractionRing V₁) F).comp (algebraMap V₁ (FractionRing V₁))

theorem tF_hom (F : Type) [Field F] [Algebra (FractionRing V₁) F] :
    jFK (R := V₁) F ≫ jK V₁ = Spec.map (CommRingCat.ofHom (toF (V₁ := V₁) F)) := by
  rw [jFK, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem prB_hom' (D : DegPre V₁) (F : Type) [Field F] [Algebra (FractionRing V₁) F] :
    (DegPre.prB D F).left ≫ D.P.A.hom = famBase D F ≫ Spec.map (CommRingCat.ofHom (toF (V₁ := V₁) F)) := by
  rw [← tF_hom]
  exact (Over.w (DegPre.prB D F)).trans (Over.w (fst (TF (R := V₁) F) D.P.A)).symm

def termF (D : DegPre V₁) (F : Type) [Field F] [Algebra (FractionRing V₁) F] (k : ℕ) (α : D.X) :
    SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB α) (DegPre.famε k)) →ₛₗ[toF (V₁ := V₁) F] FamTerm D F k α :=
  pullOver D.P.L _ (prB_hom' D F) (famφ_prB D F α)

def pullTo (D : DegPre V₁) {R' : Type} [CommRing R'] (f : V₁ →+* R') :
    SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)) →ₛₗ[f]
      SecOver (fst (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left
        (LB.LinComb D.P.L (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ D.famφB 0 i)
          (DegPre.famε 1)) :=
  pullOver D.P.L _ ((Over.w (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A)).trans
    (Over.w (fst (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A)).symm) (fun _ => rfl)

theorem isPullSecLC_pullTo (D : DegPre V₁) {R' : Type} [CommRing R'] (f : V₁ →+* R')
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) :
    IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left
      θ (pullTo D f θ) := fun _ => rfl

abbrev OneBasisAt (D : DegPre V₁) {R' : Type} [CommRing R'] (f : V₁ →+* R')
    (θ' : LB.Sec (LB.LinComb D.P.L (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ D.famφB 0 i)
      (DegPre.famε 1))) : Prop :=
  IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.P.A) _ (fun _ : Fin 1 => θ')

theorem exists_theta [IsLocalRing V₁] (hV : IsCN V₁) (D : DegPre V₁) :
    ∃ θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)),
      ∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
        IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
        OneBasisAt D f θ' := by
  haveI : IsNoetherianRing V₁ := hV.1
  obtain ⟨m, b, hm, hb⟩ := GlobalTheory.twistBaseChange V₁ D 1 le_rfl 0
  obtain rfl : m = 1 := hm.trans (one_pow _)
  refine ⟨b 0, fun R' _ f θ' h => ?_⟩
  exact hb R' f (fun _ => θ') (fun i => by rw [Subsingleton.elim i 0]; exact h)

theorem exists_ne_zero (D : DegPre V₁) {K : Type} [Field K] (f : V₁ →+* K) θ' (h : OneBasisAt D f θ') :
    ∃ j, θ'.f j ≠ 0 := by
  by_contra hc
  push_neg at hc
  obtain ⟨r, -, hu⟩ := h θ'
  have h1 := hu (fun _ => 1) (fun j => by rw [Fin.sum_univ_one, map_one, map_one, _root_.one_mul])
  have h0 := hu (fun _ => 0) (fun j => by rw [Fin.sum_univ_one, map_zero, map_zero, MulZeroClass.zero_mul, hc j])
  have e10 := congrFun (h1.trans h0.symm) 0
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv e10
  simp at this

theorem basis_BF (D : DegPre V₁) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (hθ : ∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      OneBasisAt D f θ')
    (F : Type) [Field F] [Algebra (FractionRing V₁) F] :
    IsSecBasis (T := TF (R := V₁) F) (A := D.P.A) _
      (fun _ : Fin 1 => (termF D F 1 0 θ : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F 0) (DegPre.famε 1)))) := by
  have gen : ∀ (t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of V₁)), t = Spec.map (CommRingCat.ofHom (toF (V₁ := V₁) F)) →
      ∀ (hp : (snd (Over.mk t) D.P.A).left ≫ D.P.A.hom =
          (fst (Over.mk t) D.P.A).left ≫ Spec.map (CommRingCat.ofHom (toF (V₁ := V₁) F)))
        (φ : Fin 4 → ((Over.mk t ⊗ D.P.A).left ⟶ D.P.A.left))
        (hφ : ∀ i, φ i = (snd (Over.mk t) D.P.A).left ≫ D.famφB 0 i),
      IsSecBasis (T := Over.mk t) (A := D.P.A) _
        (fun _ : Fin 1 => (pullOver D.P.L (DegPre.famε 1) hp hφ θ : LB.Sec (LB.LinComb D.P.L φ (DegPre.famε 1)))) := by
    rintro t rfl hp φ hφ
    obtain rfl : φ = fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom (toF (V₁ := V₁) F)))) D.P.A).left ≫ D.famφB 0 i :=
      funext hφ
    exact hθ F (toF F) _ (isPullSecLC_pullTo D _ θ)
  exact gen _ (tF_hom F) (prB_hom' D F) _ (famφ_prB D F 0)

theorem existsUnique_scalar (D : DegPre V₁) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (hθ : ∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      OneBasisAt D f θ')
    (F : Type) [Field F] [Algebra (FractionRing V₁) F] (th : Fam D F 1) :
    ∃! c : F, famProj D F 1 0 th = c • termF D F 1 0 θ := by
  obtain ⟨r, hr, hu⟩ := basis_BF D θ hθ F (th.s 0)
  let e := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
  refine ⟨e (r 0), SecOps.sec_ext fun j => ?_, fun c hc => ?_⟩
  · refine (hr j).trans ?_
    rw [Fin.sum_univ_one]
    show _ = resTop _ ((famBase D F).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (e (r 0)))) * _
    rw [show (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (e (r 0)) = r 0 from e.symm_apply_apply (r 0)]
    rfl
  · have h2 := hu (fun _ => e.symm c) (fun j => by
      rw [Fin.sum_univ_one]
      exact congrArg (fun s : FamTerm D F 1 0 => LB.Sec.f s j) hc)
    have h3 := congrFun h2 0
    rw [← h3]
    exact (e.apply_symm_apply c).symm

theorem fe_from_zero (hG : GlobalFnsSt) (D : DegPre V₁) (F : Type) [Field F] [Algebra (FractionRing V₁) F]
    (th : Fam D F 1) (mu : D.X) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F 1 0 mu) (DegPre.deltaε 1)), u.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F 1 mu 0) ∧
      GeneratorPullback.SecRel D.P.L (DegPre.famφ D F (0 + 1 • mu)) (DegPre.famε 1) (th.s (0 + 1 • mu))
        (DegPre.famφ D F 0) (DegPre.famε 1) (th.s 0) (DegPre.trF D F mu).left
        (DegPre.deltaφ D F 1 0 mu) (DegPre.deltaε 1) u := by
  obtain ⟨u, hu, hc⟩ := (gen_fe (D := D) (F := F) hG 1 mu 0).1
  exact ⟨u, hu, hc, th.fe mu 0 u hu hc⟩

theorem eq_of_term_zero (hG : GlobalFnsSt) (D : DegPre V₁) (F : Type) [Field F] [Algebra (FractionRing V₁) F]
    {th th' : Fam D F 1} (h : th.s 0 = th'.s 0) : th = th' := by
  refine fam_ext fun β => ?_
  have key : ∀ x, x = 0 + 1 • β → ∀ j, (th.s x).f j = (th'.s x).f j := by
    rintro x rfl j
    have hL := D.P.isLB
    obtain ⟨u, hu, hc⟩ := (gen_fe (D := D) (F := F) hG 1 β 0).1
    refine sec_ext_val hL (fun y J hJ => ?_) j
    rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (th.fe β 0 u hu hc) _ _ y J hJ,
      (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (th'.fe β 0 u hu hc) _ _ y J hJ, h]
  exact key β (by rw [zero_add, one_smul])

theorem c_zero (D : DegPre V₁) : D.c 0 = (1 : 𝟙_ _ ⟶ D.P.A) := by
  have h := D.c_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem main [IsLocalRing V₁] (hV : IsCN V₁) (D : DegPre V₁) :
    ∃ θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)),
      (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
        IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
        OneBasisAt D f θ') ∧
      (∀ (K : Type) [Field K] (f : V₁ →+* K), ∃ j, (pullTo D f θ).f j ≠ 0) ∧
      (∀ (F : Type) [Field F] [Algebra (FractionRing V₁) F] (th : Fam D F 1),
        ∃! c : F, famProj D F 1 0 th = c • termF D F 1 0 θ) ∧
      (∀ (F : Type) [Field F] [Algebra (FractionRing V₁) F] (th : Fam D F 1) (mu : D.X),
        ∃ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F 1 0 mu) (DegPre.deltaε 1)), u.IsGen ∧
          LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F 1 mu 0) ∧
          GeneratorPullback.SecRel D.P.L (DegPre.famφ D F (0 + 1 • mu)) (DegPre.famε 1) (th.s (0 + 1 • mu))
            (DegPre.famφ D F 0) (DegPre.famε 1) (th.s 0) (DegPre.trF D F mu).left
            (DegPre.deltaφ D F 1 0 mu) (DegPre.deltaε 1) u) ∧
      (∀ (F : Type) [Field F] [Algebra (FractionRing V₁) F] (th th' : Fam D F 1), th.s 0 = th'.s 0 → th = th') := by
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  obtain ⟨θ, hθ⟩ := exists_theta hV D
  exact ⟨θ, hθ, fun K _ f => exists_ne_zero D f _ (hθ K f _ (isPullSecLC_pullTo D f θ)),
    fun F _ _ th => existsUnique_scalar D θ hθ F th, fun F _ _ th mu => fe_from_zero hG D F th mu,
    fun F _ _ _ _ h => eq_of_term_zero hG D F h⟩

end GlobalTheory.Poinc.ThetaOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueSimilitudeBetweenSymplecticLevels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.HTSympCover

open scoped TensorProduct

theorem piScalarRight_tmul_one {h M : ℕ} (a : Fin h ⊕ Fin h → ℤ) :
    TensorProduct.piScalarRight ℤ (ZMod M) (ZMod M) (Fin h ⊕ Fin h) ((1 : ZMod M) ⊗ₜ[ℤ] a) = reduceMod M a := by
  funext i
  simp [TensorProduct.piScalarRight_apply, reduceMod]

theorem omegaMod_reduceMod {h M : ℕ} (a c : Fin h ⊕ Fin h → ℤ) :
    omegaMod M (reduceMod M a) (reduceMod M c) = ((omegaStd a c : ℤ) : ZMod M) := by
  simp [omegaMod, omegaStd, reduceMod]

theorem sp_exists_spMap {A B : Type} [CommRing A] [CommRing B] (g : Sp B ⟶ Sp A) : ∃ f : A →+* B, g = spMap f :=
  ⟨(Spec.preimage g).hom, by simp [spMap]⟩

theorem sympCond_fibre_existsUnique : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ), 0 < M →
  Odd M → 1 ≤ h → ∀ (σ : sympSimGrp h M → (cycAway M →+* cycAway M)),
  (∀ a, ∃ n : ℕ, IsMultOf a n ∧ σ a (zetaAway M) = zetaAway M ^ n) →
  ∀ (S : Scheme.{0}) (t : S ⟶ Sp R) (o : Obj b N t) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S)
    (t₁ t₁' : Sp K ⟶ Sp (cycAway M)) (lv lv' : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ o.A)),
    SympCond o h M (Over.mk x) t₁ lv → SympCond o h M (Over.mk x) t₁' lv' →
    ∃! a : sympSimGrp h M, t₁ ≫ spMap (σ a) = t₁' ∧ ∀ c, sympTwist a lv c = lv' c := by
  intro p _ D R _ b N h M hM hodd hh σ hσ S t o K _ _ x t₁ t₁' lv lv' H H'
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨hadd, -, hgeo⟩ := H
  obtain ⟨hadd', -, hgeo'⟩ := H'
  obtain ⟨β, hβ⟩ := sp_exists_spMap t₁
  obtain ⟨β', hβ'⟩ := sp_exists_spMap t₁'
  have hζ : ∀ g₀ : cycAway M →+* K, g₀ (zetaAway M) ^ M = 1 := fun g₀ => by
    rw [← map_pow, zetaAway_pow_self M hM.ne', map_one]
  let z : Kˣ := Units.ofPowEqOne _ M (hζ β) hM.ne'
  let z' : Kˣ := Units.ofPowEqOne _ M (hζ β') hM.ne'
  obtain ⟨hk, hon, hW⟩ := hgeo K (𝟙 _) β z (by rw [Category.id_comp, hβ]) rfl
  obtain ⟨hk', hon', hW'⟩ := hgeo' K (𝟙 _) β' z' (by rw [Category.id_comp, hβ']) rfl
  let jx : Over.mk (𝟙 (Sp K) ≫ x) ⟶ Over.mk x := Over.homMk (𝟙 _) rfl
  have canc : ∀ f g : Over.mk x ⟶ o.A, jx ≫ f = jx ≫ g → f = g := by
    intro f g e
    apply Over.OverMorphism.ext
    have := congrArg CommaMorphism.left e
    simpa [jx] using this
  let φ : (Fin h ⊕ Fin h → ℤ) → (Over.mk (𝟙 (Sp K) ≫ x) ⟶ o.A) := fun a => jx ≫ lv a
  let φ' : (Fin h ⊕ Fin h → ℤ) → (Over.mk (𝟙 (Sp K) ≫ x) ⟶ o.A) := fun a => jx ≫ lv' a
  have hφ : ∀ a c, φ (a + c) = φ a * φ c := fun a c => by simp only [φ, hadd, MonObj.comp_mul]
  have hφ' : ∀ a c, φ' (a + c) = φ' a * φ' c := fun a c => by simp only [φ', hadd', MonObj.comp_mul]
  have hkφ : ∀ a, φ a = 1 ↔ ∃ c, a = M • c := fun a => hk a
  have hkφ' : ∀ a, φ' a = 1 ↔ ∃ c, a = M • c := fun a => hk' a
  have hr : ∀ b, ∃ c, φ c = φ' b := fun b => hon (φ' b) (by
    rw [← GlobalTheory.UPel.TensorTorsionNsmul.map_nsmul_of_add hφ', (hkφ' _).2 ⟨b, rfl⟩])
  have hr' : ∀ c, ∃ b, φ' b = φ c := fun c => hon' (φ c) (by
    rw [← GlobalTheory.UPel.TensorTorsionNsmul.map_nsmul_of_add hφ, (hkφ _).2 ⟨c, rfl⟩])
  obtain ⟨e, he⟩ := GlobalTheory.UPel.TensorTorsionNsmul.exists_equiv M φ φ' hφ hφ' hkφ hkφ' hr hr'
  let E := TensorProduct.piScalarRight ℤ (ZMod M) (ZMod M) (Fin h ⊕ Fin h)
  let e' := E.symm.trans (e.trans E)
  have he' : ∀ b c, e' (reduceMod M b) = reduceMod M c ↔ φ c = φ' b := by
    intro b c
    rw [← he, ← piScalarRight_tmul_one, ← piScalarRight_tmul_one]
    show E (e (E.symm (E _))) = E _ ↔ _
    rw [LinearEquiv.symm_apply_apply, E.injective.eq_iff]
  have hz : IsPrimitiveRoot z M := IsPrimitiveRoot.coe_units_iff.1 (isPrimitiveRoot_map hM.ne' β)
  obtain ⟨i, hcop, he_i⟩ := exists_pow_of_isLocalRing hM.ne' β β'
  have hzi : z ^ i = z' := Units.ext (by
    rw [Units.val_pow_eq_pow_val]
    exact he_i.symm)
  have h2u : IsUnit (2 : ZMod M) := by
    have := (ZMod.isUnit_iff_coprime 2 M).2 (Nat.coprime_two_left.2 hodd)
    exact_mod_cast this
  have hval : ∀ a b c d, φ c = φ' a → φ d = φ' b →
      ((omegaStd c d : ℤ) : ZMod M) = (i : ZMod M) * ((omegaStd a b : ℤ) : ZMod M) := by
    intro a b c d hc hd
    have w₁ := hW c d
    have w₂ := hW' a b
    change Out.WeilIs _ _ _ (φ' a) (φ' b) _ at w₂
    change Out.WeilIs _ _ _ (φ c) (φ d) _ at w₁
    rw [← hc, ← hd] at w₂
    have e₁ := H1.unitOn_injective
      (GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.globalFns_holds o.ab (pull_isLB o.isLB _) w₂ w₁)
    rw [← hzi, ← zpow_natCast, ← zpow_mul] at e₁
    have h2 : z ^ ((i : ℤ) * (2 * omegaStd a b) - 2 * omegaStd c d) = 1 := by
      rw [zpow_sub, e₁, mul_inv_cancel]
    rw [hz.zpow_eq_one_iff_dvd, ← ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    push_cast at h2
    have h3 : (2 : ZMod M) * ((i : ZMod M) * ((omegaStd a b : ℤ) : ZMod M) - ((omegaStd c d : ℤ) : ZMod M)) = 0 := by
      linear_combination h2
    have h4 := h2u.mul_right_eq_zero.1 h3
    linear_combination -h4
  have hmul : ∀ X Y, omegaMod M (e' X) (e' Y) = (i : ZMod M) * omegaMod M X Y := by
    intro X Y
    obtain ⟨a, rfl⟩ : ∃ a, reduceMod M a = X := ⟨liftMod X, reduceMod_liftMod X⟩
    obtain ⟨b, rfl⟩ : ∃ b, reduceMod M b = Y := ⟨liftMod Y, reduceMod_liftMod Y⟩
    obtain ⟨c, hc⟩ := hr a
    obtain ⟨d, hd⟩ := hr b
    rw [(he' a c).2 hc, (he' b d).2 hd, omegaMod_reduceMod, omegaMod_reduceMod]
    exact hval a b c d hc hd
  have hsim : e' ∈ sympSimGrp h M :=
    ⟨ZMod.unitOfCoprime i hcop, fun X Y => by rw [ZMod.coe_unitOfCoprime]; exact hmul X Y⟩
  let a₀ : sympSimGrp h M := ⟨e', hsim⟩
  have hmul₀ : IsMultOf a₀ i := hmul
  refine ⟨a₀, ⟨?_, fun c => canc _ _ ?_⟩, ?_⟩
  · obtain ⟨n, hn, hσn⟩ := hσ a₀
    have hni : (n : ZMod M) = i := isMultOf_unique hh hn hmul₀
    have hc : β.comp (σ a₀) = β' := cycAway_hom_ext hM.ne' (by
      rw [RingHom.comp_apply, hσn, zetaAway_pow_eq M hM.ne' hni, map_pow, he_i])
    rw [hβ, hβ', spMap, spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  · change φ (liftMod (e' (reduceMod M c))) = φ' c
    exact (he' c _).1 (reduceMod_liftMod _).symm
  · rintro a ⟨-, ha⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro X
    obtain ⟨b', rfl⟩ : ∃ b', reduceMod M b' = X := ⟨liftMod X, reduceMod_liftMod X⟩
    have h1 : φ (liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M b'))) = φ' b' :=
      congrArg (jx ≫ ·) (ha b')
    rw [← reduceMod_liftMod ((a : (Fin h ⊕ Fin h → ZMod M) ≃ₗ[ZMod M] (Fin h ⊕ Fin h → ZMod M)) (reduceMod M b'))]
    exact ((he' b' _).2 h1).symm

end GlobalTheory.HTSympCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorsFibreOverPointIffFactorsProduct
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

theorem factor_ker_iff {R : Type} [CommRing R] (A : Over (Sp R)) {T : Over (Sp R)} {V : Type} [CommRing V]
    (φ : Sp V ⟶ T.left) {H : Over (Sp R)} (h : H ⟶ A ⊗ T) (Y : Over (Sp V)) (x : Y ⟶ bc A φ) :
    (∃ y : Y ⟶ ker A φ h, y ≫ kerι A φ h = x) ↔
      ∃ z : up φ Y ⟶ H, z ≫ h = lift (upa φ x) (upt φ Y) := by
  constructor
  · rintro ⟨y, rfl⟩
    have hy : y.left ≫ pullback.snd (h ≫ snd A T).left φ = Y.hom := Over.w y
    have hT : (h ≫ snd A T).left ≫ T.hom = H.hom := Over.w _
    have hc : (y.left ≫ pullback.fst (h ≫ snd A T).left φ) ≫ (h ≫ snd A T).left = Y.hom ≫ φ := by
      rw [← hy]
      exact (Category.assoc _ _ _).trans
        ((congrArg (y.left ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
    refine ⟨Over.homMk (y.left ≫ pullback.fst (h ≫ snd A T).left φ) ?_, ?_⟩
    · show (y.left ≫ pullback.fst (h ≫ snd A T).left φ) ≫ H.hom = Y.hom ≫ φ ≫ T.hom
      rw [← hT, ← Category.assoc, hc, Category.assoc]
    · apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst, Category.assoc]
        apply Over.OverMorphism.ext
        have e : (kerι A φ h).left ≫ pullback.fst A.hom (φ ≫ T.hom)
            = pullback.fst (h ≫ snd A T).left φ ≫ (h ≫ fst A T).left := pullback.lift_fst _ _ _
        exact (Category.assoc _ _ _).trans
          ((congrArg (y.left ≫ ·) e.symm).trans (Category.assoc _ _ _).symm)
      · rw [lift_snd, Category.assoc]
        apply Over.OverMorphism.ext
        exact hc
  · rintro ⟨z, hz⟩
    have h1 : z ≫ h ≫ fst A T = upa φ x := by rw [← Category.assoc, hz, lift_fst]
    have h2 : z ≫ h ≫ snd A T = upt φ Y := by rw [← Category.assoc, hz, lift_snd]
    have h1' : z.left ≫ (h ≫ fst A T).left = x.left ≫ pullback.fst A.hom (φ ≫ T.hom) :=
      congrArg (·.left) h1
    have h2' : z.left ≫ (h ≫ snd A T).left = Y.hom ≫ φ := congrArg (·.left) h2
    let l : Y.left ⟶ pullback (h ≫ snd A T).left φ := pullback.lift z.left Y.hom h2'
    have l1 : l ≫ pullback.fst _ _ = z.left := pullback.lift_fst _ _ _
    have l2 : l ≫ pullback.snd _ _ = Y.hom := pullback.lift_snd _ _ _
    refine ⟨Over.homMk l l2, ?_⟩
    apply Over.OverMorphism.ext
    have e1 : (kerι A φ h).left ≫ pullback.fst A.hom (φ ≫ T.hom)
        = pullback.fst (h ≫ snd A T).left φ ≫ (h ≫ fst A T).left := pullback.lift_fst _ _ _
    have e2 : (kerι A φ h).left ≫ pullback.snd A.hom (φ ≫ T.hom)
        = pullback.snd (h ≫ snd A T).left φ := pullback.lift_snd _ _ _
    have hx : x.left ≫ pullback.snd A.hom (φ ≫ T.hom) = Y.hom := Over.w x
    apply pullback.hom_ext (f := A.hom) (g := φ ≫ T.hom)
    · refine (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) e1).trans ?_)
      refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (h ≫ fst A T).left) l1).trans h1')
    · exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) e2).trans (l2.trans hx.symm))

end GlobalTheory.TwistFlat
end

