module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianNormalLocalApprox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0512
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelTorsorOrigin
section
open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginNoeth

theorem mem_originIdeal_iff {T : Type} [CommRing T] [IsLocalRing T] (f : Polynomial T) :
    f ∈ GlobalTheory.KeyOriginCut.originIdeal T ↔ f.coeff 0 ∈ maximalIdeal T := by
  constructor
  · intro hf
    have hle : GlobalTheory.KeyOriginCut.originIdeal T ≤ (maximalIdeal T).comap (Polynomial.constantCoeff (R := T)) := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        simpa using ha
      · rw [Ideal.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp
    have := hle hf
    simpa [Polynomial.coeff_zero_eq_eval_zero] using this
  · intro hf
    have h1 : Polynomial.C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal T :=
      Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)
    have h2 : f - Polynomial.C (f.coeff 0) ∈ GlobalTheory.KeyOriginCut.originIdeal T :=
      Ideal.mem_sup_right (Ideal.mem_span_singleton.mpr (Polynomial.X_dvd_sub_C))
    simpa using Ideal.add_mem _ h1 h2

theorem comap_originIdeal (A T : Type) [CommRing A] [IsLocalRing A] [CommRing T] [IsLocalRing T]
    (i : A →+* T) [IsLocalHom i] :
    (GlobalTheory.KeyOriginCut.originIdeal T).comap (Polynomial.mapRingHom i) = GlobalTheory.KeyOriginCut.originIdeal A := by
  ext f
  rw [Ideal.mem_comap, mem_originIdeal_iff, mem_originIdeal_iff, Polynomial.coe_mapRingHom,
    Polynomial.coeff_map, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_map_iff]

theorem isIntegrallyClosed_of_absIntClosed (T : Type) [CommRing T] [IsDomain T]
    (hT : GlobalTheory.LocAcyc.AbsIntClosed T) : IsIntegrallyClosed T := by
  rw [isIntegrallyClosed_iff (FractionRing T)]
  intro x hx0
  obtain ⟨p, hpm, hpx⟩ := hx0
  suffices H : ∀ n : ℕ, ∀ p : Polynomial T, p.Monic → p.natDegree = n → Polynomial.eval₂ (algebraMap T (FractionRing T)) x p = 0 →
      ∃ y, algebraMap T (FractionRing T) y = x from H _ p hpm rfl hpx
  intro n
  induction n with
  | zero =>
    intro p hp hd hx
    have h1 := Polynomial.eq_one_of_monic_natDegree_zero hp hd
    subst h1
    simp at hx
  | succ n ih =>
    intro p hp hd hx
    obtain ⟨r, hr⟩ := hT p hp (by omega)
    have hroot : p.IsRoot r := hr
    have hdec := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
    set p' := p /ₘ (Polynomial.X - Polynomial.C r)
    have hp' : p'.Monic := (Polynomial.monic_X_sub_C r).of_mul_monic_left (by rw [hdec]; exact hp)
    have hd' : p'.natDegree = n := by
      have := congrArg Polynomial.natDegree hdec
      rw [(Polynomial.monic_X_sub_C r).natDegree_mul hp', Polynomial.natDegree_X_sub_C] at this
      omega
    rw [← hdec, Polynomial.eval₂_mul] at hx
    rcases mul_eq_zero.mp hx with h | h
    · refine ⟨r, ?_⟩
      simp at h
      exact (sub_eq_zero.mp h).symm
    · exact ih p' hp' hd' h

theorem norm_finiteType {T : Type} [CommRing T] [IsDomain T] [IsIntegrallyClosed T] (S : Finset T) :
    Algebra.FiniteType ℤ (GlobalTheory.NormalApprox.norm S) := by
  haveI := GlobalTheory.finite_integralClosure_of_essFiniteType_int (GlobalTheory.NormalApprox.gen S)
  haveI : Algebra.FiniteType ℤ
      (integralClosure (GlobalTheory.NormalApprox.gen S) (FractionRing (GlobalTheory.NormalApprox.gen S))) :=
    Algebra.FiniteType.trans (S := GlobalTheory.NormalApprox.gen S) inferInstance inferInstance
  exact Algebra.FiniteType.equiv this
    (AlgEquiv.ofRingEquiv (f := (GlobalTheory.NormalApprox.normEquiv S).symm) (fun n => by simp))

theorem loc_essFiniteType {T : Type} [CommRing T] [IsDomain T] [IsIntegrallyClosed T] (S : Finset T) :
    Algebra.EssFiniteType ℤ (GlobalTheory.NormalApprox.loc S) := by
  haveI := norm_finiteType S
  haveI := GlobalTheory.NormalApprox.loc_isLocalization S
  haveI : Algebra.EssFiniteType (GlobalTheory.NormalApprox.norm S) (GlobalTheory.NormalApprox.loc S) :=
    Algebra.EssFiniteType.of_isLocalization _ (GlobalTheory.NormalApprox.unitsIn S)
  exact Algebra.EssFiniteType.comp ℤ (GlobalTheory.NormalApprox.norm S) (GlobalTheory.NormalApprox.loc S)

theorem exists_noetherian_model : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E]
      [IsScalarTower T (Polynomial T) E] [Algebra.Etale (Polynomial T) E]
      (Q : Ideal E) [Q.IsPrime],
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (j : Localization.AtPrime Q →+* O),
      j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O →
    ∀ (ψ : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψ.comp (algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp j →
    ∀ (D₁ : Type) [CommRing D₁] [Algebra (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁]
      (act₁ : Multiplicative (ZMod q) →* (D₁ ≃ₐ[GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)] D₁)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁ q act₁ →
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (_ : IsNoetherianRing A)
      (_ : IsIntegrallyClosed A) (_ : Algebra.EssFiniteType ℤ A) (i : A →+* T), Function.Injective i ∧ IsLocalHom i ∧ IsUnit (q : A) ∧
      ∃ (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial A) EA) (_ : Algebra A EA)
        (_ : IsScalarTower A (Polynomial A) EA) (_ : Algebra.Etale (Polynomial A) EA)
        (QA : Ideal EA) (_ : QA.IsPrime),
        QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A ∧
      ∃ (jA : Localization.AtPrime QA →+* O),
        jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
          (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) ∧
      ∃ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
        ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
          (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA ∧
      ∃ (DA : Type) (_ : CommRing DA) (_ : Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA)
        (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
        GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA ∧
        ∀ σ : DA →+* GlobalTheory.LocAcyc.GenFib T O,
          σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = ψA →
          ∃ σ₁ : D₁ →+* GlobalTheory.LocAcyc.GenFib T O, σ₁.comp (algebraMap (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)) D₁) = ψ := by
  intro T O _ _ _ _ _ _ _ _ hT q hq hqT E _ _ _ _ _ Q _ hQ j hj ψ hψ D₁ _ _ act₁ htor
  have hTic : IsIntegrallyClosed T := isIntegrallyClosed_of_absIntClosed T hT
  let 𝒜 : Finset T → Subring T := GlobalTheory.NormalApprox.loc
  have hmono : Monotone 𝒜 := GlobalTheory.NormalApprox.loc_mono
  have hcov : ∀ (S : Finset T), ∀ x ∈ S, x ∈ 𝒜 S := fun S x hx => GlobalTheory.NormalApprox.mem_loc_of_mem S hx
  have hprop : ∀ S, IsNoetherianRing (𝒜 S) ∧ IsIntegrallyClosed (𝒜 S) ∧ IsLocalRing (𝒜 S) ∧
      (∀ x : 𝒜 S, IsUnit (x : T) → IsUnit x) ∧ Algebra.EssFiniteType ℤ (𝒜 S) := by
    intro S
    haveI := GlobalTheory.NormalApprox.loc_isLocalization S
    haveI := GlobalTheory.NormalApprox.norm_isIntegrallyClosed S
    exact ⟨IsLocalization.isNoetherianRing (GlobalTheory.NormalApprox.unitsIn S) _ (GlobalTheory.NormalApprox.norm_isNoetherianRing S),
      isIntegrallyClosed_of_isLocalization (GlobalTheory.NormalApprox.loc S) (GlobalTheory.NormalApprox.unitsIn S)
        (GlobalTheory.NormalApprox.unitsIn_le S),
      GlobalTheory.NormalApprox.loc_isLocalRing S, GlobalTheory.NormalApprox.isUnit_of_isUnit_coe S, loc_essFiniteType S⟩
  obtain ⟨S, EA, _, _, _, _, _, e, he, β, hβ, D, _, _, actA, htorA, hlast⟩ :=
    GlobalTheory.T.exists_torsor_descent_directedUnion_subring T (Finset T) 𝒜 hmono (fun x => ⟨{x}, hcov {x} x (Finset.mem_singleton_self x)⟩) q hq E Q D₁ act₁ htor
  obtain ⟨hN, hIC, hL, hU, hEF⟩ := hprop S
  have hloc : IsLocalHom (𝒜 S).subtype := ⟨fun a ha => hU a ha⟩
  have hqA : IsUnit (q : 𝒜 S) := hU _ (by simpa using hqT)
  have horig : (Q.comap e).comap (algebraMap (Polynomial (𝒜 S)) EA) = GlobalTheory.KeyOriginCut.originIdeal (𝒜 S) := by
    rw [Ideal.comap_comap, he, ← Ideal.comap_comap, hQ]
    exact comap_originIdeal (𝒜 S) T (𝒜 S).subtype
  let jA : Localization.AtPrime (Q.comap e) →+* O := j.comp (Localization.localRingHom (Q.comap e) Q e rfl)
  have hjA : jA.comp (algebraMap (Polynomial (𝒜 S)) (Localization.AtPrime (Q.comap e))) =
      (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom (𝒜 S).subtype) := by
    refine RingHom.ext fun x => ?_
    change j (Localization.localRingHom (Q.comap e) Q e rfl
      (algebraMap (Polynomial (𝒜 S)) (Localization.AtPrime (Q.comap e)) x)) = _
    rw [IsScalarTower.algebraMap_apply (Polynomial (𝒜 S)) EA (Localization.AtPrime (Q.comap e)),
      Localization.localRingHom_to_map, ← RingHom.comp_apply e, he, RingHom.comp_apply,
      ← IsScalarTower.algebraMap_apply, ← RingHom.comp_apply j, hj]
    rfl
  refine ⟨𝒜 S, inferInstance, inferInstance, hL, hN, hIC, hEF, (𝒜 S).subtype, Subtype.val_injective, hloc, hqA,
    EA, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, Q.comap e, inferInstance, horig,
    jA, hjA, ψ.comp β, ?_, D, inferInstance, inferInstance, actA, htorA, fun σ hσ => hlast _ ψ σ hσ⟩
  rw [RingHom.comp_assoc, hβ, ← RingHom.comp_assoc, hψ]
  rfl

end GlobalTheory.KeyOriginNoeth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialisationToStrictlyHenselian
section
open IsLocalRing Polynomial

namespace GlobalTheory.Specialise

theorem sepEtale (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (Q : Ideal R) [Q.IsPrime] (L : Type) [Field L] [Algebra R L] [Algebra Q.ResidueField L]
    [IsScalarTower R Q.ResidueField L] (f : A →ₐ[R] L) (a : A) :
    IsSeparable Q.ResidueField (f a) := by
  let P : Ideal A := RingHom.ker f
  haveI : P.IsPrime := RingHom.ker_isPrime f
  have hPQ : Q = P.comap (algebraMap R A) := by
    ext r
    simp only [P, Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply R Q.ResidueField L]
    simp
  haveI : P.LiesOver Q := ⟨hPQ⟩
  letI := Localization.AtPrime.algebraOfLiesOver Q P
  have hsep : Algebra.IsSeparable Q.ResidueField P.ResidueField := inferInstance
  let g : P.ResidueField →ₐ[R] L := Ideal.ResidueField.liftₐ P f le_rfl (fun x hx => by
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
    exact isUnit_iff_ne_zero.mpr (fun h => hx h))
  have hg : ∀ x : A, g (algebraMap A P.ResidueField x) = f x := fun x =>
    Ideal.ResidueField.liftₐ_algebraMap _ _ _ _ x
  let g' : P.ResidueField →ₐ[Q.ResidueField] L :=
    { g.toRingHom with
      commutes' := by
        have : g.toRingHom.comp (algebraMap Q.ResidueField P.ResidueField) =
            algebraMap Q.ResidueField L := by
          apply Ideal.ResidueField.ringHom_ext
          ext r
          simp only [RingHom.comp_apply]
          rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
            IsScalarTower.algebraMap_apply R A P.ResidueField]
          exact (hg _).trans (f.commutes r)
        intro c
        exact DFunLike.congr_fun this c }
  have h1 : g' (algebraMap A P.ResidueField a) = f a := hg a
  rw [← h1, isSeparable_map_iff g' g'.toRingHom.injective]
  exact Algebra.IsSeparable.isSeparable _ _

theorem specialisation_exists : ∀ (R S O : Type) [CommRing R] [CommRing S] [IsLocalRing S] [CommRing O]
    [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)] [Algebra R S] [Algebra R O]
    (Q y : Ideal R) [Q.IsPrime] [y.IsPrime], Q ≤ y →
    (IsLocalRing.maximalIdeal S).comap (algebraMap R S) = y →
    (IsLocalRing.maximalIdeal O).comap (algebraMap R O) = Q →
    Module.Flat R S → GlobalTheory.LocAcyc.LocPiecesEtale R S → Nonempty (S →ₐ[R] O) := by
  intro R S O _ _ _ _ _ _ _ _ Q y _ _ hQy hy hQ _ hpieces
  haveI : Algebra.HasGoingDown R S := Algebra.HasGoingDown.of_flat
  haveI : (maximalIdeal S).LiesOver y := ⟨hy.symm⟩
  obtain ⟨Q₂, -, hQ₂p, hQ₂o⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := Q) (q := y) (maximalIdeal S) hQy
  haveI := hQ₂p
  letI : Algebra Q.ResidueField Q₂.ResidueField :=
    (Ideal.ResidueField.map Q Q₂ (algebraMap R S) hQ₂o.over).toAlgebra
  haveI : IsScalarTower R Q.ResidueField Q₂.ResidueField := .of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap,
      ← IsScalarTower.algebraMap_apply]

  have hsepS : ∀ s : S, IsSeparable Q.ResidueField (algebraMap S Q₂.ResidueField s) := by
    intro s
    obtain ⟨ι, _, _, _, Si, -, hcov, hloc⟩ := hpieces
    obtain ⟨i, hi⟩ := hcov s
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hloc i
    let F : Localization.AtPrime q →ₐ[R] Q₂.ResidueField :=
      (IsScalarTower.toAlgHom R S Q₂.ResidueField).comp ((Si i).val.comp (e : _ →ₐ[R] _))
    let f : A →ₐ[R] Q₂.ResidueField :=
      F.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime q))
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective q.primeCompl (e.symm ⟨s, hi⟩)
    have hs : algebraMap S Q₂.ResidueField s = F (IsLocalization.mk' _ a t) := by
      simp only [F, AlgHom.comp_apply, hat]
      simp
    have hft : f t ≠ 0 := by
      have : IsUnit (f t) :=
        (IsLocalization.map_units (Localization.AtPrime q) t).map F
      exact this.ne_zero
    have hmul : F (IsLocalization.mk' _ a t) * f t = f a := by
      simp only [f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', ← map_mul,
        IsLocalization.mk'_spec]
    have hx : algebraMap S Q₂.ResidueField s = f a * (f t)⁻¹ := by
      rw [hs, eq_mul_inv_iff_mul_eq₀ hft, hmul]
    rw [hx, ← mem_separableClosure_iff]
    refine mul_mem ?_ (inv_mem ?_) <;> rw [mem_separableClosure_iff] <;>
      exact sepEtale R A Q _ f _
  haveI : Algebra.IsSeparable Q.ResidueField Q₂.ResidueField := ⟨fun x => by
    obtain ⟨u, v, -, rfl⟩ := IsFractionRing.div_surjective (A := S ⧸ Q₂) x
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [Ideal.algebraMap_quotient_residueField_mk, Ideal.algebraMap_quotient_residueField_mk,
      ← mem_separableClosure_iff]
    exact div_mem ((mem_separableClosure_iff).2 (hsepS u)) ((mem_separableClosure_iff).2 (hsepS v))⟩

  have hker : ∀ r : R, algebraMap R (ResidueField O) r = 0 ↔ r ∈ Q := by
    intro r
    rw [IsScalarTower.algebraMap_apply R O (ResidueField O), ResidueField.algebraMap_eq,
      residue_eq_zero_iff, ← hQ, Ideal.mem_comap]
  letI : Algebra Q.ResidueField (ResidueField O) :=
    (Ideal.ResidueField.lift Q (algebraMap R (ResidueField O)) (fun r hr => (hker r).2 hr)
      (fun r hr => by
        simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
        exact isUnit_iff_ne_zero.mpr (fun h => hr ((hker r).1 h)))).toAlgebra
  haveI : IsScalarTower R Q.ResidueField (ResidueField O) := .of_algebraMap_eq fun r => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (Ideal.ResidueField.lift_algebraMap Q _ _ _ r).symm
  let φ₀ : Q₂.ResidueField →ₐ[Q.ResidueField] ResidueField O := IsSepClosed.lift
  let ψ : S →ₐ[R] ResidueField O :=
    (φ₀.restrictScalars R).comp (IsScalarTower.toAlgHom R S Q₂.ResidueField)
  obtain ⟨φ, -⟩ := (GlobalTheory.IndEtaleHensel.bijective_residue_comp R S O hpieces).2 ψ
  exact ⟨φ⟩

end GlobalTheory.Specialise
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorSquareKerOfSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExtSqKer

variable {R : Type} [CommRing R] {M H Q : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup H] [Module R H] [AddCommGroup Q] [Module R Q]

theorem upd_congr {J : Type} [DecidableEq J] (p : M →ₗ[R] H) (F : M [⋀^J]→ₗ[R] Q)
    (hF : ∀ (u : J → M) (j : J), p (u j) = 0 → F u = 0)
    (u : J → M) (j : J) (a b : M) (hab : p a = p b) :
    F (Function.update u j a) = F (Function.update u j b) := by
  have h1 : a = b + (a - b) := by abel
  rw [h1, F.map_update_add, hF (Function.update u j (a - b)) j (by simp [hab]), add_zero]

noncomputable def descend {J : Type} (p : M →ₗ[R] H) (hp : Function.Surjective p)
    (F : M [⋀^J]→ₗ[R] Q)
    (hF : ∀ (u : J → M) (j : J), p (u j) = 0 → F u = 0) :
    H [⋀^J]→ₗ[R] Q where
  toFun v := F (fun k => Function.surjInv hp (v k))
  map_update_add' := by
    intro _ v j x y
    have e : ∀ z : H, (fun k => Function.surjInv hp (Function.update v j z k)) =
        Function.update (fun k => Function.surjInv hp (v k)) j (Function.surjInv hp z) := by
      intro z; funext k; by_cases h : k = j
      · subst h; simp
      · simp [h]
    simp only [e]
    rw [upd_congr p F hF _ j _ (Function.surjInv hp x + Function.surjInv hp y)
      (by simp [Function.surjInv_eq hp]), F.map_update_add]
  map_update_smul' := by
    intro _ v j c x
    have e : ∀ z : H, (fun k => Function.surjInv hp (Function.update v j z k)) =
        Function.update (fun k => Function.surjInv hp (v k)) j (Function.surjInv hp z) := by
      intro z; funext k; by_cases h : k = j
      · subst h; simp
      · simp [h]
    simp only [e]
    rw [upd_congr p F hF _ j _ (c • Function.surjInv hp x)
      (by simp [Function.surjInv_eq hp]), F.map_update_smul, RingHom.id_apply]
  map_eq_zero_of_eq' := by
    intro v a b hv hab
    exact F.map_eq_zero_of_eq _ (by simp [hv]) hab

end GlobalTheory.ExtSqKer

namespace GlobalTheory.ExtSqKer

variable {R : Type} [CommRing R] {M H Q : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup H] [Module R H] [AddCommGroup Q] [Module R Q]

theorem fin_two_vector_eq_matrixVecCons (u : Fin 2 → M) : u = ![u 0, u 1] := by
  ext k; fin_cases k <;> rfl

theorem congr_two (p : M →ₗ[R] H) (F : M [⋀^Fin 2]→ₗ[R] Q)
    (hF : ∀ (u : Fin 2 → M) (j : Fin 2), p (u j) = 0 → F u = 0)
    (u u' : Fin 2 → M) (h : ∀ k, p (u k) = p (u' k)) : F u = F u' := by
  calc F u = F (Function.update u 0 (u 0)) := by rw [Function.update_eq_self]
    _ = F (Function.update u 0 (u' 0)) := upd_congr p F hF u 0 _ _ (h 0)
    _ = F (Function.update (Function.update u 0 (u' 0)) 1 ((Function.update u 0 (u' 0)) 1)) := by
        rw [Function.update_eq_self]
    _ = F (Function.update (Function.update u 0 (u' 0)) 1 (u' 1)) :=
        upd_congr p F hF _ 1 _ _ (by simpa using h 1)
    _ = F u' := by
        congr 1; ext k; fin_cases k <;> simp

end GlobalTheory.ExtSqKer


open GlobalTheory.ExtSqKer in
theorem GlobalTheory.exteriorSquare_ker_of_surjective (R : Type) [CommRing R] (W M H : Type)
    [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
    (i : W →ₗ[R] M) (p : M →ₗ[R] H) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (t : ⋀[R]^2 M) (ht : exteriorPower.map 2 p t = 0) :
    ∃ (n : ℕ) (a : Fin n → M) (w : Fin n → W),
      t = ∑ k, exteriorPower.ιMulti R 2 ![a k, i (w k)] := by
  set S : Set (⋀[R]^2 M) := {x | ∃ (a : M) (w : W), x = exteriorPower.ιMulti R 2 ![a, i w]}
  set N : Submodule R (⋀[R]^2 M) := Submodule.span R S
  let F : M [⋀^Fin 2]→ₗ[R] (⋀[R]^2 M ⧸ N) := N.mkQ.compAlternatingMap (exteriorPower.ιMulti R 2)
  have hF : ∀ (u : Fin 2 → M) (j : Fin 2), p (u j) = 0 → F u = 0 := by
    intro u j hj
    obtain ⟨w, hw⟩ := (hex (u j)).1 hj
    simp only [F, LinearMap.compAlternatingMap_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    fin_cases j
    · have e : u = ![u 1, i w] ∘ Equiv.swap 0 1 := by
        ext k; fin_cases k <;> simp [hw]
      rw [e, AlternatingMap.map_swap _ _ (by decide)]
      exact N.neg_mem (Submodule.subset_span ⟨u 1, w, rfl⟩)
    · rw [fin_two_vector_eq_matrixVecCons u]
      exact Submodule.subset_span ⟨u 0, w, by simp [hw]⟩
  let g := exteriorPower.alternatingMapLinearEquiv (descend p hp F hF)
  have hg : g ∘ₗ exteriorPower.map 2 p = N.mkQ := by
    apply exteriorPower.linearMap_ext
    ext m
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.coe_comp, Function.comp_apply,
      exteriorPower.map_apply_ιMulti, g, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    change F _ = F m
    exact congr_two p F hF _ _ (fun k => by simp [Function.surjInv_eq hp])
  have hN : t ∈ N := by
    have := congrArg (fun f => f t) hg
    simp only [LinearMap.coe_comp, Function.comp_apply, ht, map_zero, Submodule.mkQ_apply] at this
    exact (Submodule.Quotient.mk_eq_zero N).1 this.symm
  obtain ⟨n, c, x, hx⟩ := Submodule.mem_span_set'.1 hN
  choose a w haw using fun k => (x k).2
  refine ⟨n, fun k => c k • a k, w, ?_⟩
  rw [← hx]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [haw k]
  have e : ![c k • a k, i (w k)] = Function.update ![a k, i (w k)] 0 (c k • a k) := by
    ext l; fin_cases l <;> simp
  rw [e, AlternatingMap.map_update_smul]
  congr 2
  ext l; fin_cases l <;> simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgProjectiveConstantRankExtensionAndProd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem fp_prod (R : Type) [CommRing R] (W H : Type) [AddCommGroup W] [Module R W]
    [AddCommGroup H] [Module R H] (a b : ℕ) (hW : FP R W a) (hH : FP R H b) :
    FP R (W × H) (a + b) := by
  obtain ⟨hWf, hWp, hWr⟩ := hW
  obtain ⟨hHf, hHp, hHr⟩ := hH
  refine ⟨inferInstance, inferInstance, fun p => ?_⟩
  have := Module.rankAtStalk_prod (R := R) W H
  rw [congrFun this p, Pi.add_apply, hWr p, hHr p]

theorem fp_ext (R : Type) [CommRing R] (W M H : Type) [AddCommGroup W] [Module R W]
    [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (a b : ℕ)
    (i : W →ₗ[R] M) (p : M →ₗ[R] H) (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (hW : FP R W a) (hH : FP R H b) : FP R M (a + b) := by
  have hWH := fp_prod R W H a b hW hH
  obtain ⟨-, hHp, -⟩ := hH
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : H →ₗ[R] H) hp
  obtain ⟨e, -⟩ := hex.splitSurjectiveEquiv hi ⟨s, hs⟩
  obtain ⟨hf, hpr, hr⟩ := hWH
  refine ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, fun q => ?_⟩
  rw [congrFun (Module.rankAtStalk_eq_of_equiv e) q, hr q]

theorem fp_ext_prod : (∀ (R : Type) [CommRing R] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (a b : ℕ) (i : W →ₗ[R] M) (p : M →ₗ[R] H), Function.Injective i → Function.Surjective p → Function.Exact i p → FP R W a → FP R H b → FP R M (a + b)) ∧ ∀ (R : Type) [CommRing R] (W H : Type) [AddCommGroup W] [Module R W] [AddCommGroup H] [Module R H] (a b : ℕ), FP R W a → FP R H b → FP R (W × H) (a + b) :=
  ⟨fun R _ W M H _ _ _ _ _ _ a b i p hi hp hex hW hH => fp_ext R W M H a b i p hi hp hex hW hH,
   fun R _ W H _ _ _ _ a b hW hH => fp_prod R W H a b hW hH⟩

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActDualPairCommutingLieActions
section
open Formalism.BasicNotions.TH
open scoped Kronecker

namespace GlobalTheory.FockPair

theorem fockAct1_eq_kron (p q r s : ℕ) (Y : Mat p q) :
    fockAct1 p q r s Y = omAct p q r s (Y ⊗ₖ (1 : Mat r s)) := rfl

theorem fockAct2_eq_kron (p q r s : ℕ) (Z : Mat r s) :
    fockAct2 p q r s Z = omAct p q r s ((1 : Mat p q) ⊗ₖ Z) := rfl

theorem pair_lie_commute : ∀ (p q r s : ℕ), IsLieAct (fockAct1 p q r s) ∧
    IsLieAct (fockAct2 p q r s) ∧ ∀ (Y : Mat p q) (Z : Mat r s),
      fockAct1 p q r s Y * fockAct2 p q r s Z = fockAct2 p q r s Z * fockAct1 p q r s Y := by
  intro p q r s
  refine ⟨fun X Y => ?_, fun X Y => ?_, fun Y Z => ?_⟩
  · rw [map_sub]
    simp only [fockAct1_eq_kron]
    rw [← _root_.GlobalTheory.FockLie.omAct_lie, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      map_sub]
  · rw [map_sub]
    simp only [fockAct2_eq_kron]
    rw [← _root_.GlobalTheory.FockLie.omAct_lie, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      map_sub]
  · rw [← sub_eq_zero, fockAct1_eq_kron, fockAct2_eq_kron, ← _root_.GlobalTheory.FockLie.omAct_lie,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    simp

end GlobalTheory.FockPair
end

