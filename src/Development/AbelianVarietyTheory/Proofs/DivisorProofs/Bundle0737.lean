module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0717
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyFieldAddEquivGalois
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSecond
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms.BadPrimes

theorem false_of_isCoprime {A : Type} [CommRing A] [IsDedekindDomain A] (P : HeightOneSpectrum A) {a b : A}
    (h : IsCoprime a b) (ha : a ∈ P.asIdeal) (hb : b ∈ P.asIdeal) : False := by
  obtain ⟨x, y, hxy⟩ := h
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hxy ▸ add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)))

theorem eq_of_natCast_mem {A : Type} [CommRing A] [IsDedekindDomain A] (P : HeightOneSpectrum A) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (ha : (p : A) ∈ P.asIdeal) (hb : (q : A) ∈ P.asIdeal) : p = q := by
  by_contra hne
  exact false_of_isCoprime P (Nat.Coprime.cast ((Nat.coprime_primes hp hq).2 hne)) ha hb

variable {X : Fields} {Pr : Primes X}

theorem g_injective (hPr : Pr.Ok) : Function.Injective Pr.g := by
  intro i j h
  have := hPr.g_ne
  fin_cases i <;> fin_cases j <;> simp_all

theorem exists_vG {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vGs) : ∃ i, P ∈ Pr.vG i := by
  classical
  rcases Finset.mem_union.mp h with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

theorem g_mem (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) :
    ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal :=
  hPr.piG_norm i ▸ Ideal.mul_mem_left _ _ (mem_of_mem_divs h)

theorem T_mem (hPr : Pr.Ok) {u : Pr.Word} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vT u) :
    ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal :=
  hPr.piT_norm u ▸ Ideal.mul_mem_right _ _ (mem_of_mem_divs h)

theorem natCast_mem_of_conjP {P : HeightOneSpectrum (𝓞 X.E)} {n : ℕ} (h : ((n : ℕ) : 𝓞 X.E) ∈ (conjPrime₂ P).asIdeal) :
    ((n : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
  rw [mem_conjP, map_natCast] at h
  exact h

theorem rowSG_one (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) :
    rowSG Pr sel (1 : Tup X.F X.E X.K Sg) = Pr.vGs := by
  classical
  ext w
  constructor
  · intro hw
    rcases Finset.mem_union.mp hw with h | h
    · exact h
    · have h' : w ∈ QE sel ((mu0 X.F X.E X.K Sg : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) := h
      rw [twistPrimes_trivialTuple_empty sel Sg] at h'
      simp at h'
  · intro hw
    exact Finset.mem_union.mpr (Or.inl hw)

theorem prod_qOf_vGs (hPr : Pr.Ok) : ∏ P ∈ Pr.vGs, Formalism.L2.Col.qOf P = (Pr.g 0 * Pr.g 1) ^ X.f := by
  classical
  have hd : Disjoint (Pr.vG 0) (Pr.vG 1) := Finset.disjoint_left.2 fun P h0 h1 =>
    hPr.g_ne (eq_of_natCast_mem P (hPr.g_prime 0) (hPr.g_prime 1) (g_mem hPr h0) (g_mem hPr h1))
  have hi : ∀ i, ∏ P ∈ Pr.vG i, Formalism.L2.Col.qOf P = Pr.g i ^ X.f := fun i => by
    unfold Formalism.L2.Col.qOf
    rw [Finset.prod_congr rfl (g := fun _ => Pr.g i) (fun P hP => hPr.vG_norm i P hP), Finset.prod_const, hPr.vG_card]
  have hu : Pr.vGs = (Pr.vG 0).disjUnion (Pr.vG 1) hd := by
    ext w
    simp [Primes.vGs]
  rw [hu, Finset.prod_disjUnion, hi, hi, mul_pow]

theorem odd_g (hPr : Pr.Ok) (h2 : 2 ∣ Pr.cond) (i : Fin 2) : Odd (Pr.g i) :=
  Nat.odd_iff.2 ((hPr.g_cong i).of_dvd h2)

theorem two_notMem_vT (hPr : Pr.Ok) (h2 : 2 ∣ Pr.cond) {u : Pr.Word} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vT u) :
    (2 : 𝓞 X.E) ∉ P.asIdeal := by
  intro hP
  obtain ⟨c, hc⟩ := hPr.piT_cong u
  obtain ⟨k, hk⟩ := h2
  have h1 : Pr.piT u - 1 ∈ P.asIdeal := by
    rw [hc, hk]
    push_cast
    rw [mul_assoc, mul_assoc]
    exact Ideal.mul_mem_right _ _ hP
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem (mem_of_mem_divs h) h1))

theorem odd_typePrime_of_two_dvd_cond (hX : X.Ok) (hPr : Pr.Ok) (h2 : 2 ∣ Pr.cond) (u : Pr.Word) : Odd (Pr.T u) := by
  obtain ⟨P, hP⟩ : (Pr.vT u).Nonempty := Finset.card_pos.1 (hPr.vT_card u ▸ hX.f_pos)
  refine (hPr.T_prime u).odd_of_ne_two fun h => two_notMem_vT hPr h2 hP ?_
  have := T_mem hPr hP
  rw [h] at this
  exact_mod_cast this

theorem conjP_notMem (hPr : Pr.Ok) (u : Pr.Word) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vT u ∨ P ∈ Pr.vGs) :
    ¬ (conjPrime₂ P ∈ Pr.vT u ∨ conjPrime₂ P ∈ Pr.vGs) := by
  rintro (h' | h')
  · rcases h with h | h
    · exact false_of_isCoprime P (hPr.piT_cop u) (mem_of_mem_divs h) (mem_of_mem_divs h' :)
    · obtain ⟨i, hi⟩ := exists_vG h
      exact hPr.T_ne_g u i (eq_of_natCast_mem P (hPr.T_prime u) (hPr.g_prime i)
        (natCast_mem_of_conjP (T_mem hPr h')) (g_mem hPr hi))
  · obtain ⟨j, hj⟩ := exists_vG h'
    have hg := natCast_mem_of_conjP (g_mem hPr hj)
    rcases h with h | h
    · exact hPr.T_ne_g u j (eq_of_natCast_mem P (hPr.T_prime u) (hPr.g_prime j) (T_mem hPr h) hg)
    · obtain ⟨i, hi⟩ := exists_vG h
      obtain rfl : i = j := g_injective hPr (eq_of_natCast_mem P (hPr.g_prime i) (hPr.g_prime j) (g_mem hPr hi) hg)
      have h1 : cO X.E (cO X.E (Pr.piG i)) ∈ P.asIdeal := (mem_of_mem_divs hj :)
      rw [cO_cO] at h1
      exact false_of_isCoprime P (hPr.piG_cop i) h1 (mem_of_mem_divs hi)

end GlobalTheory.ColNorms.BadPrimes
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubfunctorStalkIdealCriterion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FinStalk

theorem stalk_isArtinianRing (K : Type) [Field K] (X : Scheme) (f : X ⟶ Sp K) [IsFinite f] (x : X) :
    IsArtinianRing (X.presheaf.stalk x) := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have hfin : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.Finite :=
    f.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2)
  letI := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.toAlgebra
  haveI : Module.Finite K Γ(X, ⊤) := hfin
  haveI : IsArtinianRing Γ(X, ⊤) := IsArtinianRing.of_finite K Γ(X, ⊤)
  have hU := isAffineOpen_top X
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, trivial⟩ : (⊤ : X.Opens))
  have hl := hU.isLocalization_stalk ⟨x, trivial⟩
  exact IsArtinianRing.localization_artinian (hU.primeIdealOf ⟨x, trivial⟩).asIdeal.primeCompl _

end GlobalTheory.FinStalk

namespace GlobalTheory.FinStalk

theorem stalk_quotient_ne_top_and_isArtinianRing : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∀ J : Ideal (A.left.presheaf.stalk x₀), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) → J ≠ ⊤ ∧ IsArtinianRing (A.left.presheaf.stalk x₀ ⧸ J) := by
  intro K _ A _ H _ j hj hci hfin x₀ hx₀ J hJ
  obtain ⟨p, hp⟩ := hx₀
  have hη : (η[H] ≫ j).left = η[A].left := congrArg CommaMorphism.left (IsMonHom.one_hom j)
  obtain ⟨h₀, e⟩ : ∃ h₀ : H.left, x₀ = j.left.base h₀ :=
    ⟨η[H].left.base p, by rw [← hp, ← hη]; rfl⟩
  subst e

  have hJ1 : J ≤ RingHom.ker (j.left.stalkMap h₀).hom :=
    (hJ (H.left.presheaf.stalk h₀) (j.left.stalkMap h₀).hom).1
      ⟨H.left.fromSpecStalk h₀, (Scheme.SpecMap_stalkMap_fromSpecStalk j.left).symm⟩
  have hne : J ≠ ⊤ := fun h => RingHom.ker_ne_top _ (top_le_iff.1 (h ▸ hJ1))
  refine ⟨hne, ?_⟩
  haveI : Nontrivial (A.left.presheaf.stalk (j.left.base h₀) ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsLocalRing (A.left.presheaf.stalk (j.left.base h₀) ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk J) :=
    Function.Surjective.isLocalHom _ Ideal.Quotient.mk_surjective
  obtain ⟨y, hy⟩ := (hJ _ (Ideal.Quotient.mk J)).2 (by rw [Ideal.mk_ker])
  let R := CommRingCat.of (A.left.presheaf.stalk (j.left.base h₀) ⧸ J)
  have hpt : y.base (IsLocalRing.closedPoint R) = h₀ := by
    apply j.left.isClosedEmbedding.injective
    have : j.left.base (y.base (IsLocalRing.closedPoint R)) = (A.left.fromSpecStalk (j.left.base h₀)).base
        ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).base (IsLocalRing.closedPoint R)) :=
      congrArg (fun g : Sp R ⟶ A.left => g.base (IsLocalRing.closedPoint R)) hy
    rw [this]
    haveI : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk J)).hom := by
      change IsLocalHom (Ideal.Quotient.mk J); infer_instance
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have key : ∀ z (_ : y.base (IsLocalRing.closedPoint R) = z),
      ∃ φ : H.left.presheaf.stalk z ⟶ R, Spec.map φ ≫ H.left.fromSpecStalk z = y := by
    rintro z rfl
    exact ⟨_, Scheme.Spec_stalkClosedPointTo_fromSpecStalk y⟩
  obtain ⟨φ, hφ⟩ := key h₀ hpt
  have hcomp : j.left.stalkMap h₀ ≫ φ = CommRingCat.ofHom (Ideal.Quotient.mk J) := by
    apply Spec.map_injective
    rw [← cancel_mono (A.left.fromSpecStalk (j.left.base h₀)), ← hy, ← hφ, Spec.map_comp,
      Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc]
  have hsurj : Function.Surjective φ.hom := by
    intro r
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective (I := J) r
    exact ⟨(j.left.stalkMap h₀).hom a, by
      rw [← CommRingCat.comp_apply, hcomp]; rfl⟩
  haveI := stalk_isArtinianRing K H.left H.hom h₀
  exact hsurj.isArtinianRing

end GlobalTheory.FinStalk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureNormOneProductsSubgroupPropertiesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closure_normOneProducts_h0_properties : ∀ (F : Type) [Field F] [NumberField F] (a b : F) (ε : AF F), ε * ε = ε → (∀ x ∈ closure (H0 (a := a) (b := b) ε), ∀ y ∈ closure (H0 (a := a) (b := b) ε), x * y ∈ closure (H0 (a := a) (b := b) ε)) ∧ (∀ x ∈ closure (H0 (a := a) (b := b) ε), star x ∈ closure (H0 (a := a) (b := b) ε)) ∧ (∀ δ δ' : ℍ[F, a, b], δ * δ' = 1 → ∀ x ∈ closure (H0 (a := a) (b := b) ε), rat δ * x * rat δ' ∈ closure (H0 (a := a) (b := b) ε)) ∧ (∀ x ∈ closure (H0 (a := a) (b := b) ε), nrm x = 1) := by
  first | exact @GlobalTheory.QSA.Grp.closure_normOneProducts_subgroup_properties | exact GlobalTheory.QSA.Grp.closure_normOneProducts_subgroup_properties | (intros; apply GlobalTheory.QSA.Grp.closure_normOneProducts_subgroup_properties <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyFieldAddEquivGaloisStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_cohomology_addEquiv_galois_cohomology : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (M : Rep.{0} R (Ω ≃ₐ[K] Ω)) [GroundTheory.ProfCoh.IsDiscreteRep M] (e : M ≃+ Sec F (Spec (CommRingCat.of Ω))), (∀ (σ : Ω ≃ₐ[K] Ω) (m : M), e (M.ρ σ m) = Sec.res (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) (e m)) → ∀ n : ℕ, Nonempty (H R (sp K) F n ≃+ GroundTheory.ProfCoh.cohomology M n) := by
  first
  | exact @GlobalTheory.EtC.GalFld.cohomology_field_addEquiv_galois
  | exact GlobalTheory.EtC.GalFld.cohomology_field_addEquiv_galois
  | (intros; apply GlobalTheory.EtC.GalFld.cohomology_field_addEquiv_galois <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColsInIsometry
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

noncomputable section

namespace GlobalTheory.ColFirstIso

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K] {S S' : GSD K}

def clEquiv (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D) (hs : ∀ g d, eD (g • d) = eG g • eD d) : S'.Cl ≃ S.Cl :=
  Quotient.congr eD fun a b => by
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨eG g, (hs g b).symm⟩
    · rintro ⟨g, hg⟩
      refine ⟨eG.symm g, eD.injective ?_⟩
      have hg' : g • eD b = eD a := hg
      show eD (eG.symm g • b) = eD a
      rw [hs, MulEquiv.apply_symm_apply, hg']

theorem clEquiv_cls (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D) (hs : ∀ g d, eD (g • d) = eG g • eD d) (d : S'.D) :
    clEquiv eG eD hs (S'.cls d) = S.cls (eD d) := rfl

theorem card_stab (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D) (hs : ∀ g d, eD (g • d) = eG g • eD d) (d : S'.D) :
    Nat.card (MulAction.stabilizer S'.G d) = Nat.card (MulAction.stabilizer S.G (eD d)) := by
  refine Nat.card_congr (eG.toEquiv.subtypeEquiv fun g => ?_)
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  show _ ↔ eG g • eD d = eD d
  rw [← hs, eD.injective.eq_iff]

theorem ipAt_transport (R : S.Rat) (h : S.Ok) (h' : S'.Ok) (eG : S'.G ≃* S.G) (eD : S'.D ≃ S.D)
    (hs : ∀ g d, eD (g • d) = eG g • eD d) (v : InfinitePlace K) (φ : S.EqFun) (φ' : S'.D → S'.V)
    (hp : ∀ d, S'.pairAt v (φ' d) (φ' d) = S.pairAt v ((φ : S.D → S.V) (eD d)) ((φ : S.D → S.V) (eD d))) :
    S'.ipAt h' v φ' φ' = S.ipAt h v φ φ := by
  let e := clEquiv eG eD hs
  let s : S.Sec :=
    { rep := fun c => eD (S'.outSec.rep (e.symm c))
      spec := fun c => by
        rw [← clEquiv_cls eG eD hs, S'.outSec.spec]
        exact e.apply_symm_apply c }
  rw [R.ipAt_indep h s v φ φ]
  let _ := h.fintypeCl
  let _ := h'.fintypeCl
  unfold GSD.ipAt
  refine Fintype.sum_equiv e _ _ fun c => ?_
  have h1 : s.rep (e c) = eD (S'.outSec.rep c) := by
    show eD (S'.outSec.rep (e.symm (e c))) = _
    rw [e.symm_apply_apply]
  rw [h1, S'.wt_eq h' S'.outSec c, card_stab eG eD hs, hp]

end Generic

section Frames

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

def decoEquiv (hQ : Q = ∅) : DecoF X.E n ST SG Q ≃ DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG) where
  toFun := DecoF.deco
  invFun d := ⟨(d, fun _ => 1), fun P => absurd P.2 (by simp [hQ])⟩
  left_inv p := Subtype.ext (Prod.ext rfl (funext fun P => absurd P.2 (by simp [hQ])))
  right_inv _ := rfl

def grpEquiv (hQ : Q = ∅) (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) : FrmG Λ Θ ≃* FormG Λ where
  toFun g := (g.1, g.2.1)
  invFun g := (g.1, g.2, 1)
  left_inv g := Prod.ext rfl (Prod.ext rfl (Subtype.ext (funext fun P => absurd P.2 (by simp [hQ]))))
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem ipAt_frm (hQ : Q = ∅) (C : CoefPk X n (DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG))) (Λ Λ' : LevFam X.E X.K n SG) (hΛ : Λ' = Λ)
    (Θ : LevQFam X.E X.K n Q) (R : (formGSD C Λ).Rat) (h : (formGSD C Λ).Ok)
    (h' : (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ' Θ).Ok) (v : InfinitePlace X.K) (φ : (formGSD C Λ).EqFun) :
    (frmGSD (C.pull (DecoF.deco (Q := Q))) Λ' Θ).ipAt h' v (fun p => (φ : _ → C.V) (DecoF.deco p))
      (fun p => (φ : _ → C.V) (DecoF.deco p)) = (formGSD C Λ).ipAt h v φ φ := by
  subst hΛ
  exact ipAt_transport R h h' (grpEquiv hQ Λ' Θ) (decoEquiv hQ) (fun _ _ => rfl) v φ _ fun _ => rfl

end Frames

theorem qe_one {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} :
    QE sel ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
    change Qprime (1 : Chr X.F X.E X.K) = ∅
    ext v
    simp [Qprime, MonoidHom.ker_one]
  unfold QE
  split_ifs with hf
  · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
    rfl
  · rfl

theorem colsIn_isometry : ∀ (X : Fields) (hX : X.Ok) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (hL : I.Ok Ch sel mu cst G m2) (u : Pr.Word) (h : (chF W sel mu I u 0).Ok), mu = 1 → (∀ v, IsUnit ((MramH W Ch hX u).X v).det) ∧ ∀ (v : InfinitePlace X.K) (x : Fin (ramDim W Ch hX u) → X.K), ((Formalism.HermitianLatticesTheory.normAt (Pi.basisFun X.K (Fin (ramDim W Ch hX u))) (MramH W Ch hX u).X v x ^ 2 : ℝ) : ℂ) = famIpAt (chF W sel mu I u 0) h v (colsIn W Ch hX sel mu cst I hL u x) (colsIn W Ch hX sel mu cst I hL u x) := by
  intro X hX Pr R W Ch sel Sg mu cst I G m2 hL u h hmu
  refine ⟨(colPosH W Ch hX u 0).frameOK_sub (MramV W Ch u) (MramL W Ch u), fun v x => ?_⟩
  have hQ : QE sel (mu : Chr X.F X.E X.K) = ∅ := by
    subst hmu
    exact qe_one sel
  obtain ⟨b, hb⟩ := hL.zero_uniq
  have h1 : famIpAt (chF W sel mu I u 0) h v (colsIn W Ch hX sel mu cst I hL u x) (colsIn W Ch hX sel mu cst I hL u x) =
      (colGSD W Ch u 0).ipAt (colOk W Ch hX u 0) v (colOfCoord W Ch hX u x) (colOfCoord W Ch hX u x) := by
    unfold famIpAt
    rw [Fintype.sum_eq_single b fun b' hb' => absurd (hb b') hb']
    exact ipAt_frm hQ (colVal W u 0 (Pr.vT u) Pr.vGs) (colLev Ch 0) (I.levG 0 b) (hL.zero_G b) (I.levQ 0 b)
      (colRat W Ch hX u 0) (colOk W Ch hX u 0) (h b) v (colOfCoord W Ch hX u x)
  rw [h1, ← (colRat W Ch hX u 0).maj_eq]
  have h2 := (colPosH W Ch hX u 0).sub_maj (MramV W Ch u) v ((ramBas W Ch hX u).equivFun.symm x)
    ((ramBas W Ch hX u).equivFun.symm x)
  rw [thl_majAt_coord, LinearEquiv.apply_symm_apply] at h2
  refine Eq.trans ?_ h2
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity)), Complex.ofReal_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rfl

end GlobalTheory.ColFirstIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnNormParametersEqNatStepGap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV

namespace GlobalTheory.ColumnNormCompare

theorem numRec_eq_ofRecord : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), D.s.Del = (Del : ℚ) → L.etaSz = (D.R.m : ℝ) * (h0 : ℝ) →
    GlobalTheory.ColumnNormCompare.numDatumOfParameters D L = ofRecord D L Del h0 := by
  intro D L Del h0 hD hE
  have hm : (D.R.m : ℝ) ≠ 0 := by
    have := D.R.two_le_m
    exact_mod_cast (show D.R.m ≠ 0 by omega)
  have h1 : ⌊D.s.Del⌋₊ = Del := by rw [hD]; exact Nat.floor_natCast Del
  have h2 : ⌈LevelStarExponents.h0 L⌉₊ = h0 := by
    have : LevelStarExponents.h0 L = (h0 : ℝ) := by
      unfold LevelStarExponents.h0
      rw [hE]; field_simp
    rw [this]; exact Nat.ceil_natCast h0
  simp only [numDatumOfParameters, ofRecord, h1, h2]

end GlobalTheory.ColumnNormCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommAlgFunctorCohomologyCupAnticomm
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem cup_anticomm (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (a b : GlobalTheory.CatCoh.H1 F) : cup F a b = - cup F b a := by
  rw [eq_neg_iff_add_eq_zero]
  obtain ⟨a, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F a
  obtain ⟨b, rfl⟩ := GlobalTheory.CatCoh.H1.mk_surjective F b
  rw [cup_mk, cup_mk, ← map_add (f := _)]
  refine GlobalTheory.CatCoh.H2.mk_eq_zero.2 ⟨fun T T' φ ↦ -(a.1 T T' φ * b.1 T T' φ), ?_⟩
  funext T T' T'' φ ψ
  simp only [d1_apply, Submodule.coe_add, Pi.add_apply, cupZ_apply, Z1.comp a, Z1.comp b, map_mul, map_neg]
  ring

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingAdjointEqOfPullbackIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.AdjPairing

theorem weilIs_adj_eq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → ∀ α β : A ⟶ A, IsMonHom α → IsMonHom β → LBIso (P.pull (lift (fst A A ≫ α) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ β)).left) → ∀ (n : ℤ) (T : Over S) (a b : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) P n (lift (a ≫ α) 1) (lift 1 b) c → Out.WeilIs (G2 A) P n (lift a 1) (lift 1 (b ≫ β)) c' → c = c' := by
  intro S A _ _ P hA hP α β hα hβ hiso n T a b c c' h h'
  let ψ₁ : G2 A ⟶ G2 A := lift (fst A A ≫ α) (snd A A)
  let ψ₂ : G2 A ⟶ G2 A := lift (fst A A) (snd A A ≫ β)
  haveI : IsMonHom ψ₁ := inferInstanceAs (IsMonHom (lift (fst A A ≫ α) (snd A A)))
  haveI : IsMonHom ψ₂ := inferInstanceAs (IsMonHom (lift (fst A A) (snd A A ≫ β)))
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hL : (P.pull ψ₁.left).IsLB := pull_isLB hP _
  have hx₁ : lift a 1 ≫ ψ₁ = lift (a ≫ α) 1 := by ext <;> simp [ψ₁]
  have hy₁ : lift 1 b ≫ ψ₁ = lift 1 b := by ext <;> simp [ψ₁]
  have hx₂ : lift a 1 ≫ ψ₂ = lift a 1 := by ext <;> simp [ψ₂]
  have hy₂ : lift 1 b ≫ ψ₂ = lift 1 (b ≫ β) := by ext <;> simp [ψ₂]
  have hw₁ : LBIso (lbPow (P.pull ψ₁.left) 1) (P.pull ψ₁.left) := lbIso_lbPow_one hL
  have hw₂ : LBIso (lbPow (P.pull ψ₁.left) 1) (P.pull ψ₂.left) :=
    LBIso.trans (isLB_lbPow hL 1) hL (pull_isLB hP _) (lbIso_lbPow_one hL) hiso
  have h1 := WeilIsogeny.weilIs_pull_hom (d := 1) (x := lift a 1) (y := lift 1 b)
    globalFns_holds hAA hL hP ψ₁ hw₁ (by rw [hx₁, hy₁]; exact h)
  have h2 := WeilIsogeny.weilIs_pull_hom (d := 1) (x := lift a 1) (y := lift 1 b)
    globalFns_holds hAA hL hP ψ₂ hw₂ (by rw [hx₂, hy₂]; exact h')
  rw [Nat.cast_one, _root_.mul_one] at h1 h2
  exact CommutatorPairing.weilIs_unique globalFns_holds hAA hL h1 h2

end GlobalTheory.AdjPairing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContConeOfQcqsAffineStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contCone_of_isLimit_of_qcqs_affine_transitions : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Scheme.{0}) (c : Cone G), IsLimit c → (∀ i, CompactSpace (G.obj i)) → (∀ i, QuasiSeparatedSpace (G.obj i)) → (∀ (i j : I) (f : i ⟶ j), IsAffineHom (G.map f)) → ContCone R F (sch.mapCone c) := by
  first
  | exact @GlobalTheory.EtC.contCone_of_qcqs_affine
  | exact GlobalTheory.EtC.contCone_of_qcqs_affine
  | (intros; apply GlobalTheory.EtC.contCone_of_qcqs_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalVanishingCohomologyStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_local_vanishing_cohomology : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ¬ IsUnit f → ∀ (m i : ℤ), 1 ≤ m → ∀ y : Ht q (sp B) m i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A') (_ : Algebra.Etale B A'), IsNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ y = 0 := by
  first | (exact @GlobalTheory.CurveNbhdKill.exists_nbhd_pull_eq_zero) | (exact GlobalTheory.CurveNbhdKill.exists_nbhd_pull_eq_zero) | (intros; apply GlobalTheory.CurveNbhdKill.exists_nbhd_pull_eq_zero <;> assumption)
end

