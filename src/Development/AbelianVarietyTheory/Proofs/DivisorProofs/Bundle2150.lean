module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2052
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2078
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0806
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftOneParameterQuotientTorus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2061
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatePolynomialSubMemMaximalIdealPow
section
open IsLocalRing GlobalTheory.FormalOrigin GlobalTheory.FormalOrigin.Extend

namespace GlobalTheory

theorem exists_mem_closure_sub_mem_maximalIdeal_pow
    (R A : Type) [CommRing R] [IsLocalRing R] [CommRing A] [IsLocalRing A]
    (inc : R →+* A) (ev : A →+* R) (hev : ∀ r, ev (inc r) = r) (n : ℕ) (z : Fin n → A)
    (hm : maximalIdeal A = (maximalIdeal R).map inc ⊔ Ideal.span (Set.range z))
    (k : ℕ) (f : A) :
    ∃ p ∈ Subring.closure (Set.range inc ∪ Set.range z), f - p ∈ maximalIdeal A ^ k := by
  set P := Subring.closure (Set.range inc ∪ Set.range z) with hP
  set m := maximalIdeal A with hmdef
  have incP : ∀ r, inc r ∈ P := fun r => Subring.subset_closure (Or.inl ⟨r, rfl⟩)
  have zP : ∀ i, z i ∈ P := fun i => Subring.subset_closure (Or.inr ⟨i, rfl⟩)
  have hker : ∀ x : A, x - inc (ev x) ∈ m := by
    intro x
    have h1 : x - inc (ev x) ∈ RingHom.ker ev := by
      simp [RingHom.mem_ker, hev]
    exact le_maximalIdeal (RingHom.ker_ne_top ev) h1
  let C : ℕ → Ideal A := fun j =>
    { carrier := {x | ∃ q ∈ P, q ∈ m ^ j ∧ x - q ∈ m ^ (j + 1)}
      add_mem' := by
        rintro a b ⟨q, hq, hqm, hqe⟩ ⟨q', hq', hqm', hqe'⟩
        refine ⟨q + q', P.add_mem hq hq', Ideal.add_mem _ hqm hqm', ?_⟩
        have : a + b - (q + q') = (a - q) + (b - q') := by ring
        rw [this]; exact Ideal.add_mem _ hqe hqe'
      zero_mem' := ⟨0, P.zero_mem, Ideal.zero_mem _, by simp⟩
      smul_mem' := by
        rintro c x ⟨q, hq, hqm, hqe⟩
        refine ⟨inc (ev c) * q, P.mul_mem (incP _) hq, Ideal.mul_mem_left _ _ hqm, ?_⟩
        have hx : x ∈ m ^ j := by
          have : x = q + (x - q) := by ring
          rw [this]; exact Ideal.add_mem _ hqm (Ideal.pow_le_pow_right (Nat.le_succ j) hqe)
        have : c • x - inc (ev c) * q = inc (ev c) * (x - q) + (c - inc (ev c)) * x := by
          simp only [smul_eq_mul]; ring
        rw [this]
        refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hqe) ?_
        rw [pow_succ']
        exact Ideal.mul_mem_mul (hker c) hx }
  have memC : ∀ j x, x ∈ C j ↔ ∃ q ∈ P, q ∈ m ^ j ∧ x - q ∈ m ^ (j + 1) := fun _ _ => Iff.rfl
  have hC1 : m ≤ C 1 := by
    calc m = _ := hm
      _ ≤ C 1 := by
        refine sup_le ?_ ?_
        · rw [Ideal.map_le_iff_le_comap]
          intro r hr
          refine (memC _ _).2 ⟨inc r, incP r, ?_, by simp⟩
          rw [pow_one, hm]; exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hr)
        · rw [Ideal.span_le]
          rintro _ ⟨i, rfl⟩
          refine (memC _ _).2 ⟨z i, zP i, ?_, by simp⟩
          rw [pow_one, hm]; exact Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  have hCj : ∀ j, m ^ j ≤ C j := by
    intro j
    induction j with
    | zero =>
      intro x _
      exact (memC _ _).2 ⟨inc (ev x), incP _, by simp, by simpa using hker x⟩
    | succ j ih =>
      rw [pow_succ]
      refine Ideal.mul_le.2 fun y hy w hw => ?_
      obtain ⟨q, hq, hqm, hqe⟩ := (memC _ _).1 (ih hy)
      obtain ⟨q1, hq1, hq1m, hq1e⟩ := (memC _ _).1 (hC1 hw)
      refine (memC _ _).2 ⟨q * q1, P.mul_mem hq hq1, ?_, ?_⟩
      · rw [pow_succ]; exact Ideal.mul_mem_mul hqm (by simpa using hq1m)
      · have : y * w - q * q1 = q * (w - q1) + (y - q) * w := by ring
        rw [this]
        refine Ideal.add_mem _ ?_ ?_
        · have : m ^ (j + 1 + 1) = m ^ j * m ^ (1 + 1) := by rw [← pow_add]
          rw [this]; exact Ideal.mul_mem_mul hqm hq1e
        · rw [pow_succ]; exact Ideal.mul_mem_mul hqe hw
  induction k with
  | zero => exact ⟨0, P.zero_mem, by simp⟩
  | succ k ih =>
    obtain ⟨p, hp, hfp⟩ := ih
    obtain ⟨q, hq, -, hqe⟩ := (memC _ _).1 (hCj k hfp)
    refine ⟨p + q, P.add_mem hp hq, ?_⟩
    rw [show f - (p + q) = f - p - q by ring]
    exact hqe

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesLogVectorFieldsDeterminant
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

theorem GlobalTheory.LogPole.exists_coord_logDet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)) (x₀ : TF.Y.X), x₀ ∈ U.1 → ∃ (x : Fin Dw.dim → Γ(TF.Y.X, U.1)) (U' : TF.Y.X.affineOpens) (hU' : U'.1 ≤ U.1), x₀ ∈ U'.1 ∧ TopForm.IsFrame (TopForm.dOn TF.Y.s fun i => resG TF.Y.X hU' (x i)) ∧ (LogKS.boundary TF.Y).ideal U' = Ideal.span {resG TF.Y.X hU' (logDet (fun j => (b j).1) x)} := by
  intro E _ _ _ H Dw l Xo c TF U b x₀ hx₀
  classical
  have hres : ∀ (V W : TF.Y.X.Opens) (hW : IsAffineOpen W) (h : W ≤ V) (hVU : V ≤ U.1)
      (f : Fin Dw.dim → Γ(TF.Y.X, U.1)), TopForm.IsFrame (TopForm.dOn TF.Y.s fun i => resG TF.Y.X hVU (f i)) →
      TopForm.IsFrame (TopForm.dOn TF.Y.s fun i => resG TF.Y.X (h.trans hVU) (f i)) := by
    intro V W hW h hVU f hf
    have h' := hf.res hW h
    rw [TopForm.resForm_dOn] at h'
    simpa only [LB.resG_resG] using h'
  obtain ⟨hreg, m, a, J, hRsp, hIa⟩ := _root_.GlobalTheory.SncStalk.stalk_snc TF.Y.X (LogKS.boundary TF.Y) TF.snc U x₀ hx₀
  haveI := TF.smooth
  obtain ⟨hfp, hfree, hfin, hrank⟩ := GlobalTheory.T.smooth_affineOpen_finitePresentation_stalkKaehler_free_rank c.F TF.Y.X TF.Y.s Dw.dim U x₀ hx₀
  letI : Algebra c.F Γ(TF.Y.X, U.1) := (algX TF.Y.s U.1).toAlgebra
  letI : Algebra Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) :=
    TopCat.Presheaf.algebra_section_stalk TF.Y.X.presheaf ⟨x₀, hx₀⟩
  letI : Algebra c.F (TF.Y.X.presheaf.stalk x₀) :=
    ((TF.Y.X.presheaf.germ U.1 x₀ hx₀).hom.comp (algX TF.Y.s U.1)).toAlgebra
  haveI : IsScalarTower c.F Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hloc := U.2.isLocalization_stalk ⟨x₀, hx₀⟩
  haveI : IsNoetherianRing Γ(TF.Y.X, U.1) := Algebra.FiniteType.isNoetherianRing c.F _
  haveI : IsNoetherianRing (TF.Y.X.presheaf.stalk x₀) :=
    IsLocalization.isNoetherianRing (U.2.primeIdealOf ⟨x₀, hx₀⟩).asIdeal.primeCompl _ inferInstance
  have h3 := _root_.GlobalTheory.exists_coords_extending_regularParams c.F Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀)
    (U.2.primeIdealOf ⟨x₀, hx₀⟩).asIdeal Dw.dim hrank m a hRsp
  obtain ⟨x, e, hxe, bs, hbs⟩ := h3
  have hxe' : (fun j => x (e j)) = a := funext hxe
  have hI : ((LogKS.boundary TF.Y).ideal U).map (algebraMap Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀)) =
      Ideal.span {algebraMap Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) (∏ j ∈ J, x (e j))} := by
    simp only [hxe]; exact hIa
  have hspan : ∀ D : Derivation ℤ Γ(TF.Y.X, U.1) Γ(TF.Y.X, U.1),
      (∀ c', D (algebraMap c.F Γ(TF.Y.X, U.1) c') = 0) → (∀ f ∈ (LogKS.boundary TF.Y).ideal U, D f ∈ (LogKS.boundary TF.Y).ideal U) →
      ∃ cf : Fin Dw.dim → Γ(TF.Y.X, U.1), D = ∑ j, cf j • (b j).1 := by
    intro D h0 h1
    let D' : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U := ⟨D, h0, h1⟩
    refine ⟨b.repr D', ?_⟩
    have := congrArg Subtype.val (b.sum_repr D')
    rw [Submodule.coe_sum] at this
    exact this.symm
  have h4 := _root_.GlobalTheory.logDet_local_eq_unit_mul_prod c.F Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) (U.2.primeIdealOf ⟨x₀, hx₀⟩).asIdeal
    Dw.dim m x e J (by simp only [hxe]; exact hRsp) ⟨bs, hbs⟩ ((LogKS.boundary TF.Y).ideal U) hI
    (fun j => (b j).1) (fun j c' => (b j).2.1 c') (fun j => (b j).2.2) hspan
  obtain ⟨u, hu⟩ := h4
  have hd : ((LogKS.boundary TF.Y).ideal U).map (TF.Y.X.presheaf.germ U.1 x₀ hx₀).hom =
      Ideal.span {(TF.Y.X.presheaf.germ U.1 x₀ hx₀).hom (logDet (fun j => (b j).1) x)} := by
    change ((LogKS.boundary TF.Y).ideal U).map (algebraMap Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀)) =
      Ideal.span {algebraMap Γ(TF.Y.X, U.1) (TF.Y.X.presheaf.stalk x₀) (logDet (fun j => (b j).1) x)}
    exact hI.trans ((Ideal.span_singleton_mul_left_unit u.isUnit _).symm.trans (congrArg (fun y => Ideal.span {y}) hu.symm))
  have h5 := GlobalTheory.T.idealSheaf_eq_span_on_basicOpens_of_stalk_principal TF.Y.X (LogKS.boundary TF.Y) U x₀ hx₀ _ inferInstance hd
  obtain ⟨s₂, hs₂, hid⟩ := h5
  have h2 := GlobalTheory.T.exists_basicOpen_topFormFrame_of_stalkKaehlerBasis c.F TF.Y.X TF.Y.s Dw.dim U x₀ hx₀ x ⟨bs, hbs⟩
  obtain ⟨s₁, hs₁, hfr⟩ := h2
  have hle₁ : TF.Y.X.basicOpen (s₁ * s₂) ≤ TF.Y.X.basicOpen s₁ := by
    rw [Scheme.basicOpen_mul]; exact inf_le_left
  have hle₂ : TF.Y.X.basicOpen (s₁ * s₂) ≤ TF.Y.X.basicOpen s₂ := by
    rw [Scheme.basicOpen_mul]; exact inf_le_right
  refine ⟨x, TF.Y.X.affineBasicOpen (s₁ * s₂), TF.Y.X.basicOpen_le _, ?_, ?_, hid _ hle₂⟩
  · show x₀ ∈ TF.Y.X.basicOpen (s₁ * s₂)
    rw [Scheme.basicOpen_mul]; exact ⟨hs₁, hs₂⟩
  · exact hres _ _ (U.2.basicOpen (s₁ * s₂)) hle₁ _ x hfr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeMulPrimePowMemConductor
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open IsDedekindDomain
open GlobalTheory.CMVal (OF Af lattice IsBaseCond IsFinSetSplitPlacesCoprimeConductor condQ hatO)
open GlobalTheory.LatVal (OneOver)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (a0)

namespace GlobalTheory.HilbFam.CondNumber

theorem exists_mul_pow_mem {K : Type} [Field K] [NumberField K] {l : ℕ} (hl : l.Prime) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ M j : ℕ, ¬ l ∣ M ∧ (M : 𝓞 K) * (l : 𝓞 K) ^ j ∈ I := by
  have h0 : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  obtain ⟨j, M, hM, he⟩ := Nat.exists_eq_pow_mul_and_not_dvd h0 l hl.ne_one
  refine ⟨M, j, hM, ?_⟩
  have := Ideal.absNorm_mem I
  rw [he] at this
  push_cast at this
  rwa [mul_comm] at this

theorem mem_of_forall_pow {R : Type} [CommRing R] [IsDedekindDomain R] {I : Ideal R} (hI : I ≠ ⊥) {x : R}
    (h : ∀ (v : HeightOneSpectrum R) (n : ℕ), v.asIdeal ^ n ∣ I → x ∈ v.asIdeal ^ n) : x ∈ I := by
  have e := Ideal.iInf_maxPowDividing_eq (I := I) hI
  rw [← e, Submodule.mem_iInf]
  intro v
  apply h v
  rw [Ideal.dvd_iff_le]
  exact e.ge.trans (iInf_le _ v)

theorem exists_mem_condQ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))), l.Prime → IsBaseCond 𝔣 → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) → ∃ M : ℕ, ¬ l ∣ M ∧ ((M * l ^ a0 𝔣 l : ℕ) : OF E) ∈ condQ 𝔣 Q := by
  intro E _ _ _ l 𝔣 Q hl h𝔣 hQ
  obtain ⟨M₁, j, hM₁, hj⟩ := exists_mul_pow_mem hl h𝔣.1
  have h1 : (M₁ : OF E) * (l : OF E) ^ a0 𝔣 l ∈ 𝔣 := by
    refine mem_of_forall_pow h𝔣.1 fun v n hn => ?_
    by_cases hv : (l : OF E) ∈ v.asIdeal
    · have hfin : FiniteMultiplicity v.asIdeal 𝔣 :=
        FiniteMultiplicity.of_not_isUnit v.irreducible.not_isUnit h𝔣.1
      have hle : n ≤ a0 𝔣 l :=
        (hfin.le_multiplicity_of_pow_dvd hn).trans (GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.expIn_le_maxConductorExponentOverPrime h𝔣 hv)
      exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hle (Ideal.pow_mem_pow hv _))
    · have h2 := Ideal.le_of_dvd hn hj
      have := v.isPrime
      rcases Ideal.IsPrime.mem_pow_mul v.asIdeal h2 with h3 | h3
      · exact Ideal.mul_mem_right _ _ h3
      · exact absurd (v.isPrime.mem_of_pow_mem _ h3) hv
  have h2 : ∀ q : HeightOneSpectrum (OF E), ∃ M : ℕ, ¬ l ∣ M ∧ (q ∈ Q → (M : OF E) ∈ q.asIdeal) := by
    intro q
    obtain ⟨M, i, hM, hi⟩ := exists_mul_pow_mem hl q.ne_bot
    refine ⟨M, hM, fun hq => ?_⟩
    rcases q.isPrime.mem_or_mem hi with h3 | h3
    · exact h3
    · exact absurd (q.isPrime.mem_of_pow_mem _ h3) (hQ q hq)
  choose N hN hNq using h2
  refine ⟨M₁ * ∏ q ∈ Q, N q, ?_, ?_⟩
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    · exact hM₁ h
    · obtain ⟨q, -, hq⟩ := (Prime.dvd_finsetProd_iff hl.prime _).1 h
      exact hN q hq
  · have h3 : (∏ q ∈ Q, (N q : OF E)) ∈ ∏ q ∈ Q, q.asIdeal := Ideal.prod_mem_prod fun q hq => hNq q hq
    have h4 := Ideal.mul_mem_mul h1 h3
    unfold condQ
    convert h4 using 1
    push_cast
    ring

end GlobalTheory.HilbFam.CondNumber
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectedLocIsoOfDefectCoboundary
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_corr_of_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Par s₀ → ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ → ∀ E : GlobForm s₀ →+ C0 S'.F, (∀ w, S'.IsIdealValuedLiftSystemCochain (E w)) → (∀ (r : R) w, E (π r • w) = r • E w) → (∀ (w : GlobForm s₀) U V a, θ U V a (w.1 U) = d0 S'.F (E w) U V a) → ∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hpar S S' Φ θ hθ E hEI hEs hEd

  have hext : ∀ U : AffOp X₀, ∃! η : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj U,
      (∀ b w, η (S.p U b • w) = (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) b * η w) ∧
      (∀ w, η w ∈ I.map (algebraMap R (S'.F.obj U))) ∧ ∀ w : GlobForm s₀, η (w.1 U) = E w U := fun U ↦
    exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar U (S.F.obj U) (S'.F.obj U) (S.p U) (S.semi U)
      (S.surj U) (S.ker U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) ((Pi.evalAddMonoidHom _ U).comp E)
      (fun r w ↦ by simp [hEs]) (fun w ↦ hEI w U)

  choose η hη using fun U ↦ (hext U).exists
  have hψ : ∀ U : AffOp X₀, ∃ ψ : S.F.obj U →ₐ[R] S'.F.obj U,
      IsTheta I (S.p U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) ψ (-η U) := fun U ↦
    (_root_.GlobalTheory.LiftSys.theta_classify R R₀ (S.F.obj U) (Sec s₀ U.unop.1) (S'.F.obj U) I hI π hπ (S.p U) (S.semi U) (S.surj U)
      (S.ker U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U)).2 (-η U)
      (fun b w ↦ by rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, (hη U).1, mul_neg])
      (fun w ↦ by rw [AddMonoidHom.neg_apply]; exact neg_mem ((hη U).2.1 w))
  choose ψ hψ using hψ
  have hψv : ∀ U b, ψ U b = Φ.φ U b + η U (D R₀ (Sec s₀ U.unop.1) (S.p U b)) := fun U b ↦ by
    have h := (hψ U).der b
    rw [AddMonoidHom.neg_apply] at h
    change -η U _ = Φ.φ U b - ψ U b at h
    linear_combination h
  refine ⟨ψ, fun U b ↦ ?_, fun U V a b ↦ ?_⟩
  · rw [hψv, map_add (f := _), Φ.red, (S'.ker U _).2 ((hη U).2.1 _), add_zero]
  ·
    let α : S.F.obj U →ₐ[R] S'.F.obj V := (mp S'.F a).comp (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U)
    let χ : Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V := θ U V a + (mp S'.F a).toAddMonoidHom.comp (η U) -
      (η V).comp (p1 (OAff s₀) a).toAddMonoidHom
    have hχ : ∀ w, χ w = θ U V a w + mp S'.F a (η U w) - η V (p1 (OAff s₀) a w) := fun _ ↦ rfl

    have hmemV : ∀ w, η V w ∈ I.map (algebraMap R (S'.F.obj V)) := (hη V).2.1
    have hdiff : ∀ c : S.F.obj U, ∀ x ∈ I.map (algebraMap R (S'.F.obj V)),
        (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V) (mp S.F a c) * x = α c * x := by
      intro c x hx
      have h1 := (hθ U V a).der c
      have h2 : α c - (Φ.φ V : S.F.obj V →ₐ[R] S'.F.obj V) (mp S.F a c) ∈ I.map (algebraMap R (S'.F.obj V)) :=
        h1 ▸ (hθ U V a).mem _
      have h3 := mul_eq_zero_of_mem_map hI h2 hx
      rw [sub_mul] at h3
      exact (sub_eq_zero.1 h3).symm
    have hu := exists_unique_formExt R R₀ I hI π hπ hk X₀ s₀ hpar U (S.F.obj U) (S'.F.obj V) (S.p U) (S.semi U)
      (S.surj U) (S.ker U) α 0 (fun r w ↦ by simp) (fun w ↦ zero_mem _)
    have hχ0 : χ = 0 := by
      refine hu.unique ⟨fun b w ↦ ?_, fun w ↦ ?_, fun w ↦ ?_⟩ ⟨fun b w ↦ by simp, fun w ↦ zero_mem _, fun w ↦ rfl⟩
      · rw [hχ, hχ, (hθ U V a).smul, (hη U).1, oneFormsMapOfFunctorMorphism_smul, map_mul]
        rw [← S.nat a b, (hη V).1, hdiff _ _ (hmemV _)]
        simp only [α, AlgHom.coe_comp, Function.comp_apply]
        ring
      · rw [hχ]
        exact sub_mem (add_mem ((hθ U V a).mem w) (algHom_mem_map I _ ((hη U).2.1 w))) (hmemV _)
      · rw [hχ, hEd, amitsur_d0_apply, (hη U).2.2, ← w.2 a, (hη V).2.2]
        simp
    have h0 : χ (D R₀ (Sec s₀ U.unop.1) (S.p U b)) = 0 := by rw [hχ0]; rfl
    rw [hχ, p1_D] at h0
    have hn : mp (OAff s₀) a (S.p U b) = S.p V (mp S.F a b) := (S.nat a b).symm
    rw [hn] at h0
    have h1 := (hθ U V a).der b
    simp only [α, AlgHom.coe_comp, Function.comp_apply] at h1
    rw [hψv, hψv, map_add (f := _)]
    simp only [AlgEquiv.coe_toAlgHom] at h0 h1 ⊢
    linear_combination h0 - h1

end GlobalTheory.LiftSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalStructureMapOfLineBundleIsoRescaled
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PkgBaseChange
open GlobalTheory.UU

theorem surjective_of_cube {S' : Scheme.{0}} (G' : Over S') [GrpObj G']
    (h3 : Function.Surjective (G3 G').hom.appTop.hom) : Function.Surjective G'.hom.appTop.hom := by
  let s : G' ⟶ G3 G' := lift (𝟙 G') (lift 1 1)
  have hs : s.left ≫ (fst G' (G' ⊗ G')).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hw : s.left ≫ (G3 G').hom = G'.hom := Over.w s
  intro g
  obtain ⟨c, hc⟩ := h3 ((fst G' (G' ⊗ G')).left.appTop.hom g)
  refine ⟨c, ?_⟩
  have e1 : G'.hom.appTop.hom c = s.left.appTop.hom ((G3 G').hom.appTop.hom c) := by
    rw [← hw, Scheme.Hom.comp_appTop]; rfl
  have e2 : s.left.appTop.hom ((fst G' (G' ⊗ G')).left.appTop.hom g) = g := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs]; rfl
  rw [e1, hc, e2]

theorem exists_isCPMap_of_lbIso : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
    (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (F : G'.left ⟶ G.left) (hw : F ≫ G.hom = G'.hom ≫ f),
    (∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) →
    Function.Surjective (G3 G').hom.appTop.hom → ∀ (P : GlobalTheory.UU.CP G) (P' : GlobalTheory.UU.CP G'),
    LBIso P'.L.L (P.L.L.pull F) → ∃ w, GlobalTheory.UU.IsCPMap P' P f F hw w := by
  intro S S' f G _ _ G' _ _ F hw mul h3 M M' ⟨w, hg⟩
  have h1 := surjective_of_cube G' h3
  obtain ⟨rig, hr, c, s, hs, h₂, h₃, H⟩ := exists_isCPMap M mul M'.L.L M'.L.isLB w hg
  let N : CP G' := ⟨⟨M'.L.L, rig, M'.L.isLB, hr⟩, c, s, hs, h₂, h₃⟩
  obtain ⟨a, ha⟩ := GlobalTheory.AbPackage.exists_unit_ratio M'.L.isLB (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1)
    hr M'.L.rigGen
  let b : Γ(G'.left, ⊤)ˣ := pullU G'.hom ⊤ a
  have es : ∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (J), Good M'.L.L z J → val s r z J = val M'.sym r z J :=
    gen_unique M'.L.isLB G'.hom (1 : 𝟙_ (Over S') ⟶ G').left (Over.w _) h1 hs M'.sym_gen
      fun y J hJ => (N.val_sym_one hJ).trans (M'.val_sym_one hJ).symm
  have ec : ∀ (T : Over S') (z : T.left) (J), Good M'.L.L z J → ∀ x y u : T ⟶ G',
      cubV c z J x y u = cubV M'.c z J x y u := fun T z J hJ x y u =>
    gen_unique M'.L.isLB (φ := thφ G' (x3 G')) (ε := thε) (G3 G').hom
      (lift (1 : 𝟙_ (Over S') ⟶ G') (lift 1 1)).left (Over.w _) h3 c.isGen M'.c.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV M'.c hJ).face 1 1).symm) _ _ z J hJ
  refine ⟨scaleGen b w, mul, scaleGen_isGen b hg, fun T z J' J hJ' hJ W hW => ?_⟩
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
    ∀ x, W₀ x = gw w x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : (T.left.presheaf.stalk z)ˣ, α = gm (Y := T.left) T.hom z ⊤ a := ⟨_, rfl⟩
  have e : ∀ x, W x = α * W₀ x := fun x => by
    have hm : x.left z ∈ (M.L.L.pull F).U (fun _ => J (x.left ≫ F)) ⊓ M'.L.L.U (J' x.left) :=
      ⟨mem_pull.2 (hJ (x.left ≫ F)), hJ' x.left⟩
    rw [hW, hW₀, hα, ← Over.w x]
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res x.left z le_top hm b).trans
      (gm_pull x.left G'.hom z ⊤ trivial a)) rfl)
  obtain ⟨a₁, a₂, a₃⟩ := H.vals T z J' J hJ' hJ W₀ hW₀
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · refine a₁.trans ((congrArg (W₀ 1 * ·) (ha _ T.hom z J' hJ')).trans ?_)
    rw [e, hα, mul_comm _ (W₀ 1), _root_.mul_assoc]
  · have q : val M.sym (x.left ≫ F) z J * W₀ x = W₀ x⁻¹ * val M'.sym x.left z J' :=
      (a₂ x).trans (congrArg (W₀ x⁻¹ * ·) (es _ x.left z J' hJ'))
    rw [e, e, mul_left_comm, q, _root_.mul_assoc]
  · have q := (a₃ x y u).trans (congrArg (W₀ (x * y * u) * W₀ x * W₀ y * W₀ u * ·) (ec T z J' hJ' x y u))
    simp only [e]
    apply Additive.ofMul.injective
    have q' := congrArg Additive.ofMul q
    simp only [ofMul_mul] at q' ⊢
    linear_combination (norm := abel) q'

end GlobalTheory.PkgBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalTrivialisationSplitTorusField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TorusCubTriv

open GlobalTheory GlobalTheory.UU GlobalTheory.EvenGenTorus TorusCube

theorem exists_cubTriv : ∀ (k : Type) [CommRing k], IsField k → ∀ (G₀ : Over (Sp k)) [GrpObj G₀] [IsCommMonObj G₀] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (P₀ : GlobalTheory.UU.CP G₀) (i : splitTorus (Sp k) X ⟶ G₀), IsMonHom i → Nonempty (GlobalTheory.UU.CubTriv P₀.c i) := by
  intro k _ hk G₀ _ _ X _ _ _ P₀ i hi
  letI := hk.toField
  haveI := hi
  haveI : IsAffine (splitTorus (Sp k) X).left := isAffine_of_isAffineHom (splitTorus (Sp k) X).hom
  haveI := GlobalTheory.SS.LiftTorus.subsingleton_pic_torus k X
  obtain ⟨τ, hτ⟩ := GlobalTheory.LB.exists_isGen_of_subsingleton_pic_top
    (ReciprocityTheory.ChartRestriction.G.Semi.LB.isLB_linComb P₀.L.isLB (K := PUnit) (fun _ => i.left) (fun _ => 1))
  have e1 : (1 : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X).left ≫ i.left = (1 : splitTorus (Sp k) X ⟶ G₀).left := by
    rw [← Over.comp_left, MonObj.one_comp]
  obtain ⟨σ, hσ, vσ⟩ := exists_gen (φ' := ![i.left, (1 : splitTorus (Sp k) X ⟶ G₀).left]) (ε' := ![1, -1]) P₀.L.isLB
    (fun U _ h => (Fintype.prod_sum_type _).trans (by simp [Fin.prod_univ_two, e1]))
    (LB.mulGen _ _ _ _ _ τ (LB.invGen _ _ _ (LB.pullGen P₀.L.L (fun _ : PUnit => i.left) (fun _ => 1) τ
      (1 : splitTorus (Sp k) X ⟶ splitTorus (Sp k) X).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hτ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _)))
  have v : ∀ (T : Over (Sp k)) (x : T ⟶ splitTorus (Sp k) X) (z : T.left) (J), Good P₀.L.L z J →
      val σ x.left z J = val τ x.left z J * (val τ (1 : T ⟶ splitTorus (Sp k) X).left z J)⁻¹ := by
    intro T x z J hJ
    rw [vσ _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, ← Over.comp_left, MonObj.comp_one]
  refine ⟨⟨σ, hσ, fun T x y u z J hJ => ?_⟩⟩
  have a := cube k X G₀ i P₀.L P₀.c τ hτ T x y u z J hJ
  simp only [v T _ z J hJ]
  apply Additive.ofMul.injective
  have a' := congrArg Additive.ofMul a
  simp only [ofMul_mul, ofMul_inv] at a' ⊢
  linear_combination (norm := abel) a'

end GlobalTheory.Mum.TorusCubTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorMumfordBundleInvPullbackPrimitiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_mumfordBundle_inv_pullback_primitive : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Sp A)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (_ : CubicalStr B M), IsAbelianScheme B → ∃ u : LB.Gen (abelian₂ B (LB.LinComb M.L (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1])), u.IsGen := by
  first | exact @GlobalTheory.PolDeg.NegPrim.lam_negPull_sub_isTrivial | exact GlobalTheory.PolDeg.NegPrim.lam_negPull_sub_isTrivial | (intros; apply GlobalTheory.PolDeg.NegPrim.lam_negPull_sub_isTrivial <;> assumption)
end

