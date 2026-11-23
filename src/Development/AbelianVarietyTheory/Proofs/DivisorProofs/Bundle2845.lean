module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2821
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2385
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2604
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1820
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSideV
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2614
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PreimageEqTopOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicGenericFibreQuotientStrictHenselisationNoTors
section
open GlobalTheory.EtC

namespace GlobalTheory.QPic

theorem pic0 : ∀ (R : Type) [CommRing R], (∀ P : Ideal R, P.IsPrime → P.IsMaximal) → ∀ c : CommRing.Pic R, c = 1 := GlobalTheory.T.pic_eq_one_of_forall_prime_maximal

theorem incomp : ∀ (B O : Type) [CommRing B] [CommRing O] [Algebra B O], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra B O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra B E) (_ : Algebra.Etale B E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[B] Si i)) → ∀ p p' : Ideal O, p.IsPrime → p'.IsPrime → p ≤ p' → p.comap (algebraMap B O) = p'.comap (algebraMap B O) → p = p' := GlobalTheory.T.ind_etale_prime_comparison

theorem poly : ∀ (T : Type) [CommRing T] [IsDomain T] (P P' : Ideal (Polynomial T)), P.IsPrime → P'.IsPrime → P ≤ P' → P ≠ ⊥ → P'.comap (algebraMap T (Polynomial T)) = ⊥ → P = P' := by
  intro T _ _ P P' hP hP' hle h0 hC
  let K := FractionRing T
  letI : Algebra (Polynomial T) (Polynomial K) := Polynomial.algebra T K
  haveI : IsLocalization (Submonoid.map Polynomial.C (nonZeroDivisors T)) (Polynomial K) :=
    Polynomial.isLocalization (nonZeroDivisors T) K
  set M := Submonoid.map Polynomial.C (nonZeroDivisors T) with hM
  have hdisj' : Disjoint (M : Set (Polynomial T)) (P' : Set (Polynomial T)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    have : s ∈ P'.comap (algebraMap T (Polynomial T)) := by
      rw [Ideal.mem_comap, Polynomial.algebraMap_eq]; exact hsP
    rw [hC, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hs this
  have hdisj : Disjoint (M : Set (Polynomial T)) (P : Set (Polynomial T)) :=
    hdisj'.mono_right hle
  have hPK := IsLocalization.isPrime_of_isPrime_disjoint M (Polynomial K) P hP hdisj
  have hP'K := IsLocalization.isPrime_of_isPrime_disjoint M (Polynomial K) P' hP' hdisj'
  have hc := IsLocalization.under_map_of_isPrime_disjoint M (Polynomial K) hP hdisj
  have hc' := IsLocalization.under_map_of_isPrime_disjoint M (Polynomial K) hP' hdisj'
  have hM0 : (0 : Polynomial T) ∉ M := by
    intro h
    obtain ⟨s, hs, hs0⟩ := Submonoid.mem_map.mp h
    exact nonZeroDivisors.ne_zero hs (Polynomial.C_eq_zero.mp hs0)
  have hne : P.map (algebraMap (Polynomial T) (Polynomial K)) ≠ ⊥ := by
    intro hb
    apply h0
    rw [← hc, hb, eq_bot_iff]
    intro x hx0
    have hx : algebraMap (Polynomial T) (Polynomial K) x = 0 := (Ideal.mem_bot).mp hx0
    exact (Ideal.mem_bot).mpr (IsLocalization.injective (Polynomial K) (le_nonZeroDivisors_of_noZeroDivisors hM0)
      (hx.trans (map_zero _).symm))
  have hmax : (P.map (algebraMap (Polynomial T) (Polynomial K))).IsMaximal := hPK.isMaximal hne
  have heq := hmax.eq_of_le hP'K.ne_top (Ideal.map_mono hle)
  rw [← hc, ← hc', heq]

theorem pic_transfer {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) (q : ℕ)
    (h : ∀ c : CommRing.Pic S, c ^ q = 1 → c = 1) (c : CommRing.Pic R) (hc : c ^ q = 1) : c = 1 := by
  have h1 : CommRing.Pic.mapRingHom e.toRingHom c = 1 := h _ (by rw [← map_pow, hc, map_one])
  have h2 : CommRing.Pic.mapRingHom e.symm.toRingHom (CommRing.Pic.mapRingHom e.toRingHom c) = c := by
    rw [CommRing.Pic.mapRingHom_mapRingHom]
    have : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by ext x; simp
    rw [this, CommRing.Pic.mapRingHom_id_apply]
  rw [← h2, h1, map_one]

theorem primes_eq (T O : Type) [CommRing T] [IsDomain T] [CommRing O] [IsDomain O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O]
    (hind : ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i))
    (p p' : Ideal O) [p.IsPrime] [p'.IsPrime] (hle : p ≤ p') (h0 : p ≠ ⊥)
    (hT : p'.comap (algebraMap T O) = ⊥) : p = p' := by
  have hinc := incomp (Polynomial T) O hind
  refine hinc p p' inferInstance inferInstance hle ?_
  refine poly T _ _ (Ideal.comap_isPrime _ _) (Ideal.comap_isPrime _ _) (Ideal.comap_mono hle) ?_ ?_
  · intro hb
    have : (⊥ : Ideal O).comap (algebraMap (Polynomial T) O) = p.comap (algebraMap (Polynomial T) O) := by
      apply le_antisymm (Ideal.comap_mono bot_le); rw [hb]; exact bot_le
    exact h0 (hinc ⊥ p Ideal.isPrime_bot inferInstance bot_le this).symm
  · rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]; exact hT

end GlobalTheory.QPic


open GlobalTheory.QPic in
theorem GlobalTheory.pic_generic_fibre_quotient_strictHenselisation_no_torsion : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (O : Type) [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (IsLocalRing.ResidueField O)], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (E : Type) (_ : CommRing E) (_ : Algebra (Polynomial T) E) (_ : Algebra.Etale (Polynomial T) E) (P : Ideal E) (_ : P.IsPrime), Nonempty (Localization.AtPrime P ≃ₐ[(Polynomial T)] Si i)) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A] (π : O →ₐ[Polynomial T] A), Function.Surjective π → ∀ c : CommRing.Pic (TensorProduct T (FractionRing T) A), c ^ q = 1 → c = 1 := by
  intro q _ T _ _ _ hAIC hq O _ _ _ _ _ _ hind A _ _ _ _ π hπ c hc
  haveI : IsIntegrallyClosed T := GlobalTheory.LocIndEtale.isIntegrallyClosed_of_forall_monic_root T hAIC
  haveI : IsDomain O := (GlobalTheory.indEtale_isDomain_isIntegrallyClosed (Polynomial T) O hind).1
  let eA := Localization.tensorRightAlgEquiv (nonZeroDivisors T) A
  by_cases hI : RingHom.ker (π : O →+* A) = ⊥
  · have hinj : Function.Injective π := (RingHom.injective_iff_ker_eq_bot _).mpr hI
    let eπ : O ≃ₐ[T] A := AlgEquiv.ofBijective (π.restrictScalars T) ⟨hinj, hπ⟩
    let e1 : TensorProduct T (FractionRing T) A ≃ₐ[T] TensorProduct T (FractionRing T) O :=
      Algebra.TensorProduct.congr AlgEquiv.refl eπ.symm
    let e2 := Localization.tensorRightAlgEquiv (nonZeroDivisors T) O
    refine pic_transfer (e1.toRingEquiv.trans e2.toRingEquiv) q ?_ c hc
    exact GlobalTheory.pic_localization_strictHenselisation_no_torsion T O q ⟨inferInstance, hAIC⟩ hq
      (Nat.pos_of_ne_zero (NeZero.ne q)) hind
  · refine pic_transfer eA.toRingEquiv q (fun c' _ => pic0 _ ?_ c') c hc
    intro Q hQ
    obtain ⟨Q', hQ'max, hle⟩ := Ideal.exists_le_maximal Q hQ.ne_top
    suffices hQQ : Q = Q' by rw [hQQ]; exact hQ'max
    set L := Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors T))
    have hQ'p : Q'.IsPrime := hQ'max.isPrime
    set p := (Q.comap (algebraMap A L)).comap (π : O →+* A) with hpdef
    set p' := (Q'.comap (algebraMap A L)).comap (π : O →+* A) with hp'def
    have hpp : p = p' := by
      refine primes_eq T O hind p p' (Ideal.comap_mono (Ideal.comap_mono hle)) ?_ ?_
      · intro hb
        apply hI
        rw [eq_bot_iff, ← hb]
        intro x hx
        rw [RingHom.mem_ker] at hx
        simp [hpdef, hx]
      · rw [eq_bot_iff]
        intro t ht
        rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap] at ht
        rw [Ideal.mem_bot]
        by_contra ht0
        have hcomm : (π : O →+* A) (algebraMap T O t) = algebraMap T A t := by
          rw [IsScalarTower.algebraMap_apply T (Polynomial T) O, IsScalarTower.algebraMap_apply T (Polynomial T) A]
          exact π.commutes _
        rw [hcomm] at ht
        have hu : IsUnit (algebraMap A L (algebraMap T A t)) :=
          IsLocalization.map_units L (⟨algebraMap T A t, t, mem_nonZeroDivisors_of_ne_zero ht0, rfl⟩ :
            Algebra.algebraMapSubmonoid A (nonZeroDivisors T))
        exact hQ'p.ne_top (Ideal.eq_top_of_isUnit_mem _ ht hu)
    have hqq : Q.comap (algebraMap A L) = Q'.comap (algebraMap A L) := by
      rw [← Ideal.map_comap_of_surjective (π : O →+* A) hπ (Q.comap (algebraMap A L)),
        ← Ideal.map_comap_of_surjective (π : O →+* A) hπ (Q'.comap (algebraMap A L))]
      exact congrArg _ hpp
    rw [← IsLocalization.map_under (Algebra.algebraMapSubmonoid A (nonZeroDivisors T)) L Q,
      ← IsLocalization.map_under (Algebra.algebraMapSubmonoid A (nonZeroDivisors T)) L Q']
    exact congrArg (Ideal.map (algebraMap A L)) hqq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveHodgeToOmegaSpanModMaximal
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem sup_smul_top_eq_top_of_span {R M N : Type} [CommRing R] (I : Ideal R) [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module (R ⧸ I) N] (om : M →ₛₗ[algebraMap R (R ⧸ I)] N)
    (hinj : Function.Injective (PDiv.liftSemi om)) (S : Submodule R M)
    (hall : ∀ y : N, y ∈ Submodule.span (R ⧸ I) (om '' (S : Set M))) :
    S ⊔ I • (⊤ : Submodule R M) = ⊤ := by
  let f := TensorProduct.mk R (R ⧸ I) M 1
  have hsf : ∀ x, PDiv.liftSemi om (f x) = om x := fun x => by simp [f]
  have hmemK : ∀ x, f x ∈ Submodule.span (R ⧸ I) (f '' (S : Set M)) := by
    intro x
    have h1 : PDiv.liftSemi om (f x) ∈ Submodule.map (PDiv.liftSemi om)
        (Submodule.span (R ⧸ I) (f '' (S : Set M))) := by
      have himg : (⇑(PDiv.liftSemi om) ∘ ⇑f) '' (S : Set M) = om '' (S : Set M) :=
        Set.image_congr fun a _ => hsf a
      rw [Submodule.map_span, ← Set.image_comp, himg, hsf]
      exact hall _
    obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.1 h1
    have hz' : z = f x := hinj hzx
    subst hz'
    exact hz
  let Q : Submodule (R ⧸ I) ((R ⧸ I) ⊗[R] M) :=
    { carrier := Submodule.map f S
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := by
        intro a z hz
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
        refine Submodule.mem_map.2 ⟨r • w, Submodule.smul_mem _ r hw, ?_⟩
        rw [map_smul]
        exact (algebraMap_smul (R ⧸ I) r (f w)).symm }
  have hQ : Submodule.span (R ⧸ I) (f '' (S : Set M)) ≤ Q := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.mem_map_of_mem ha
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.1 (hQ (hmemK x))
  have hxy : x - y ∈ I • (⊤ : Submodule R M) := by
    have h0 : f (x - y) = 0 := by rw [map_sub, hyx, sub_self]
    have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul M I) h0
    rw [map_zero] at h2
    simp only [f, TensorProduct.mk_apply] at h2
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero] at h2
    exact h2
  have hx : x = y + (x - y) := by abel
  rw [hx]
  exact Submodule.add_mem_sup hy hxy

theorem psi_sup_smul_top_eq_top : GlobalTheory.Published.AbelianHodgeDeRham →
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (ψ : PrimitiveSubmodule A →ₗ[R] G.omega),
    (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
    ∀ I : Ideal R, I.IsMaximal → LinearMap.range ψ ⊔ I • (⊤ : Submodule R G.omega) = ⊤ := by
  intro hH p _ R _ N hN A _ g hA hg G t ψ hψ I hI
  obtain ⟨-, hBC, -⟩ := GlobalTheory.abelianDeRham_free_baseChange_rigid hH
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  have hNk : ((p : ℕ) : R ⧸ I) ^ N = 0 := by
    rw [← map_natCast (algebraMap R (R ⧸ I)), ← map_pow, hN, map_zero]
  have hk0 : ((p : ℕ) : R ⧸ I) = 0 := pow_eq_zero_iff'.1 hNk |>.1
  letI : GrpObj ((Over.pullback (spMap (algebraMap R (R ⧸ I)))).obj A) := Functor.grpObjObj
  have h := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A (spMap (algebraMap R (R ⧸ I)))
  have hAk : IsAbelianScheme ((Over.pullback (spMap (algebraMap R (R ⧸ I)))).obj A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ A hA
  obtain ⟨gk, hgk⟩ := GlobalTheory.AbVarRelDim.exists_relDim (R ⧸ I) _ hAk
  obtain ⟨ψk, hψk⟩ := GlobalTheory.T.exists_hodgeFiltration_to_pDivOmega_linearMap p (R ⧸ I) N hNk _ hAk (G.baseChange (R ⧸ I)) (t.baseChange h)
  have hsurj := _root_.GlobalTheory.PtExt.surjective_of_isCan_field hH p (R ⧸ I) hk0 _ gk hAk hgk _ _ ψk hψk
  have hbc := GlobalTheory.T.hodgeToOmega_canonical_extension_base_change p R (R ⧸ I) N hN A _ _ h hA hAk G _ t (t.baseChange h) ψ ψk hψ hψk
  rw [t.semiHom_baseChange h] at hbc
  have hF := (hBC R A g hA hg (R ⧸ I) _ _ h).2
  have hom := GlobalTheory.PDivGroup.omega_baseChange_bijective_of_isNilpotent p R (R ⧸ I) ⟨N, hN⟩ G

  let T : Submodule (R ⧸ I) (G.baseChange (R ⧸ I)).omega :=
    Submodule.span (R ⧸ I) ((G.toBase (R ⧸ I)).omega '' (LinearMap.range ψ : Set G.omega))
  have hle : PrimitiveSubmodule ((Over.pullback (spMap (algebraMap R (R ⧸ I)))).obj A) ≤
      Submodule.map (PrimitiveSubmodule _).subtype (T.comap ψk) := by
    refine hF.le.trans (Submodule.span_le.2 ?_)
    rintro _ ⟨c, hc, rfl⟩
    have hc' : (GlobalTheory.Published.AbelianDeRham.bcMor h).pull c ∈
        PrimitiveSubmodule ((Over.pullback (spMap (algebraMap R (R ⧸ I)))).obj A) :=
      hF ▸ Submodule.subset_span ⟨c, hc, rfl⟩
    refine ⟨⟨_, hc'⟩, ?_, rfl⟩
    show ψk ⟨_, hc'⟩ ∈ T
    rw [hbc ⟨c, hc⟩ hc']
    exact Submodule.subset_span ⟨ψ ⟨c, hc⟩, LinearMap.mem_range_self _ _, rfl⟩
  have hall : ∀ y, y ∈ T := by
    intro y
    obtain ⟨c, rfl⟩ := hsurj y
    obtain ⟨c', hc', he⟩ := Submodule.mem_map.1 (hle c.2)
    have : c' = c := Subtype.ext he
    subst this
    exact hc'
  exact sup_smul_top_eq_top_of_span I _ hom.1 _ hall

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationExtendsByNewTuplesKeepingLaws
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TupExt

open GlobalTheory.BigOn.Exp.TwConj

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 N : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D}
  [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}
  {j : Fin D.R.m} {V : NewLev D N} {X : NewFam A N} (Y : NewReal R V X)


set_option maxHeartbeats 2000000 in
theorem baseOf_ext {B : Base (Vc D j) (Wc D j)} (h : BaseOf R j B) : BaseOf (extR R Y) j B :=
  ⟨h.ψ, h.θ, h.sT, h.BS, h.BT, h.ΛS, h.ΛT, h.βS, h.βT, h.vac, h.Pg, h.mu0, h.eta, h.lam, h.delta, h.p, h.q, h.c⟩


set_option maxHeartbeats 2000000 in
theorem ext_ext : Ext T R κ v₀ O j (extR R Y) v₀ (fun i => omExt Y (O i)) := by
  refine ⟨fun τ h => (fixBase_ext Y j τ).2 h, fun τ ζ Φ Φ' h => ?_, ?_⟩
  · exact (h)
  · exact (by with_unfolding_all exact ((Ext.refl (T := T) (R := R) (κ := κ) (v₀ := v₀) (O := O) (j := j)).2.2 :))

end


set_option maxHeartbeats 2000000 in
theorem extend_tuples : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach →
  ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)),
    Formalism.IndefR.Links.HostHyp D → GlobalTheory.BigOn.Exp.TwConj.Laws T R F κ v₀ O ph j B →
    ∀ (N : Type) [Finite N] (χ : N → Formalism.L2.Host.HChar D.host.E) (xi : N → (AE D)ˣ →* Circle) (Q : N → Finset (Pl D.host.E))
      (xiR : N → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ),
      (∀ n, GlobalTheory.BigOn.Exp.TwConj.TwLev R (χ n) (xi n) (Q n) (xiR n)) → Function.Injective χ → (∀ n t, χ n ≠ R.xiH t) →
      (∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
        (∀ t, ∀ PP ∈ R.Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) ∧
          ∀ n, ∀ PP ∈ Q n, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) →
      ∃ (T0' : Type) (A' : FamIn D.what₂.LL G Pl0 T0' D.R.m) (R' : RealDat D A' T.Q.c.F) (F' : Face D A')
        (v₀' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (O' : ∀ i, OMDat T.toCore R' i Unit (fun _ => A'.μ0)),
        GlobalTheory.BigOn.Exp.TwConj.Laws T R' F' κ v₀' O' ph j B ∧ GlobalTheory.BigOn.Exp.TwConj.Ext T R κ v₀ O j R' v₀' O' ∧
          ∀ n, ∃ t', R'.xi t' = xi n ∧ R'.Q t' = Q n := by
  intro h1 _ _ h4 h5 D G _ _ Pl0 T0 A T _ R F κ v₀ O ph j B hH hL N _ χ xi Q xiR hV hi hn hQ
  obtain ⟨hC, hfin, ⟨hfw⟩, hio, hg, hp, hph, hB⟩ := hL
  let V : NewLev D N := ⟨χ, xi, Q, xiR⟩
  have hL' : (extL R.toLevCh V).Is (.inl A.μ0) := by
    have hL := hC.lev
    exact
      { mu0 := hL.mu0
        eta := hL.eta
        xi := Sum.rec hL.xi fun n => (hV n).xi
        xi_inj := by
          rintro (t | n) (t' | n') h
          · exact congrArg _ (hL.xi_inj h)
          · exact absurd h.symm (hn n' t)
          · exact absurd h (hn n t')
          · exact congrArg _ (hi h)
        xi_base := hL.xi_base
        xi_fin := Sum.rec hL.xi_fin fun n => (hV n).xi_fin
        xi_triv := Sum.rec hL.xi_triv fun n => (hV n).xi_triv
        xi_tame := Sum.rec hL.xi_tame fun n => (hV n).xi_tame
        Pg := hL.Pg
        Q_pl := Sum.rec hL.Q_pl fun n => (hV n).Q_pl
        Q_off := Sum.rec hL.Q_off fun n => (hV n).Q_off
        Q_de p hp := (hQ p hp).imp fun _ h => Sum.rec h.1 h.2
        Q_ram := Sum.rec hL.Q_ram fun n => (hV n).Q_ram
        chi := hL.chi
        xiR := Sum.rec hL.xiR fun n => (hV n).xiR
        βY := hL.βY
        βX := hL.βX
        βV := hL.βV
        βW := hL.βW }
  obtain ⟨X, Y0, h0⟩ := fam_stage (GlobalTheory.SideLevel.sideReal_moreLevel) hC hL' hV
  obtain ⟨Y, hC', hT⟩ := core_ext h4 GlobalTheory.HcPort.print_harishChandraModules h1 h5 (GlobalTheory.Chain.ParOfNodeGap.chainPar_of_nodeGap D hH.nodeGap) hC hL' Y0 h0
  have hg' : QGuard (extR R Y) := ⟨Sum.rec hg.1 fun n => (hV n).half, Sum.rec hg.2 fun n => (hV n).guard⟩
  exact ⟨T0 ⊕ N, extA A X, extR R Y, extF F X, v₀, fun i => omExt Y (O i),
    ⟨hC', inferInstance, ⟨fwExt Y hfw⟩, ioExt_ext R Y hio, hg', omPins_ext Y hT hp, phaseTie_ext Y hph, baseOf_ext Y hB⟩,
    ext_ext Y, fun n => ⟨.inr n, rfl, rfl⟩⟩

end GlobalTheory.TupExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SndPullCohomZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

theorem spOver_epsHom_ptV {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (v : epsR R ⟶ B)
    {D D' : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D) :
    (spOver (epsHom φ) ≫ ptV v x : Pt (A ⊗ B) (DualNumber D')) =
      ptV v (spOver φ ≫ x : Pt A D') := by
  have h1 : (epsHom φ).comp (TrivSqZeroExt.inlAlgHom R D D) = (TrivSqZeroExt.inlAlgHom R D' D').comp φ :=
    AlgHom.ext fun a ↦ by simp [epsHom]
  have h2 : (epsHom φ).comp (EpsWeil.epsMap R D) = EpsWeil.epsMap R D' :=
    DualNumber.algHom_ext (by simp [epsHom, EpsWeil.epsMap, DualNumber.lift_apply_apply])
  simp only [ptV, comp_lift, ← Category.assoc, spOver_comp, h1, h2]

theorem fst_ptV {A B : Over (Sp R)} [GrpObj A] [GrpObj B] {v : epsR R ⟶ B} (hv : IsTangent v)
    {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) :
    (spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x : Pt (A ⊗ B) D) = pt0 B x := by
  have h1 : (TrivSqZeroExt.fstHom R D D).comp (TrivSqZeroExt.inlAlgHom R D D) = AlgHom.id R D :=
    AlgHom.ext fun _ ↦ rfl
  have h2 : (TrivSqZeroExt.fstHom R D D).comp (EpsWeil.epsMap R D) =
      (Algebra.ofId R D).comp (TrivSqZeroExt.fstHom R R R) :=
    DualNumber.algHom_ext (by simp [EpsWeil.epsMap, DualNumber.lift_apply_apply])
  rw [ptV, pt0, comp_lift, ← Category.assoc, spOver_comp, h1, spOver_id, Category.id_comp,
    ← Category.assoc, spOver_comp, h2, ← spOver_comp, Category.assoc]
  congr 1
  ext1
  rw [Over.comp_left, Over.comp_left, spOver_left, spOver_left, Hom.one_def, Over.comp_left, Over.toUnit_left]
  have := hv
  unfold IsTangent at this
  erw [this]
  rfl

theorem sm_ptV {A B : Over (Sp R)} [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) {v : epsR R ⟶ B}
    (hv : IsTangent v) {D : Type} [CommRing D] [Algebra R D] {x : Pt A D}
    (hx : Sm (chartsA (A := A) (B := B) P) x) : Sm (X := A ⊗ B) P.U (ptV v x) := by
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, ?_⟩
  have hsurj : Surjective (spOver (TrivSqZeroExt.fstHom R D D)).left := by
    rw [spOver_left]
    refine GlobalTheory.TorusLift.surjective_specMap _ (fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩) ⟨2, ?_⟩
    rw [sq, Ideal.zero_eq_bot, eq_bot_iff]
    refine Ideal.mul_le.2 fun a ha b hb ↦ ?_
    have ha' : a.fst = 0 := ha
    have hb' : b.fst = 0 := hb
    rw [Ideal.mem_bot]
    ext <;> simp [ha', hb']
  have e : (spOver (TrivSqZeroExt.fstHom R D D) ≫ ptV v x : Pt (A ⊗ B) D).left =
      x.left ≫ (AbDual.inl A B).left := by
    rw [fst_ptV hv, ← Over.comp_left, pt0, AbDual.inl, comp_lift, Category.comp_id, MonObj.comp_one]
  have := GlobalTheory.TorusLift.preimage_eq_top_of_surjective (spOver (TrivSqZeroExt.fstHom R D D)).left
    (ptV v x).left (U := P.U i) (by
      rw [← Over.comp_left, e, Scheme.Hom.comp_preimage]
      exact top_unique hi)
  exact this.ge

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStandingTripleThetaFirstStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_standing_triple_theta_first : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X →
    ∀ (v : Bs.P) (w : Pl D.host.E), splitPrime (Bs.τ v) = w → ∀ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso (Bs.τ v) w jj → IsLocIso jj →
    ∀ cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w), (Γ.W.bas v).val.map jj * cc.val = basCols B e w →
    ∃ g : GL (Fin (spW₁ G i j).rank) (Kw w),
      IsMixChart v.1 (mixHalfS e (atPl w 1)) (mixHalfS e (cA D (atPl w 1))) (mixCoS B t e w)
        (fun u => chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
          (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u))
        (fun u => (xiAt w)⁻¹ • chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) (invT g) (invT cc)
          (coX (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u))
        (Assignment.one.block _ _) ∧
      ∀ u, chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
          (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u) = linB B t i j w (ptB e u) := by
  first | exact @GlobalTheory.TopFlip.ChartB.exists_mixChart_linB | exact GlobalTheory.TopFlip.ChartB.exists_mixChart_linB | (intros; apply GlobalTheory.TopFlip.ChartB.exists_mixChart_linB <;> assumption)
end

