module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthBallQuotientEqSumMulFdeg
section
open TensorProduct

namespace GlobalTheory.PointSupport


open TensorProduct in
open TensorProduct in
theorem _root_.GlobalTheory.PointSupport.exists_algHom_ker_eq (K : Type) [Field K] [IsAlgClosed K] (R : Type)
    [CommRing R] [Algebra K R] [Algebra.FiniteType K R] (M : Ideal R) [M.IsMaximal] :
    ∃ χ : R →ₐ[K] K, RingHom.ker χ = M := by
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite K (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ M)
  let e : K ≃ₐ[K] R ⧸ M :=
    AlgEquiv.ofBijective (Algebra.ofId K (R ⧸ M)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K M), ?_⟩
  ext x
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]


open TensorProduct in
open TensorProduct in
theorem _root_.GlobalTheory.PointSupport.finiteLength_and_finrank_eq_length :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (R : Type) [CommRing R] [Algebra K R]
      [Algebra.FiniteType K R] (χ₀ : R →ₐ[K] K) (O : Type) [CommRing O] [Algebra R O]
      [(RingHom.ker χ₀).IsPrime] [IsLocalization.AtPrime O (RingHom.ker χ₀)]
      (H : Type) [AddCommGroup H] [Module R H] [Module K H] [IsScalarTower K R H]
      [Module.Finite R H],
      (∀ χ : R →ₐ[K] K, χ ≠ χ₀ → ∃ r : R, χ r ≠ 0 ∧ ∀ z : H, r • z = 0) →
      IsFiniteLength O (O ⊗[R] H) ∧ Module.Finite K H ∧
        (Module.finrank K H : ℕ∞) = Module.length O (O ⊗[R] H) := by
  intro K _ _ R _ _ _ χ₀ O _ _ _ _ H _ _ _ _ _ hsupp
  classical
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hχ₀ : Function.Surjective χ₀ := fun k => ⟨algebraMap K R k, χ₀.commutes k⟩
  haveI hP : (RingHom.ker χ₀).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hχ₀

  have hmax : ∀ M : Ideal R, M.IsMaximal → Module.annihilator R H ≤ M → M = RingHom.ker χ₀ := by
    intro M hM hle
    obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.PointSupport.exists_algHom_ker_eq K R M
    by_cases h : χ = χ₀
    · rw [← hχ, h]
    · obtain ⟨r, hr, hrz⟩ := hsupp χ h
      have hrM : r ∈ M := hle (Module.mem_annihilator.mpr hrz)
      rw [← hχ] at hrM
      exact absurd (RingHom.mem_ker.mp hrM) hr

  have hprime : ∀ Q : Ideal R, Q.IsPrime → Module.annihilator R H ≤ Q → Q = RingHom.ker χ₀ := by
    intro Q hQ hle
    rw [← IsJacobsonRing.out' Q hQ.isRadical]
    apply le_antisymm
    · obtain ⟨J, hJ, hQJ⟩ := Ideal.exists_le_maximal Q hQ.ne_top
      rw [← hmax J hJ (hle.trans hQJ)]
      exact sInf_le ⟨hQJ, hJ⟩
    · exact le_sInf fun J hJ => (hmax J hJ.2 (hle.trans hJ.1)).ge

  letI : Module (R ⧸ Module.annihilator R H) H := Module.quotientAnnihilator
  have hmk : ∀ (r : R) (z : H), (Ideal.Quotient.mk (Module.annihilator R H) r) • z = r • z :=
    fun _ _ => rfl
  haveI : IsScalarTower R (R ⧸ Module.annihilator R H) H :=
    ⟨fun r a z => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, hmk, hmk, mul_smul]⟩
  haveI : IsScalarTower K (R ⧸ Module.annihilator R H) H :=
    ⟨fun k a z => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, hmk, hmk, ← Algebra.smul_def,
        smul_assoc]⟩
  haveI : Module.Finite (R ⧸ Module.annihilator R H) H :=
    Module.Finite.of_restrictScalars_finite R _ H
  have hprimeq : ∀ Q : Ideal (R ⧸ Module.annihilator R H), Q.IsPrime →
      Q.comap (Ideal.Quotient.mk _) = RingHom.ker χ₀ := fun Q hQ =>
    hprime _ (Ideal.comap_isPrime _ Q) fun r hr => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
      exact Q.zero_mem
  haveI : Ring.KrullDimLE 0 (R ⧸ Module.annihilator R H) := Ring.KrullDimLE.mk₀ fun Q hQ => by
    rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q, hprimeq Q hQ]
    refine Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective ?_
    rw [Ideal.mk_ker, ← hprimeq Q hQ]
    intro r hr
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    exact Q.zero_mem
  haveI : Module.Finite K (R ⧸ Module.annihilator R H) :=
    (Module.finite_iff_krullDimLE_zero K _).mpr inferInstance
  haveI hfin : Module.Finite K H := Module.Finite.trans (R ⧸ Module.annihilator R H) H

  have hunit : ∀ s : (RingHom.ker χ₀).primeCompl, IsUnit (algebraMap R (Module.End R H) s) := by
    intro s
    have ha : IsUnit (Ideal.Quotient.mk (Module.annihilator R H) (s : R)) := by
      by_contra h
      obtain ⟨I, hI, hsI⟩ := exists_max_ideal_of_mem_nonunits h
      have hsI' : (s : R) ∈ Ideal.comap (Ideal.Quotient.mk (Module.annihilator R H)) I := hsI
      rw [hprimeq I hI.isPrime] at hsI'
      exact s.2 hsI'
    rw [Module.End.isUnit_iff]
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    refine ⟨fun x y hxy => ?_, fun z => ⟨b • z, ?_⟩⟩
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← hmk, ← hmk] at hxy
      exact ha.smul_left_cancel.mp hxy
    · rw [Module.algebraMap_end_apply, ← hmk, smul_smul, hb, one_smul]
  haveI : IsLocalizedModule (RingHom.ker χ₀).primeCompl (LinearMap.id : H →ₗ[R] H) :=
    IsLocalizedModule.mk hunit (fun y => ⟨⟨y, 1⟩, one_smul _ _⟩)
      (fun {x₁ x₂} h => ⟨1, by simpa using h⟩)
  let e : H ≃ₗ[R] O ⊗[R] H := IsLocalizedModule.linearEquiv (RingHom.ker χ₀).primeCompl
    LinearMap.id (TensorProduct.mk R O H 1)

  letI : Algebra K O := ((algebraMap R O).comp (algebraMap K R)).toAlgebra
  haveI : IsScalarTower K R O := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let eK : H ≃ₗ[K] O ⊗[R] H := e.restrictScalars K
  haveI : IsLocalRing O := IsLocalization.AtPrime.isLocalRing O (RingHom.ker χ₀)
  haveI : IsLocalHom (algebraMap K O) := ⟨fun k hk => by
    by_cases h0 : k = 0
    · rw [h0, map_zero] at hk
      exact absurd hk not_isUnit_zero
    · exact isUnit_iff_ne_zero.mpr h0⟩
  haveI : Module.Finite K (O ⊗[R] H) := Module.Finite.equiv eK

  have hsurj : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)) := by
    have hR : ∀ r : R, IsLocalRing.residue O (algebraMap R O r) ∈
        (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)).fieldRange := by
      intro r
      refine ⟨IsLocalRing.residue K (χ₀ r), ?_⟩
      have hmem : algebraMap R O (r - algebraMap K R (χ₀ r)) ∈ IsLocalRing.maximalIdeal O := by
        rw [IsLocalization.AtPrime.to_map_mem_maximal_iff O (RingHom.ker χ₀), RingHom.mem_ker,
          map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, sub_eq_zero] at hmem
      rw [hmem]
      exact IsLocalRing.ResidueField.map_residue (algebraMap K O) (χ₀ r)
    intro x
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (RingHom.ker χ₀).primeCompl o
    rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul]
    have hs : IsLocalRing.residue O (IsLocalization.mk' O (1 : R) s) =
        (IsLocalRing.residue O (algebraMap R O s))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, IsLocalization.mk'_spec, map_one, map_one]
    rw [hs]
    exact Subfield.mul_mem _ (hR r) (Subfield.inv_mem _ (hR s))
  have hres : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O) = 1 := by
    let f := LinearEquiv.ofBijective
      (Algebra.linearMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O))
      ⟨(algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)).injective, hsurj⟩
    rw [← f.length_eq, Module.length_eq_one_iff]
    infer_instance
  have hlen := IsLocalRing.length_restrictScalars K O (O ⊗[R] H)
  rw [hres, mul_one, Module.length_eq_finrank K] at hlen
  have hfr : Module.finrank K H = Module.finrank K (O ⊗[R] H) := eK.finrank_eq
  refine ⟨?_, hfin, ?_⟩
  · rw [← Module.length_ne_top_iff, ← hlen]
    exact ENat.coe_ne_top _
  · rw [hfr]
    exact hlen

end GlobalTheory.PointSupport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemNonzeroLocusIffMemBasicOpenChart
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

theorem mem_nonzeroLocus_iff_mem_basicOpen_chart {Y : Scheme.{0}} {H : LB Y} (s : LB.Sec H) (k : H.ι)
    {x : Y} (hk : x ∈ H.U k) : x ∈ nonzeroLocus s ↔ x ∈ Y.basicOpen (s.f k) := by
  refine ⟨fun hx => ?_, fun hx => TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx⟩⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have e := congrArg Y.basicOpen (s.compat k l)
  rw [Scheme.basicOpen_mul, Y.basicOpen_of_isUnit (H.g k l).isUnit] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hx' : x ∈ H.U k ⊓ H.U l := ⟨hk, Y.basicOpen_le _ hl⟩
  exact (e.ge ⟨hx', hx', hl⟩).2

theorem mem_basicOpen_finset_prod_iff {Y : Scheme.{0}} {U : Y.Opens} {ι : Type} (f : ι → Γ(Y, U))
    (I : Finset ι) {x : Y} (hx : x ∈ U) :
    x ∈ Y.basicOpen (∏ i ∈ I, f i) ↔ ∀ i ∈ I, x ∈ Y.basicOpen (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using hx
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul, Finset.forall_mem_insert, ← ih]
    rfl

theorem mem_finset_biInf_opens_iff {Y : Scheme.{0}} {ι : Type} (D : ι → Y.Opens) (I : Finset ι)
    {x : Y} : x ∈ (⨅ i ∈ I, D i) ↔ ∀ i ∈ I, x ∈ D i := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iInf_insert, Finset.forall_mem_insert, ← ih]
    rfl

theorem exists_prod_sec_nonzeroLocus : ∀ (Y : Scheme.{0}) (H : LB Y) (ι : Type) (s : ι → LB.Sec H) (I : Finset ι), H.IsLB → ∃ σ : LB.Sec (pw H (I.card : ℤ)), (∀ l : H.ι, σ.f l = ∏ i ∈ I, (s i).f l) ∧ nonzeroLocus σ = ⨅ i ∈ I, nonzeroLocus (s i) := by
  intro Y H ι s I hH
  let σ : LB.Sec (pw H (I.card : ℤ)) :=
    { f := fun l : H.ι => ∏ i ∈ I, (s i).f l
      compat := fun k l : H.ι => by
        change (Y.presheaf.map (homOfLE (inf_le_left : H.U k ⊓ H.U l ≤ H.U k)).op).hom
            (∏ i ∈ I, (s i).f k) = ((H.g k l ^ (I.card : ℤ) : Γ(Y, H.U k ⊓ H.U l)ˣ) :
              Γ(Y, H.U k ⊓ H.U l)) *
          (Y.presheaf.map (homOfLE (inf_le_right : H.U k ⊓ H.U l ≤ H.U l)).op).hom
            (∏ i ∈ I, (s i).f l)
        rw [map_prod, map_prod, zpow_natCast, Units.val_pow_eq_pow_val, ← Finset.prod_const,
          ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => (s i).compat k l }
  refine ⟨σ, fun _ => rfl, TopologicalSpace.Opens.ext (Set.ext fun x => ?_)⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (show x ∈ (⊤ : Y.Opens) from trivial))
  refine (mem_nonzeroLocus_iff_mem_basicOpen_chart σ l hl).trans
    (((mem_basicOpen_finset_prod_iff (fun i => (s i).f l) I hl).trans ?_).trans
      (mem_finset_biInf_opens_iff (fun i => nonzeroLocus (s i)) I).symm)
  exact forall₂_congr fun i _ => (mem_nonzeroLocus_iff_mem_basicOpen_chart (s i) l hl).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SecCubeExactAtZeroAndOne
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem secCube_exactAt_zero_and_one (R : Type) [CommRing R] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ]
    (D : κ → Y.Opens) (hD : ⨆ i, D i = ⊤) :
    (cubeComplex (secCube f M D)).ExactAt 0 ∧ (cubeComplex (secCube f M D)).ExactAt 1 := by
  let O : κ → Y.Opens := fun a => ⨅ i ∈ ({a} : Finset κ), D i
  have hOD (a : κ) : O a = D a := by simp [O]
  have hO (a : κ) : O a ≤ ⨅ i ∈ (∅ : Finset κ), D i :=
    iInf_le_iInf_of_subset D (Finset.empty_subset _)
  have hc : (⨅ i ∈ (∅ : Finset κ), D i) ≤ ⨆ a, O a := by
    simp only [hOD, hD, le_top]
  constructor
  · rw [cubeComplex_exactAt_zero_iff]
    intro s t h
    exact SecOnR.ext_of_cover f O hO hc fun a => congrFun h ⟨{a}, Finset.card_singleton a⟩
  · rw [cubeComplex_exactAt_one_iff]
    intro x
    constructor
    · intro hx
      have key (a b : κ) (hab : a < b) {W : Y.Opens} (ha : W ≤ O a) (hb : W ≤ O b) :
          SecOnR.restrict f M ha (x ⟨{a}, Finset.card_singleton a⟩) =
            SecOnR.restrict f M hb (x ⟨{b}, Finset.card_singleton b⟩) := by
        have e := Cube.d_one_apply_pair (secCube f M D) x hab
        rw [hx] at e
        have e' := (sub_eq_zero.1 e.symm).symm
        have hW : W ≤ ⨅ i ∈ ({a, b} : Finset κ), D i := by
          rw [hOD] at ha hb
          rw [Finset.iInf_insert, Finset.iInf_singleton]
          exact le_inf ha hb
        have e'' := congrArg (SecOnR.restrict f M hW) e'
        exact (SecOnR.restrict_restrict f _ _ _).symm.trans
          (e''.trans (SecOnR.restrict_restrict f _ _ _))
      obtain ⟨t, ht, -⟩ := SecOnR.existsUnique_glue f O hO hc
        (fun a => x ⟨{a}, Finset.card_singleton a⟩) fun a b => by
          rcases lt_trichotomy a b with h | rfl | h
          · exact key a b h _ _
          · rfl
          · exact (key b a h _ _).symm
      refine ⟨t, funext ?_⟩
      rintro ⟨s, hs⟩
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hs
      exact ht a
    · rintro ⟨t, rfl⟩
      have := Cube.d_zero_apply (secCube f M D) ((Cube.termZeroEquiv _).symm t)
      rw [LinearEquiv.apply_symm_apply] at this
      rw [← this]
      exact Cube.d_d _ 0 _

end GlobalTheory.AbLaw
end

