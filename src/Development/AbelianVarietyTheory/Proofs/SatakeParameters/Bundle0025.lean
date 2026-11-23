module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0023
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStrictHenselisationOfDirectedUnion
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodSemilinear
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FiniteResidueFieldPadicInt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagonalComplementSecondProjectionIsFiniteEtaleStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonalComplementSecondProjection_isFinite_etale : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f], IsFinite (GlobalTheory.EtC.Tr.diagComplHom f) ∧ Etale (GlobalTheory.EtC.Tr.diagComplHom f) := by
  first | (exact @GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale) | (exact GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale) | (intros; apply GlobalTheory.EtC.Tr.diagComplHom_isFinite_etale  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFibreFieldPointsCardLEOfIsFiniteIsAffineStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibreFieldPointsCardLE_of_isFinite_isAffine : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [IsAffine X], ∃ n, GlobalTheory.EtC.Tr.FibrePointsLE f n := by
  first | (exact @GlobalTheory.EtC.Tr.finite_fibrePointsLE_of_isAffine) | (exact GlobalTheory.EtC.Tr.finite_fibrePointsLE_of_isAffine) | (intros; apply GlobalTheory.EtC.Tr.finite_fibrePointsLE_of_isAffine  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibreFieldPointsCardLEDiagonalComplementSecondPrStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreFieldPointsCardLE_diagonalComplementSecondProjection : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (n : ℕ), GlobalTheory.EtC.Tr.FibrePointsLE f (n + 1) → GlobalTheory.EtC.Tr.FibrePointsLE (GlobalTheory.EtC.Tr.diagComplHom f) n := by
  first | (exact @GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom) | (exact GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom) | (intros; apply GlobalTheory.EtC.Tr.fibrePointsLE_diagComplHom  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormsBaseChange
section
set_option autoImplicit false
noncomputable section
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1.Base

variable (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]

theorem mapDR_ιMulti (n : ℕ) (v : Fin n → Ω[K⁄k]) :
    mapDR k K L (ExteriorAlgebra.ιMulti K n v) =
      ExteriorAlgebra.ιMulti L n (fun i => KaehlerDifferential.map k k K L (v i)) := by
  rw [ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  exact congrArg (fun l => List.prod l) (congrArg List.ofFn (funext fun i => by
    show mapDR k K L (ExteriorAlgebra.ι K (v i)) = _
    rw [mapDR, ExteriorAlgebra.lift_ι_apply]; rfl))


variable {k K L} in
theorem mapDR_basis {I : Type} [LinearOrder I] (bK : Module.Basis I K Ω[K⁄k]) (bL : Module.Basis I L Ω[L⁄k])
    (h : ∀ i, bL i = KaehlerDifferential.map k k K L (bK i)) (s : Finset I) :
    mapDR k K L (bK.ExteriorAlgebra s) = bL.ExteriorAlgebra s := by
  rw [ExteriorAlgebra.basis_apply_ofCard _ rfl, ExteriorAlgebra.basis_apply_ofCard _ rfl,
    ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_family, mapDR_ιMulti]
  exact congrArg _ (funext fun i => (h _).symm)


variable {k K L} in
theorem repr_mapDR {I : Type} [LinearOrder I] (bK : Module.Basis I K Ω[K⁄k]) (bL : Module.Basis I L Ω[L⁄k])
    (h : ∀ i, bL i = KaehlerDifferential.map k k K L (bK i)) (ω : DR k K) (s : Finset I) :
    bL.ExteriorAlgebra.repr (mapDR k K L ω) s = algebraMap K L (bK.ExteriorAlgebra.repr ω s) := by
  have : ((bL.ExteriorAlgebra.coord s).restrictScalars K ∘ₗ (mapDR k K L).toLinearMap) =
      Algebra.linearMap K L ∘ₗ bK.ExteriorAlgebra.coord s := by
    refine bK.ExteriorAlgebra.ext fun t => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, mapDR_basis bK bL h,
      LinearMap.coe_restrictScalars, Module.Basis.coord_apply, Module.Basis.repr_self, Algebra.linearMap_apply]
    by_cases hts : t = s
    · subst hts; simp
    · simp [Finsupp.single_apply, hts]
  exact congrArg (· ω) this

end GlobalTheory.W1.Base

namespace GlobalTheory.W1.Base

theorem forms_baseChange : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L],
    (∀ y : DR k L, ∃ (m : ℕ) (b : Fin m → L) (ω : Fin m → DR k K), y = ∑ j, b j • mapDR k K L (ω j)) ∧
      ∀ (m : ℕ) (b : Fin m → L) (ω : Fin m → DR k K), LinearIndependent K b →
        ∑ j, b j • mapDR k K L (ω j) = 0 → ∀ j, ω j = 0 := by
  intro k K L _ _ _ _ _ _ _ _ _
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  haveI : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  let I := Module.Basis.ofVectorSpaceIndex K Ω[K⁄k]
  letI : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let bK : Module.Basis I K Ω[K⁄k] := Module.Basis.ofVectorSpace K Ω[K⁄k]
  let bL : Module.Basis I L Ω[L⁄k] := (bK.baseChange L).map (tensorKaehlerEquivOfFormallyEtale k K L)
  have h : ∀ i, bL i = KaehlerDifferential.map k k K L (bK i) := fun i => by
    simp only [bL, Module.Basis.map_apply, Module.Basis.baseChange_apply, tensorKaehlerEquivOfFormallyEtale_apply,
      mapBaseChange_tmul, one_smul]
  set BK := bK.ExteriorAlgebra
  set BL := bL.ExteriorAlgebra
  refine ⟨fun y => ?_, fun m b ω hb hsum j => ?_⟩
  · set S := (BL.repr y).support
    refine ⟨S.card, fun j => BL.repr y (S.equivFin.symm j), fun j => BK (S.equivFin.symm j), ?_⟩
    simp only [BK, BL, mapDR_basis bK bL h]
    conv_lhs => rw [← BL.linearCombination_repr y, Finsupp.linearCombination_apply, Finsupp.sum, ← Finset.sum_coe_sort]
    exact (Fintype.sum_equiv S.equivFin _ _ fun _ => by rw [Equiv.symm_apply_apply])
  · have hc : ∀ s, ∀ j, BK.repr (ω j) s = 0 := by
      intro s
      have h0 := congrArg (fun z => BL.repr z s) hsum
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finset.sum_apply', Finsupp.smul_apply, smul_eq_mul,
        map_zero, Finsupp.zero_apply, BK, BL, repr_mapDR bK bL h] at h0
      refine Fintype.linearIndependent_iff.1 hb (fun j => BK.repr (ω j) s) ?_
      simpa [Algebra.smul_def, mul_comm] using h0
    exact BK.repr.injective (Finsupp.ext fun s => by simpa using hc s j)

end GlobalTheory.W1.Base
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FreeSheafSumSectionsEqOfTwoSplittingsStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeSheaf_sum_sections_eq_of_two_splittings : ∀ (R : Type) [CommRing R] {Z X V : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m m' : ℕ} {s : Fin m → (V ⟶ Z)} {s' : Fin m' → (V ⟶ Z)}, GlobalTheory.EtC.Tr.SplitBy f y s → GlobalTheory.EtC.Tr.SplitBy f y s' → ∑ j, (GlobalTheory.EtC.free R).map (yoneda.map (s j)) = ∑ j, (GlobalTheory.EtC.free R).map (yoneda.map (s' j)) := by
  first | (exact @GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings) | (exact GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings) | (intros; apply GlobalTheory.EtC.Tr.sum_sections_eq_of_two_splittings  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IndEtaleComp
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ind_etale_comp : ∀ (X Y Z : Type) [CommRing X] [CommRing Y] [CommRing Z] (f : X →+* Y) (g : Y →+* Z), GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale f → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale g → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp f) := by
  first | (exact @GlobalTheory.IndEtaleComp.isIndEtale_comp) | (exact GlobalTheory.IndEtaleComp.isIndEtale_comp) | (intros; apply GlobalTheory.IndEtaleComp.isIndEtale_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsArtinianRingFibQuot
section
open GlobalTheory.PD

namespace GlobalTheory

theorem finite_quotient_of_integral {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    [Algebra.FiniteType k S] (f : R →ₐ[k] S) (hi : (f : R →+* S).IsIntegral) (I : Ideal S)
    (hc : ∀ r, ∃ c : k, f r - algebraMap k S c ∈ I) : Module.Finite k (S ⧸ I) := by
  classical
  letI : Algebra R S := (f : R →+* S).toAlgebra
  haveI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq (fun c => (f.commutes c).symm)
  haveI : Algebra.FiniteType R S := Algebra.FiniteType.of_restrictScalars_finiteType k R S
  haveI : Algebra.IsIntegral R S := ⟨hi⟩
  haveI : Module.Finite R S := Algebra.IsIntegral.finite
  obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := R) (M := S)
  refine ⟨⟨G.image (Ideal.Quotient.mk I), ?_⟩⟩
  rw [eq_top_iff]
  rintro q -
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hs : s ∈ Submodule.span R (G : Set S) := hG ▸ Submodule.mem_top
  induction hs using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span (by simp only [Finset.coe_image]; exact ⟨y, hy, rfl⟩)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul r a _ ha =>
    obtain ⟨c, hc⟩ := hc r
    have e : Ideal.Quotient.mk I (r • a) = c • Ideal.Quotient.mk I a := by
      rw [Algebra.smul_def, map_mul, Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap]
      congr 1
      exact Ideal.Quotient.eq.2 hc
    rw [e]
    exact Submodule.smul_mem _ _ ha

end GlobalTheory

namespace GlobalTheory.PD

theorem isArtinianRing_fib_quot : ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (F : Type) [Field F] [Algebra k F] [Algebra F K]
    [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    IsArtinianRing (rB k K x {0} ⧸ Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0}))) := by
  intro k K _ _ _ F _ _ _ _ d x h
  haveI := h.smooth 0
  set I := Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem k K x j⟩ : rB k K x {0})) with hI
  let f : rA k x {0} →ₐ[k] rB k K x {0} :=
    ((IsScalarTower.toAlgHom k F K).comp (rA k x {0}).val).codRestrict (rB k K x {0})
      (fun a => (integralClosure (rA k x {0}) K).algebraMap_mem a)
  have hi : (f : rA k x {0} →+* rB k K x {0}).IsIntegral := by
    intro s
    obtain ⟨p, hm, hp⟩ := s.2
    refine ⟨p, hm, Subtype.val_injective ?_⟩
    have e := Polynomial.hom_eval₂ p (f : rA k x {0} →+* rB k K x {0}) (rB k K x {0}).val.toRingHom s
    refine e.trans ?_
    exact hp
  have hc : ∀ r, ∃ c : k, f r - algebraMap k _ c ∈ I := by
    rintro ⟨r, hr⟩
    induction hr using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨i, hi0, j, rfl⟩ := hy
      rw [Finset.mem_singleton] at hi0
      subst hi0
      cases j using Fin.cases with
      | zero =>
        refine ⟨1, ?_⟩
        convert I.zero_mem using 1
        rw [map_one, sub_eq_zero]
        refine Subtype.ext ?_
        show algebraMap F K (x 0 / x 0) = 1
        rw [div_self (h.pd.ne 0), map_one]
      | succ j =>
        refine ⟨0, ?_⟩
        rw [map_zero, sub_zero]
        exact Ideal.subset_span ⟨j, rfl⟩
    | algebraMap r =>
      refine ⟨r, ?_⟩
      have : f ⟨algebraMap k F r, _⟩ = algebraMap k _ r := f.commutes r
      rw [this, sub_self]
      exact I.zero_mem
    | add a b ha hb iha ihb =>
      obtain ⟨c₁, h₁⟩ := iha
      obtain ⟨c₂, h₂⟩ := ihb
      refine ⟨c₁ + c₂, ?_⟩
      have : f ⟨a + b, add_mem ha hb⟩ = f ⟨a, ha⟩ + f ⟨b, hb⟩ := map_add f ⟨a, ha⟩ ⟨b, hb⟩
      rw [this, map_add (f := _)]
      convert add_mem h₁ h₂ using 1
      ring
    | mul a b ha hb iha ihb =>
      obtain ⟨c₁, h₁⟩ := iha
      obtain ⟨c₂, h₂⟩ := ihb
      refine ⟨c₁ * c₂, ?_⟩
      have : f ⟨a * b, mul_mem ha hb⟩ = f ⟨a, ha⟩ * f ⟨b, hb⟩ := map_mul f ⟨a, ha⟩ ⟨b, hb⟩
      rw [this, map_mul]
      convert add_mem (I.mul_mem_right (f ⟨b, hb⟩) h₁) (I.mul_mem_left (algebraMap k _ c₁) h₂) using 1
      ring
  haveI := GlobalTheory.finite_quotient_of_integral f hi I hc
  exact IsArtinianRing.of_finite k _

end GlobalTheory.PD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsEmptyOfFibreFieldPointsCardLEZeroStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEmpty_of_fibreFieldPointsCardLE_zero : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X), GlobalTheory.EtC.Tr.FibrePointsLE f 0 → IsEmpty Z := by
  first | (exact @GlobalTheory.EtC.Tr.isEmpty_of_fibrePointsLE_zero) | (exact GlobalTheory.EtC.Tr.isEmpty_of_fibrePointsLE_zero) | (intros; apply GlobalTheory.EtC.Tr.isEmpty_of_fibrePointsLE_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemEtaleTopologyOfPullbackFiniteEtaleStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_etaleTopology_of_pullback_finite_etale : ∀ {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (T : Sieve X), T.pullback f ∈ Scheme.etaleTopology Z → (∀ {V : Scheme.{0}} (v : V ⟶ X), IsEmpty (pullback f v : Scheme.{0}) → T v) → T ∈ Scheme.etaleTopology X := by
  first | (exact @GlobalTheory.EtC.Tr.mem_etaleTopology_of_pullback_finite) | (exact GlobalTheory.EtC.Tr.mem_etaleTopology_of_pullback_finite) | (intros; apply GlobalTheory.EtC.Tr.mem_etaleTopology_of_pullback_finite  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RedCompatOfFiniteEtale
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC.Tr

open GlobalTheory.EtC.CupSpec

section CyclicComplexMaps

variable {R : Type} [CommRing R]

theorem chainMap_f {X Z : Scheme.{0}} (t : freeSch R X ⟶ freeSch R Z) (p : ℕ) :
    (chainsXIso R (sch.obj X) p).inv ≫ (chainMap R t).f (-(p : ℤ)) = t ≫ (chainsXIso R (sch.obj Z) p).inv := by
  have h1 : (chainMap R t).f (-(p : ℤ)) =
      (chainsXIso R (sch.obj X) p).hom ≫ ((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).map (simpMap R t)).f p ≫
        (chainsXIso R (sch.obj Z) p).inv :=
    HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat (i := p) rfl
  rw [h1, Iso.inv_hom_id_assoc]
  rfl

theorem ev_chainMap {X Z : Scheme.{0}} (t : freeSch R X ⟶ freeSch R Z) {I : Cx R} {n : ℤ}
    (α : Cochain ((chains R).obj (sch.obj Z)) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
    (y : Sx (sch.obj X) p U) :
    ev ((Cochain.ofHom (chainMap R t)).comp α (zero_add n)) p s h U y =
      Sec.map ((chainsXIso R (sch.obj Z) p).inv ≫ α.v _ _ h) (Sec.map t (freeGen R (yoneda.obj X) U y)) := by
  rw [ev_def, Cochain.zero_cochain_comp_v, Cochain.ofHom_v, ← Category.assoc, chainMap_f]
  rfl

end CyclicComplexMaps

section Key

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

theorem secMap_sum {F G : Shv R} {ι : Type*} (s : Finset ι) (g : ι → (F ⟶ G)) {U : Scheme.{0}} (a : Sec F U) :
    Sec.map (∑ j ∈ s, g j) a = ∑ j ∈ s, Sec.map (g j) a :=
  map_sum (mapHom F G a) g s

theorem exists_free_restr (P : PSh) : ∃ ι : (free R).obj P ⟶ (restr φ).obj ((free S).obj P),
    ∀ U x, Sec.map ι (freeGen R P U x) = (show Sec ((restr φ).obj ((free S).obj P)) U from freeGen S P U x) :=
  free_exists P _ (fun U x => show Sec ((restr φ).obj ((free S).obj P)) U from freeGen S P U x)
    (fun V U g x => freeGen_res P g x)

theorem isTransfer_reduce {Z X : Scheme.{0}} {f : Z ⟶ X} {t : freeSch R X ⟶ freeSch R Z} (ht : IsTransfer R f t)
    (ι : freeSch R Z ⟶ (restr φ).obj (freeSch S Z))
    (hι : ∀ U x, Sec.map ι (freeGen R (yoneda.obj Z) U x) =
      (show Sec ((restr φ).obj (freeSch S Z)) U from freeGen S (yoneda.obj Z) U x))
    (t' : freeSch S X ⟶ freeSch S Z)
    (ht' : ∀ U x, Sec.map t' (freeGen S (yoneda.obj X) U x) =
      (show Sec (freeSch S Z) U from Sec.map ι (Sec.map t (freeGen R (yoneda.obj X) U x)))) :
    IsTransfer S f t' := by
  intro T x m s hs hiso
  apply free_ext
  intro V w
  have e := congrArg (fun g => Sec.map ι (Sec.map g (freeGen R (yoneda.obj T) V w))) (ht T x m s hs hiso)
  change Sec.map ι (Sec.map t (Sec.map ((free R).map (yoneda.map x)) (freeGen R (yoneda.obj T) V w))) =
    Sec.map ι (Sec.map (∑ j, (free R).map (yoneda.map (s j))) (freeGen R (yoneda.obj T) V w)) at e
  change Sec.map t' (Sec.map ((free S).map (yoneda.map x)) (freeGen S (yoneda.obj T) V w)) =
    Sec.map (∑ j, (free S).map (yoneda.map (s j))) (freeGen S (yoneda.obj T) V w)
  rw [freeGen_map, ht']
  rw [freeGen_map] at e
  refine e.trans ?_
  rw [secMap_sum, secMap_sum]
  refine (map_sum (ι.hom.app (op V)).hom _ Finset.univ).trans (Finset.sum_congr rfl fun j _ => ?_)
  change Sec.map ι (Sec.map ((free R).map (yoneda.map (s j))) (freeGen R (yoneda.obj T) V w)) = _
  rw [freeGen_map, freeGen_map, hι]

theorem key_free {Z X : Scheme.{0}} {f : Z ⟶ X} {I : Shv R} {J : Shv S} (A : freeSch R Z ⟶ I) (B : freeSch S Z ⟶ J)
    (ρ' : I ⟶ (restr φ).obj J)
    (hAB : ∀ V z, Sec.map B (freeGen S (yoneda.obj Z) V z) = Sec.map ρ' (Sec.map A (freeGen R (yoneda.obj Z) V z)))
    {tR : freeSch R X ⟶ freeSch R Z} (htR : IsTransfer R f tR) {tS : freeSch S X ⟶ freeSch S Z}
    (huniq : ∀ t, IsTransfer S f t → t = tS) (U : Scheme.{0}) (y : U ⟶ X) :
    Sec.map B (Sec.map tS (freeGen S (yoneda.obj X) U y)) =
      Sec.map ρ' (Sec.map A (Sec.map tR (freeGen R (yoneda.obj X) U y))) := by
  obtain ⟨ι, hι⟩ := exists_free_restr φ (yoneda.obj Z)
  obtain ⟨t', ht'⟩ := free_exists (R := S) (yoneda.obj X) (freeSch S Z)
    (fun U y => show Sec (freeSch S Z) U from Sec.map ι (Sec.map tR (freeGen R (yoneda.obj X) U y)))
    (fun V U g y => by
      refine (map_res ι g _).trans ?_
      change Sec.map ι (Sec.res g (Sec.map tR (freeGen R (yoneda.obj X) U y))) = _
      rw [map_res, freeGen_res])
  have hT := huniq t' (isTransfer_reduce φ htR ι hι t' ht')
  subst hT
  rw [ht']
  have hm : ι ≫ (restr φ).map B = A ≫ ρ' := free_ext _ _ (fun V z => by
    change Sec.map B (Sec.map ι (freeGen R (yoneda.obj Z) V z)) = Sec.map ρ' (Sec.map A (freeGen R (yoneda.obj Z) V z))
    rw [hι]
    exact hAB V z)
  exact congrArg (fun g => Sec.map g (Sec.map tR (freeGen R (yoneda.obj X) U y))) hm

end Key

theorem redCompat_of_finite_etale (l : ℕ) [Fact l.Prime] {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f]
    (hex : ∀ (R : Type) [CommRing R], ∃! t, IsTransfer R f t) (n i : ℤ) : RedCompat l f n i := by
  intro k x
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl⟩
  have hd : l ^ k ∣ l ^ (k + 1) := pow_dvd_pow l (Nat.le_succ k)
  obtain ⟨t0, ht0, -⟩ := hex (ZMod (l ^ (k + 1)))
  have htQ := transfer_spec (ZMod (l ^ (k + 1))) ⟨t0, ht0⟩
  obtain ⟨t1, ht1, hu1⟩ := hex (ZMod (l ^ k))
  have huniq : ∀ t, IsTransfer (ZMod (l ^ k)) f t → t = transfer (ZMod (l ^ k)) f := fun t ht =>
    (hu1 t ht).trans (hu1 _ (transfer_spec _ ⟨t1, ht1⟩)).symm
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨β, hβ⟩ := (redMap (l ^ (k + 1)) (l ^ k) i).image_exists (sch.obj Z) n α
  have h1 : red (l ^ (k + 1)) (l ^ k) (sch.obj Z) n i (CohomologyClass.mk α) = CohomologyClass.mk β :=
    (redMap (l ^ (k + 1)) (l ^ k) i).op_spec _ n α β hβ
  rw [h1]
  have key := (redMap (l ^ (k + 1)) (l ^ k) i).op_spec (sch.obj X) n
    (zcomp (Cocycle.ofHom (chainMap _ (transfer _ f))) α (zero_add n))
    (zcomp (Cocycle.ofHom (chainMap _ (transfer _ f))) β (zero_add n)) (by
      intro p s h U y
      change ev ((Cochain.ofHom (chainMap _ (transfer _ f))).comp β.1 (zero_add n)) p s h U y =
        (redMap (l ^ (k + 1)) (l ^ k) i).app U s
          (ev ((Cochain.ofHom (chainMap _ (transfer _ f))).comp α.1 (zero_add n)) p s h U y)
      rw [ev_chainMap, ev_chainMap]
      exact key_free (ZMod.castHom hd (ZMod (l ^ k))) _ _
        (ScalarExt.semiHom (redMap (l ^ (k + 1)) (l ^ k) i) (ScalarExt.zmod_semilinear hd _) s)
        (fun V z => (ev_def β.1 p s h V z).symm.trans ((hβ p s h V z).trans (congrArg _ (ev_def α.1 p s h V z))))
        htQ huniq U y)
  exact key

end GlobalTheory.EtC.Tr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeBoundOfIsometricSphericalGL
section
open GlobalTheory.LatHecke

namespace GlobalTheory.LatHecke

theorem satake_bound_of_isometric_spherical : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ρ : Representation ℂ (GL (Fin r) K) V) (v : V) (α : Multiset ℂ), α.card = r → (∀ g x, ‖ρ g x‖ = ‖x‖) → v ≠ 0 → (∀ g, glMap g (std O K r).1 = (std O K r).1 → ρ g v = v) → (∀ k ≤ r, ∀ s : Finset (GL (Fin r) K), Set.BijOn (fun g => glMap g (std O K r).1) s (Subtype.val '' subElem k (std O K r)) → ∑ g ∈ s, ρ g v = ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • v) → ∀ a ∈ α, ‖a‖ ≤ (qRes O : ℝ) ^ (((r : ℝ) - 1) / 2) := by
  intro O K _ _ _ _ _ _ _ r V _ _ ρ v α hcard hnorm hv hinv heig
  classical
  have hmul : ∀ (a b : GL (Fin r) K) (x : V), ρ (a * b) x = ρ a (ρ b x) := fun a b x => by
    rw [map_mul]; rfl
  have hone : ∀ x : V, ρ 1 x = x := fun x => by
    rw [map_one]; rfl
  choose γ hγ using (_root_.GlobalTheory.LatHecke.gl_transitive_lattices O K r).1
  have hγ' : ∀ L : Lat O K r, γ L • std O K r = L := fun L => Subtype.ext (hγ L)
  let φ : Lat O K r → V := fun L => ρ (γ L) v

  have hφ : ∀ g : GL (Fin r) K, φ (g • std O K r) = ρ g v := by
    intro g
    have hfix : ((γ (g • std O K r))⁻¹ * g) • std O K r = std O K r := by
      rw [mul_smul, inv_smul_eq_iff, hγ']
    have h1 : ρ ((γ (g • std O K r))⁻¹ * g) v = v :=
      hinv _ (congrArg Subtype.val hfix)
    have h2 : ρ g v = ρ (γ (g • std O K r) * ((γ (g • std O K r))⁻¹ * g)) v := by
      rw [mul_inv_cancel_left]
    change ρ (γ (g • std O K r)) v = ρ g v
    rw [h2, hmul, h1]
  have hφg : ∀ (g : GL (Fin r) K) (M : Lat O K r), φ (g • M) = ρ g (φ M) := by
    intro g M
    have h1 : g • M = (g * γ M) • std O K r := by rw [mul_smul, hγ']
    rw [h1, hφ, hmul]
  have hstd : φ (std O K r) = v := by
    have := hφ 1
    rwa [one_smul, hone] at this
  refine _root_.GlobalTheory.SatakeBound.main O K r V φ α ‖v‖ hcard ?_ ?_ ?_
  · intro h
    exact hv (by rw [← hstd, h]; rfl)
  · intro L
    exact (hnorm _ _).le
  · intro k hk L

    have h0 : heckeElem k φ (std O K r)
        = ((((qRes O : ℝ) ^ ((k : ℝ) * ((r : ℝ) - k) / 2) : ℝ) : ℂ) * α.esymm k) • v := by
      rw [heckeElem_eq_sum, ← heig k hk ((subElem_finite k (std O K r)).toFinset.image γ)]
      · rw [Finset.sum_image]
        intro M _ M' _ h
        rw [← hγ' M, ← hγ' M', h]
      · refine ⟨?_, ?_, ?_⟩
        · intro g hg
          obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hg)
          exact ⟨M, (Set.Finite.mem_toFinset _).1 hM, (hγ M).symm⟩
        · intro g hg g' hg' h
          obtain ⟨M, hM, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hg)
          obtain ⟨M', hM', rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hg')
          have h' : M = M' := Subtype.ext (by simpa only [hγ] using h)
          rw [h']
        · rintro _ ⟨M, hM, rfl⟩
          exact ⟨γ M, Finset.mem_coe.2 (Finset.mem_image.2
            ⟨M, (Set.Finite.mem_toFinset _).2 hM, rfl⟩), hγ M⟩

    have h1 : heckeElem k φ L = ρ (γ L) (heckeElem k φ (std O K r)) := by
      conv_lhs => rw [← hγ' L]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [heckeElem_smul, heckeElem_eq_sum, heckeElem_eq_sum, map_sum]
      exact Finset.sum_congr rfl fun M _ => hφg _ _
    rw [h1, h0, map_smul]
end GlobalTheory.LatHecke
end

