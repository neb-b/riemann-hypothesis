module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.SchrodingerMatching.PsiPlaces
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityLevelFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0606
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.HWDefs
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.PfSWUS.SwFockk

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC NumberField IsDedekindDomain

def lstd (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) :
    AddSubgroup (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) where
  carrier := {y | ∀ i, y i ∈ intLoc F E v}
  add_mem' hx hy i := add_mem (hx i) (hy i)
  zero_mem' _ := zero_mem _
  neg_mem' hx i := neg_mem (hx i)

def HWFin : Prop :=
  ∀ (D : D7) (n : ℕ) (w : G D n), mat w = blk4 0 1 (-1) 0 → ∀ nb : hermA D n → G D n, PositivityTheory.PfSWUS.IsNMap nb →
  ∀ (b : hermA D n) (p k : G D n), p ∈ P D n → k ∈ K D n → w * nb b = p * k →
  ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 →
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (lam : Measure (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)),
    lam.IsAddHaarMeasure →
    PositivityTheory.SiegelWeilFormula.Gen.nu2 lam (lstd D.host.F D.host.E n v) (lstd D.host.F D.host.E n v) (PositivityTheory.SiegelWeilFormula.Gen.matV v b.1) =
      ((GlobalTheory.Doubling.absEv D.host.F D.host.E v (GlobalTheory.Doubling.unitFin D.host.F D.host.E v
        (Matrix.GeneralLinearGroup.det a)) : ℝ≥0) : ℝ)⁻¹

def HWInf : Prop :=
  ∀ (D : D7) (n : ℕ) (θ : InfFam D), IsInfFam θ → ∀ (w : G D n), mat w = blk4 0 1 (-1) 0 →
  ∀ nb : hermA D n → G D n, PositivityTheory.PfSWUS.IsNMap nb →
  ∀ (b : hermA D n) (p k : G D n), p ∈ P D n → k ∈ K D n → w * nb b = p * k →
  ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 →
    (((∏ w' : NumberField.InfinitePlace D.host.F, GlobalTheory.Doubling.absEw D.host.F D.host.E w'
        (GlobalTheory.Doubling.unitInf D.host.F D.host.E w' (Matrix.GeneralLinearGroup.det a)) : ℝ≥0) : ℝ)) *
      PositivityTheory.SiegelWeilFormula.Gen.nuInf θ (fun _ => 1) (PositivityTheory.SiegelWeilFormula.Gen.matInf b.1) = 1

def LstdStd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ),
    (∀ v, PositivityTheory.SiegelWeilFormula.Gen.IsCO (lstd F E n v)) ∧
    ∀ (d : ℕ) (bs : Module.Basis (Fin d) F E), ∀ᶠ v in Filter.cofinite,
      (lstd F E n v : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) = PositivityTheory.PfSWUS.Loc.latO bs v

end PositivityTheory.PfSWUS.SwFockk

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.IntAtEventually
section
noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory NumberField IsDedekindDomain
open scoped Matrix TensorProduct

namespace GlobalTheory.CompanionTheory.SwFinM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def compV (v : HeightOneSpectrum (𝓞 F)) :
    (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E) →ₐ[F] (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.map ((HeckeCharacterZeroLocus.SiegelWeilU.evalV F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA F)) (AlgHom.id F E)

theorem matV_eq (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (h : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    PositivityTheory.SiegelWeilFormula.Gen.matV v h = (compV v).mapMatrix h := rfl

theorem repr_map {A B : Type} [CommRing A] [Algebra F A] [CommRing B] [Algebra F B] (f : A →ₐ[F] B) {d : ℕ}
    (bs : Module.Basis (Fin d) F E) (x : A ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis B bs).repr (Algebra.TensorProduct.map f (AlgHom.id F E) x) k =
      f ((Algebra.TensorProduct.basis A bs).repr x k) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Algebra.TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]

theorem ev_int (y : HeckeCharacterZeroLocus.SiegelWeilU.AF F) :
    ∀ᶠ v in Filter.cofinite, HeckeCharacterZeroLocus.SiegelWeilU.evalV F v (HeckeCharacterZeroLocus.SiegelWeilU.sndA F y) ∈ v.adicCompletionIntegers F :=
  (HeckeCharacterZeroLocus.SiegelWeilU.sndA F y).2

theorem comp_mem_Rv {d : ℕ} (bs : Module.Basis (Fin d) F E) (x : HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E) :
    ∀ᶠ v in Filter.cofinite, compV v x ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v := by
  have h := Filter.eventually_all.2 fun k => ev_int (F := F) ((Algebra.TensorProduct.basis _ bs).repr x k)
  filter_upwards [h] with v hv k
  rw [compV, repr_map]
  exact hv k

theorem matV_mem_Rv {d : ℕ} (bs : Module.Basis (Fin d) F E) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) :
    ∀ᶠ v in Filter.cofinite, ∀ i j, PositivityTheory.SiegelWeilFormula.Gen.matV v X i j ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v :=
  Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => comp_mem_Rv bs (X i j)

theorem intAt_eventually {d : ℕ} (bs : Module.Basis (Fin d) F E) :
    ∀ᶠ v in Filter.cofinite, PositivityTheory.SiegelWeilFormula.Gunr.IntAt v (PositivityTheory.SiegelWeilFormula.Gunr.basisSet (AlgHom.id F E) bs) :=
  _root_.GlobalTheory.CompanionTheory.Gunr.finInt F _

section Lat

variable {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}

theorem mem_ringOf {σ : E →ₐ[F] E} (h : PositivityTheory.SiegelWeilFormula.Gunr.IntAt v (PositivityTheory.SiegelWeilFormula.Gunr.basisSet σ bs))
    (x : HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) : x ∈ GlobalTheory.CompanionTheory.RvRingPf.ringOf h ↔ x ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v := Iff.rfl

theorem mulVec_mem_latO {σ : E →ₐ[F] E} (h : PositivityTheory.SiegelWeilFormula.Gunr.IntAt v (PositivityTheory.SiegelWeilFormula.Gunr.basisSet σ bs)) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (hX : ∀ i j, X i j ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v)
    (y : Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E) (hy : y ∈ PositivityTheory.PfSWUS.Loc.latO bs v) :
    X *ᵥ y ∈ PositivityTheory.PfSWUS.Loc.latO bs v := by
  have hy' : ∀ j, y j ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v := (GlobalTheory.CompanionTheory.SiegLoc.NuIndex.mem_latO_iff bs v y).1 hy
  refine (GlobalTheory.CompanionTheory.SiegLoc.NuIndex.mem_latO_iff bs v _).2 fun i => ?_
  have e : (X *ᵥ y) i = ∑ j, X i j * y j := rfl
  rw [e]
  have hs : (∑ j, X i j * y j) ∈ GlobalTheory.CompanionTheory.RvRingPf.ringOf h :=
    Subring.sum_mem _ fun j _ => Subring.mul_mem _ ((mem_ringOf h _).2 (hX i j)) ((mem_ringOf h _).2 (hy' j))
  exact (mem_ringOf h _).1 hs

theorem image_latO {σ : E →ₐ[F] E} (h : PositivityTheory.SiegelWeilFormula.Gunr.IntAt v (PositivityTheory.SiegelWeilFormula.Gunr.basisSet σ bs)) {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v ⊗[F] E)) (hX : ∀ i j, X i j ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v)
    (hY : ∀ i j, Y i j ∈ PositivityTheory.SiegelWeilFormula.Gunr.Rv bs v) (hXY : X * Y = 1) :
    (fun y => X *ᵥ y) '' PositivityTheory.PfSWUS.Loc.latO bs v = PositivityTheory.PfSWUS.Loc.latO bs v := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mulVec_mem_latO h X hX y hy
  · intro hz
    refine ⟨Y *ᵥ z, mulVec_mem_latO h Y hY z hz, ?_⟩
    show X *ᵥ (Y *ᵥ z) = z
    rw [Matrix.mulVec_mulVec, hXY, Matrix.one_mulVec]

end Lat

end GlobalTheory.CompanionTheory.SwFinM

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.FockLatticeHeights.LatticeNormMatrixConj
section
noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped Matrix ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SwFinM

section Scale

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] {n : ℕ}

def mulVecHomeo (A Ai : Matrix (Fin n) (Fin n) R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) : (Fin n → R) ≃ₜ (Fin n → R) where
  toFun x := A *ᵥ x
  invFun x := Ai *ᵥ x
  left_inv x := by simp [Matrix.mulVec_mulVec, h2]
  right_inv x := by simp [Matrix.mulVec_mulVec, h1]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

def mulVecCAE (A Ai : Matrix (Fin n) (Fin n) R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) : (Fin n → R) ≃ₜ+ (Fin n → R) :=
  { (mulVecHomeo A Ai h1 h2).toEquiv with
    map_add' := fun x y => Matrix.mulVec_add A x y
    continuous_toFun := (mulVecHomeo A Ai h1 h2).continuous
    continuous_invFun := (mulVecHomeo A Ai h1 h2).symm.continuous }

theorem image_eq_preimage (A Ai : Matrix (Fin n) (Fin n) R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) (S : Set (Fin n → R)) :
    (fun x => A *ᵥ x) '' S = (fun x => Ai *ᵥ x) ⁻¹' S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show Ai *ᵥ (A *ᵥ y) ∈ S
    rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  · intro hx
    refine ⟨Ai *ᵥ x, hx, ?_⟩
    show A *ᵥ (Ai *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem exists_scale (lam : Measure (Fin n → R)) [lam.IsAddHaarMeasure] (A Ai : Matrix (Fin n) (Fin n) R)
    (h1 : A * Ai = 1) (h2 : Ai * A = 1) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ S : Set (Fin n → R), lam ((fun x => A *ᵥ x) '' S) = c * lam S := by
  let e : (Fin n → R) ≃ₜ+ (Fin n → R) := mulVecCAE Ai A h2 h1
  have hcoc : Filter.Tendsto (e : (Fin n → R) → (Fin n → R)) (Filter.cocompact _) (Filter.cocompact _) :=
    (mulVecHomeo Ai A h2 h1).isClosedEmbedding.tendsto_cocompact
  have : (lam.map e).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map lam (e : (Fin n → R) →+ (Fin n → R)) e.continuous e.surjective hcoc
  have hsm := Measure.isAddLeftInvariant_eq_smul (lam.map e) lam
  set c : ℝ≥0 := (lam.map e).addHaarScalarFactor lam
  have hmap : ∀ S : Set (Fin n → R), (lam.map e) S = lam ((fun x => Ai *ᵥ x) ⁻¹' S) := fun S =>
    MeasurableEquiv.map_apply (mulVecHomeo Ai A h2 h1).toMeasurableEquiv S
  have key : ∀ S : Set (Fin n → R), lam ((fun x => A *ᵥ x) '' S) = (c : ℝ≥0∞) * lam S := by
    intro S
    rw [image_eq_preimage A Ai h1 h2, ← hmap, hsm]
    rfl
  refine ⟨c, ?_, ENNReal.coe_ne_top, key⟩
  intro h0
  have hu := key Set.univ
  rw [h0, zero_mul, Set.image_univ_of_surjective (f := fun x => A *ᵥ x) (mulVecHomeo A Ai h1 h2).surjective] at hu
  exact isOpen_univ.measure_ne_zero lam Set.univ_nonempty hu

end Scale

section Index

variable {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
  [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] {n : ℕ}

theorem lattice_norm_matrix_conj (lam : Measure (Fin n → R)) [lam.IsAddHaarMeasure] (L : AddSubgroup (Fin n → R))
    (A Ai A' C B : Matrix (Fin n) (Fin n) R) (h1 : A * Ai = 1) (h2 : Ai * A = 1) (hAC : A' * C = 1) :
    PositivityTheory.SiegelWeilFormula.Gen.nu2 lam (L.map (Matrix.mulVecLin A).toAddMonoidHom) (L.map (Matrix.mulVecLin C).toAddMonoidHom)
      (A * B * A') = PositivityTheory.SiegelWeilFormula.Gen.nu2 lam L L B := by
  obtain ⟨c, hc0, hct, hc⟩ := exists_scale lam A Ai h1 h2
  have hS : {x | ∃ y ∈ L.map (Matrix.mulVecLin A).toAddMonoidHom, ∃ y' ∈ L.map (Matrix.mulVecLin C).toAddMonoidHom,
      x = y + (A * B * A').mulVec y'} = (fun x => A *ᵥ x) '' {x | ∃ y ∈ L, ∃ y' ∈ L, x = y + B.mulVec y'} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_image, AddSubgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, _, ⟨u', hu', rfl⟩, rfl⟩
      refine ⟨u + B *ᵥ u', ⟨u, hu, u', hu', rfl⟩, ?_⟩
      simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, Matrix.mulVec_add, Matrix.mulVec_mulVec]
      rw [Matrix.mul_assoc A B A', Matrix.mul_assoc A (B * A') C, Matrix.mul_assoc B A' C, hAC, Matrix.mul_one]
    · rintro ⟨_, ⟨u, hu, u', hu', rfl⟩, rfl⟩
      refine ⟨A *ᵥ u, ⟨u, hu, rfl⟩, C *ᵥ u', ⟨u', hu', rfl⟩, ?_⟩
      simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec]
      rw [Matrix.mul_assoc A B A', Matrix.mul_assoc A (B * A') C, Matrix.mul_assoc B A' C, hAC, Matrix.mul_one]
  have hL : ((L.map (Matrix.mulVecLin A).toAddMonoidHom : AddSubgroup (Fin n → R)) : Set (Fin n → R)) =
      (fun x => A *ᵥ x) '' (L : Set (Fin n → R)) := by
    rw [AddSubgroup.coe_map]
    rfl
  unfold PositivityTheory.SiegelWeilFormula.Gen.nu2
  rw [hS, hL, hc, hc, ENNReal.mul_div_mul_left _ _ hc0 hct]

end Index

end GlobalTheory.CompanionTheory.SwFinM

end
end

