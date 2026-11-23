module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0010
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0011
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NullSingOfIdemEx

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.BlockMatrixMulUpperUnipotent
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LGenK

open Matrix

variable {R : Type} [CommRing R] {n : ℕ}

private theorem blk4_mul_blk4 (A B C E A' B' C' E' : Matrix (Fin n) (Fin n) R) :
    blk4 A B C E * blk4 A' B' C' E' =
      blk4 (A * A' + B * C') (A * B' + B * E') (C * A' + E * C') (C * B' + E * E') := by
  simp only [blk4, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

private theorem cj_one' (s : R →+* R) : cj s (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  unfold cj
  rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

theorem fact_alg (s : R →+* R) (a β c u ui : Matrix (Fin n) (Fin n) R) (hu1 : u * ui = 1) (hu2 : ui * u = 1)
    (R2 : c * cj s u = u * cj s c) (C3 : cj s β * u = cj s u * β) :
    cj s (β * ui) = β * ui ∧ cj s (ui * c) = ui * c ∧
      blk4 1 (β * ui) 0 1 * blk4 (a - β * ui * c) 0 0 u * blk4 1 0 (ui * c) 1 = blk4 a β c u := by
  have hcu : cj s ui * cj s u = 1 := by
    rw [← cj_mul, hu1, cj_one']
  have hcu' : cj s u * cj s ui = 1 := by
    rw [← cj_mul, hu2, cj_one']
  have hβ : cj s β = cj s u * β * ui := by
    calc cj s β = cj s β * (u * ui) := by rw [hu1, mul_one]
      _ = cj s u * β * ui := by rw [← mul_assoc, C3]
  have hc : cj s c = ui * c * cj s u := by
    calc cj s c = (ui * u) * cj s c := by rw [hu2, one_mul]
      _ = ui * c * cj s u := by rw [mul_assoc, ← R2, ← mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [cj_mul, hβ, ← mul_assoc, ← mul_assoc, hcu, one_mul]
  · rw [cj_mul, hc, mul_assoc, hcu', mul_one]
  · have e1 : β * ui * u = β := by rw [mul_assoc, hu2, mul_one]
    have e2 : u * (ui * c) = c := by rw [← mul_assoc, hu1, one_mul]
    rw [blk4_mul_blk4, blk4_mul_blk4]
    simp only [mul_zero, zero_mul, add_zero, zero_add, one_mul, mul_one]
    rw [e1, e2, mul_assoc β ui c, sub_add_cancel]

theorem block_matrix_mul_upper_unipotent (a b c d X : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 1 X 0 1 = blk4 a (a * X + b) c (d + c * X) := by
  rw [blk4_mul_blk4]
  simp only [mul_one, mul_zero, add_zero, zero_add]
  rw [add_comm (a * X) b, add_comm (c * X) d]

theorem upper_unipotent_block_inverse (X : Matrix (Fin n) (Fin n) R) : blk4 1 X 0 1 * blk4 1 (-X) 0 1 = 1 := by
  rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]

theorem lower_unipotent_block_inverse (X : Matrix (Fin n) (Fin n) R) : blk4 1 0 X 1 * blk4 1 0 (-X) 1 = 1 := by
  rw [submatrix_fromBlocks_mul]; simp [block_matrix_one]

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FinitePartMemIntegralAdeles
section
noncomputable section

set_option synthInstance.maxHeartbeats 400000

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LFixW.U2

section Gen

theorem tmul_den {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] (x : A) {c : F}
    (hc : c ≠ 0) (b : E) : (x * algebraMap F A c⁻¹) ⊗ₜ[F] (c • b) = x ⊗ₜ[F] b := by
  rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_left_comm, ← map_mul,
    mul_inv_cancel₀ hc, map_one, mul_one]

theorem map_smul_basis {F E R R' ι : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (φ : R →ₐ[F] R') (b : Module.Basis ι F E) (r : R) (k : ι) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (r • Algebra.TensorProduct.basis R b k) = φ r ⊗ₜ[F] b k := by
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

end Gen

variable {D : D7}

abbrev bA (D : D7) := Algebra.TensorProduct.basis (AF D.host.F) (bE D.host.F D.host.E)

theorem crd_cv (v : Pl D) (z : AE D) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (bV (E := D.host.E) v).repr (cv D v z) k = evFin D.host.F v ((bA D).repr z k) :=
  LIdemEx.repr_map' (evFin D.host.F v) (bE D.host.F D.host.E) z k

theorem finPart_plc_mem (v : Pl D) {t : Fv D.host.F v ⊗[D.host.F] D.host.E} (ht : t ∈ intLoc D.host.F D.host.E v) :
    finPart D (plc D.host.E v t) ∈ intAE D := by
  refine intLoc_induction (p := fun t => finPart D (plc D.host.E v t) ∈ intAE D) (fun a ha x => ?_) (by simp)
    (fun y z hy hz => by rw [LinearMap.map_add (f := _), RingHom.map_add (f := _)]; exact add_mem hy hz)
    (fun y hy => by rw [LinearMap.map_neg, RingHom.map_neg]; exact neg_mem hy) ht
  rw [plc_tmul]
  refine AddSubgroup.subset_closure ⟨(iV v a).2, fun w => ?_, x, rfl⟩
  by_cases h : w = v
  · subst h
    show (iV w a).2 w ∈ _
    rw [show (iV w a).2 w = a from GlobalTheory.CompanionTheory.PsiCondLoc.single_self w a]
    exact ha
  · show (iV v a).2 w ∈ _
    rw [show (iV v a).2 w = 0 from GlobalTheory.CompanionTheory.PsiCondLoc.single_ne v a h]
    exact zero_mem _

theorem finPart_mem_of_good {z : AE D} (hb : ∀ v, ¬ IsGood D.host.F D.host.E v → cv D v z = 0)
    (hz : ∀ v, cv D v z ∈ intLoc D.host.F D.host.E v) : finPart D z ∈ intAE D := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (bA D).sum_repr z, map_sum]
  refine sum_mem fun k _ => ?_
  have hN : (den (bE D.host.F D.host.E k) : D.host.F) ≠ 0 := by exact_mod_cast den_ne (bE D.host.F D.host.E k)
  let o : 𝓞 D.host.E := ⟨(den (bE D.host.F D.host.E k) : D.host.E) * bE D.host.F D.host.E k, den_int _⟩
  have ho : (o : D.host.E) = (den (bE D.host.F D.host.E k) : D.host.F) • bE D.host.F D.host.E k := by
    rw [Algebra.smul_def, map_intCast]
    rfl
  have e1 : finPart D ((bA D).repr z k • (bA D) k) =
      sndA D.host.F ((bA D).repr z k) ⊗ₜ[D.host.F] bE D.host.F D.host.E k :=
    map_smul_basis (sndA D.host.F) (bE D.host.F D.host.E) _ k
  rw [e1]
  refine AddSubgroup.subset_closure ⟨sndA D.host.F ((bA D).repr z k) *
    algebraMap D.host.F (Af D.host.F) ((den (bE D.host.F D.host.E k) : D.host.F))⁻¹, fun v => ?_, o,
    by rw [ho]; exact (tmul_den _ hN _).symm⟩
  show evalV D.host.F v (sndA D.host.F ((bA D).repr z k) * algebraMap D.host.F (Af D.host.F) _) ∈ _
  rw [map_mul, AlgHom.commutes]
  have hc : evalV D.host.F v (sndA D.host.F ((bA D).repr z k)) = (bV (E := D.host.E) v).repr (cv D v z) k :=
    (crd_cv v z k).symm
  rw [hc]
  by_cases hv : IsGood D.host.F D.host.E v
  · exact mul_mem ((mem_intLoc_iff hv _).1 (hz v) k) (hv.deninv k)
  · rw [hb v hv, map_zero, Finsupp.zero_apply, zero_mul]
    exact zero_mem _

open Classical in
theorem cv_sub_plc (z : AE D) (B : Finset (Pl D)) (z' : AE D) (hz' : z' = z - ∑ v ∈ B, plc D.host.E v (cv D v z))
    (w : Pl D) : cv D w z' = if w ∈ B then 0 else cv D w z := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hz', RingHom.map_sub, map_sum]
  by_cases hw : w ∈ B
  · rw [if_pos hw, Finset.sum_eq_single w (fun v _ hv => compFin_plc_ne (Ne.symm hv) _) (fun h => absurd hw h),
      compFin_plc_self, sub_self]
  · rw [if_neg hw, Finset.sum_eq_zero (fun v hv => compFin_plc_ne (fun h => hw (by rw [h]; exact hv)) _), sub_zero]

open Classical in
theorem finite_part_mem_integral_adeles (z z' : AE D) (hz : ∀ v, cv D v z ∈ intLoc D.host.F D.host.E v)
    (hfin : {x | ¬IsGood D.host.F D.host.E x}.Finite) (B : Finset (Pl D)) (hB : B = hfin.toFinset)
    (hcv : ∀ w, cv D w z' = if w ∈ B then 0 else cv D w z) : finPart D z' ∈ intAE D := by
  refine finPart_mem_of_good (fun v hv => ?_) (fun v => ?_)
  · rw [hcv, if_pos (by rw [hB]; exact (Set.Finite.mem_toFinset hfin).2 hv)]
  · rw [hcv]
    split_ifs
    · exact zero_mem _
    · exact hz v

theorem finPart_mem (z : AE D) (hz : ∀ v, cv D v z ∈ intLoc D.host.F D.host.E v) : finPart D z ∈ intAE D := by
  have hfin : {x | ¬IsGood D.host.F D.host.E x}.Finite :=
    Filter.eventually_cofinite.1 (eventually_good (F := D.host.F) (E := D.host.E))
  have h1 := finite_part_mem_integral_adeles z _ hz hfin _ rfl (cv_sub_plc z hfin.toFinset _ rfl)
  have e : z = (z - ∑ v ∈ hfin.toFinset, plc D.host.E v (cv D v z)) + ∑ v ∈ hfin.toFinset, plc D.host.E v (cv D v z) :=
    (sub_add_cancel _ _).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, RingHom.map_add (f := _), map_sum]
  exact add_mem h1 (sum_mem fun v _ => finPart_plc_mem v (hz v))

theorem infPart_eq_one {z : AE D} (h : ∀ w, compInf D.host.F D.host.E w z = 1) : infPart D z = 1 := by
  let bI := Algebra.TensorProduct.basis (Ainf D.host.F) (bE D.host.F D.host.E)
  apply bI.repr.injective
  refine Finsupp.ext fun k => ?_
  have h1 := LIdemEx.repr_map' (fstA D.host.F) (bE D.host.F D.host.E) z k
  have h2 := LIdemEx.repr_map' (fstA D.host.F) (bE D.host.F D.host.E) (1 : AE D) k
  have e1 : infPart D z = Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) z := rfl
  have e2 : (1 : Ainf D.host.F ⊗[D.host.F] D.host.E) =
      Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (1 : AE D) := (map_one _).symm
  rw [e1, e2, h1, h2]
  funext w
  have g1 := LIdemEx.repr_map' (evInf D.host.F w) (bE D.host.F D.host.E) z k
  have g2 := LIdemEx.repr_map' (evInf D.host.F w) (bE D.host.F D.host.E) (1 : AE D) k
  have hz : Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) z =
      Algebra.TensorProduct.map (evInf D.host.F w) (AlgHom.id D.host.F D.host.E) 1 := by
    rw [map_one]; exact h w
  rw [hz] at g1
  exact g1.symm.trans g2

end PositivityTheory.Rg.Rsw.L.LFixW.U2

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWD
section
noncomputable section

set_option synthInstance.maxHeartbeats 200000

open scoped Matrix TensorProduct
open IsDedekindDomain NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.AdelicU
  GlobalTheory.MixModel GlobalTheory.StdUnn Filter

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {D : D7}

theorem exists_fin {p : Pl D → Prop} (h : ∀ᶠ v in cofinite, p v) : ∃ S₀ : Finset (Pl D), ∀ v ∉ S₀, p v :=
  ⟨(Filter.eventually_cofinite.1 h).toFinset, fun v hv => by
    rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv; exact hv⟩

def IntS (S : Finset (Pl D)) (a : AE D) : Prop := ∀ v ∉ S, cv D v a ∈ intLoc D.host.F D.host.E v

def OffS (S : Finset (Pl D)) (a : AE D) : Prop :=
  (∀ w, compInf D.host.F D.host.E w a = 0) ∧ (∀ v ∈ S, cv D v a = 0) ∧ IntS S a

variable {S : Finset (Pl D)}

theorem IntS.add {a b : AE D} (ha : IntS S a) (hb : IntS S b) : IntS S (a + b) := fun v hv => by
  rw [map_add (f := _)]; exact add_mem (ha v hv) (hb v hv)

theorem IntS.mul {a b : AE D} (ha : IntS S a) (hb : IntS S b) : IntS S (a * b) := fun v hv => by
  rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)

theorem IntS.neg {a : AE D} (ha : IntS S a) : IntS S (-a) := fun v hv => by
  rw [map_neg]; exact neg_mem (ha v hv)

theorem intS_zero : IntS S (0 : AE D) := fun v _ => by rw [map_zero]; exact zero_mem _

theorem intS_sum {ι : Type} (s : Finset ι) (f : ι → AE D) (h : ∀ i ∈ s, IntS S (f i)) : IntS S (∑ i ∈ s, f i) :=
  fun v hv => by rw [map_sum]; exact sum_mem fun i hi => h i hi v hv

theorem IntS.cA {a : AE D} (ha : IntS S a) : IntS S (cA D a) := fun v hv => by
  rw [LIdemEx.cv_cA]; exact sigR_mem_intLoc _ (ha v hv)

theorem OffS.add {a b : AE D} (ha : OffS S a) (hb : OffS S b) : OffS S (a + b) :=
  ⟨fun w => by rw [map_add (f := _), ha.1 w, hb.1 w, add_zero], fun v hv => by rw [map_add (f := _), ha.2.1 v hv, hb.2.1 v hv, add_zero],
    ha.2.2.add hb.2.2⟩

theorem offS_zero : OffS S (0 : AE D) := ⟨fun w => map_zero _, fun v _ => map_zero _, intS_zero⟩

theorem OffS.neg {a : AE D} (ha : OffS S a) : OffS S (-a) :=
  ⟨fun w => by rw [map_neg, ha.1 w, neg_zero], fun v hv => by rw [map_neg, ha.2.1 v hv, neg_zero], ha.2.2.neg⟩

theorem OffS.mul_left {a b : AE D} (ha : IntS S a) (hb : OffS S b) : OffS S (a * b) :=
  ⟨fun w => by rw [map_mul, hb.1 w, mul_zero], fun v hv => by rw [map_mul, hb.2.1 v hv, mul_zero], ha.mul hb.2.2⟩

theorem OffS.mul_right {a b : AE D} (ha : OffS S a) (hb : IntS S b) : OffS S (a * b) :=
  ⟨fun w => by rw [map_mul, ha.1 w, zero_mul], fun v hv => by rw [map_mul, ha.2.1 v hv, zero_mul], ha.2.2.mul hb⟩

theorem offS_sum {ι : Type} (s : Finset ι) (f : ι → AE D) (h : ∀ i ∈ s, OffS S (f i)) : OffS S (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact offS_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem OffS.cA {a : AE D} (ha : OffS S a) : OffS S (cA D a) :=
  ⟨fun w => by rw [LIdemEx.compInf_cA, ha.1 w, map_zero], fun v hv => by rw [LIdemEx.cv_cA, ha.2.1 v hv, map_zero],
    ha.2.2.cA⟩

theorem OffS.intS {a : AE D} (ha : OffS S a) : IntS S a := ha.2.2

theorem intOff_iff {a b : ℕ} (x : Mx D a b) : IntOff S x ↔ ∀ i j, IntS S (x i j) :=
  ⟨fun h i j v hv => h v hv i j, fun h v hv i j => h i j v hv⟩

theorem offS_mul_left {a b c : ℕ} {x : Mx D a b} {y : Mx D b c} (hx : ∀ i j, IntS S (x i j)) (hy : ∀ i j, OffS S (y i j))
    (i : Fin a) (j : Fin c) : OffS S ((x * y) i j) := by
  rw [Matrix.mul_apply]; exact offS_sum _ _ fun k _ => (hy k j).mul_left (hx i k)

theorem offS_mul_right {a b c : ℕ} {x : Mx D a b} {y : Mx D b c} (hx : ∀ i j, OffS S (x i j)) (hy : ∀ i j, IntS S (y i j))
    (i : Fin a) (j : Fin c) : OffS S ((x * y) i j) := by
  rw [Matrix.mul_apply]; exact offS_sum _ _ fun k _ => (hx i k).mul_right (hy k j)

theorem intS_mul {a b c : ℕ} {x : Mx D a b} {y : Mx D b c} (hx : ∀ i j, IntS S (x i j)) (hy : ∀ i j, IntS S (y i j))
    (i : Fin a) (j : Fin c) : IntS S ((x * y) i j) := by
  rw [Matrix.mul_apply]; exact intS_sum _ _ fun k _ => (hx i k).mul (hy k j)

theorem offS_trace {a : ℕ} {x : Mx D a a} (hx : ∀ i j, OffS S (x i j)) : OffS S (Matrix.trace x) :=
  offS_sum _ _ fun i _ => hx i i

theorem adj_intS {a b : ℕ} {x : Mx D a b} (hx : ∀ i j, IntS S (x i j)) (i : Fin b) (j : Fin a) : IntS S (adj x i j) :=
  (hx j i).cA

theorem adj_offS {a b : ℕ} {x : Mx D a b} (hx : ∀ i j, OffS S (x i j)) (i : Fin b) (j : Fin a) : OffS S (adj x i j) :=
  (hx j i).cA

theorem exists_rat_int {a b : ℕ} (Q : Matrix (Fin a) (Fin b) D.host.E) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ i j, IntS S (rat Q i j) := by
  have h : ∀ᶠ v : Pl D in cofinite, IsGood D.host.F D.host.E v ∧ ∀ i j k,
      algebraMap D.host.F (Fv D.host.F v) ((bE D.host.F D.host.E).repr (Q i j) k) ∈ v.adicCompletionIntegers D.host.F :=
    eventually_good.and (eventually_all.2 fun i => eventually_all.2 fun j => eventually_coord (Q i j))
  obtain ⟨S₀, hS₀⟩ := exists_fin h
  refine ⟨S₀, fun S hS i j v hv => ?_⟩
  obtain ⟨hg, hc⟩ := hS₀ v (fun h => hv (hS h))
  show (1 : Fv D.host.F v) ⊗ₜ[D.host.F] Q i j ∈ _
  refine (mem_intLoc_iff hg _).2 fun k => ?_
  rw [crd_tmul, one_mul]
  exact hc i j k

theorem psi_off {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ z : AE D, OffS S z → ψ (trA z) = 1 ∧ ψ (halfTr z) = 1 := by
  classical
  obtain ⟨S₁, hS₁⟩ := psi_kernel hψ
  obtain ⟨S₂, hS₂⟩ := exists_fin (eventually_good (F := D.host.F) (E := D.host.E))
  refine ⟨S₁ ∪ S₂, fun S hS z hz => ?_⟩
  have h1 : (trA z).1 = 0 := funext fun w => by rw [trA_fst, hz.1 w, map_zero]; rfl
  have hg : ∀ v ∉ S, IsGood D.host.F D.host.E v := fun v hv =>
    hS₂ v fun h => hv (hS (Finset.mem_union_right _ h))
  have h2 : ∀ v ∈ S, (trA z).2 v = 0 := fun v hv => by rw [trA_snd, hz.2.1 v hv, map_zero]
  have h3 : ∀ v ∉ S, (trA z).2 v ∈ v.adicCompletionIntegers D.host.F := fun v hv => by
    rw [trA_snd]; exact trace_mem (hg v hv) (hz.2.2 v hv)
  have hS1 : S₁ ⊆ S := fun v h => hS (Finset.mem_union_left _ h)
  refine ⟨hS₁ S hS1 _ h1 h2 h3, hS₁ S hS1 _ ?_ ?_ ?_⟩
  · show (algebraMap D.host.F (AF D.host.F) (1 / 2)).1 * (trA z).1 = 0
    rw [h1, mul_zero]
  · intro v hv
    show (algebraMap D.host.F (AF D.host.F) (1 / 2)).2 v * (trA z).2 v = 0
    rw [h2 v hv, mul_zero]
  · intro v hv
    show (algebraMap D.host.F (AF D.host.F) (1 / 2)).2 v * (trA z).2 v ∈ _
    refine mul_mem ?_ (h3 v hv)
    have := (hg v hv).half
    rwa [one_div]

theorem dual_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ v ∉ S₀, ∀ c : Fv D.host.F v ⊗[D.host.F] D.host.E,
      (∀ t ∈ intLoc D.host.F D.host.E v,
        psiV D.host.F ψ v (Algebra.trace (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) (c * t)) = 1) →
      c ∈ intLoc D.host.F D.host.E v := by
  obtain ⟨S₀, hS₀⟩ := exists_fin ((eventually_good (F := D.host.F) (E := D.host.E)).and
    (GlobalTheory.CompanionTheory.PsiCondLoc.psiCond D.host.F ψ hψ))
  refine ⟨S₀, fun v hv c hc => ?_⟩
  obtain ⟨hg, hp⟩ := hS₀ v hv
  refine mem_of_trace hg c fun t ht => (hp _).1 fun s hs => ?_
  have hst : algebraMap (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) s * t ∈ intLoc D.host.F D.host.E v := by
    refine mul_mem ?_ ht
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    exact tmul_one_mem hs
  have := hc _ hst
  have e : c * (algebraMap (Fv D.host.F v) (Fv D.host.F v ⊗[D.host.F] D.host.E) s * t) = s • (c * t) := by
    rw [Algebra.smul_def]; ring
  rw [e, LinearMap.map_smul, smul_eq_mul, mul_comm] at this
  exact this

end PositivityTheory.Rg.Rsw.L.LFixW

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LMajorE
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LMajor

variable {D : D7} {a b : ℕ}

theorem row_smul (i : Fin a) (c : AE D) (x : Mx D a b) : row i (c • x) = c • row i x := by
  rfl

theorem intOff_row {S : Finset (Pl D)} {x : Mx D a b} (hx : IntOff S x) (i : Fin a) : IntOff S (row i (sF D • x)) := by
  intro v hv i' j
  show cv D v (sF D * x i j) ∈ _
  rw [cv_sF]
  exact hx v hv i j

theorem not_intOff_row {S : Finset (Pl D)} {x : Mx D a b} (hx : ¬ IntOff S x) :
    ∃ i, ¬ IntOff S (row i (sF D • x)) := by
  by_contra hcon
  push Not at hcon
  apply hx
  intro v hv i j
  have e := hcon i v hv 0 j
  have e' : cv D v (sF D * x i j) ∈ GlobalTheory.AdelicU.intLoc (↥D.host.F) D.host.E v := e
  rwa [cv_sF] at e'


set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 800000 in
theorem bumpMaj (hB : BumpEx) (θ : InfFam D) (hθ : IsInfFam θ) {S : Finset (Pl D)} {e : AE D} (he : IsIdem S e)
    (K : Set (Mx D a b)) (hK : IsCompact K) (F₀ : SchwartzMap (D.what₂.Tau → Fin a → Fin b → ℂ) ℂ)
    (hF₀ : ∀ y, 0 ≤ (F₀ y).re ∧ (F₀ y).im = 0) :
    ∃ Φ₀ ∈ schwartzA θ a b, Good S e Φ₀ ∧ (∀ x, 0 ≤ (Φ₀ x).re ∧ (Φ₀ x).im = 0) ∧
      ∀ x, IntOff S x → GlobalTheory.Unf.InBox K x → Φ₀ x = F₀ (cA θ x) := by
  have hCint : ∀ y ∈ (fun k => sF D • (e • k)) '' K, IntOff S y := by
    rintro _ ⟨k, -, rfl⟩ v hv i j
    show cv D v (sF D * (e * k i j)) ∈ _
    rw [cv_sF, map_mul, he.2 v, if_neg hv, zero_mul]
    exact (GlobalTheory.AdelicU.intLoc _ _ v).zero_mem
  obtain ⟨η, hη⟩ := hB D θ hθ a b S e he _
    (hK.image ((continuous_const_smul (sF D)).comp (continuous_const_smul e))) hCint
  have hG : ∀ i, ∃ G ∈ GlobalTheory.WeilM.SB (Fin 1 → Fin b → TensorProduct (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af ↥D.host.F) D.host.E),
      ∀ y : Mx D 1 b, η i (sF D • y) = G fun i' j => finPart D (y i' j) :=
    fun i => rowSB θ (sF D) infPart_sF finPart_sF (η i) (hη i).1
  choose G hGSB hGeq using hG
  set Ψ : Mx D a b → ℂ := fun x => ∏ i, η i (sF D • row i x) with hΨ
  have hΨG : ∀ x, Ψ x = (fun z => ∏ i, G i fun _ j => z i j) (fun i j => finPart D (x i j)) := by
    intro x
    exact Finset.prod_congr rfl fun i _ => hGeq i (row i x)
  have hΨgood : Good S e Ψ := by
    intro x
    by_cases hx : IntOff S x
    · rw [if_pos hx]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← row_smul, (hη i).2.2.1, if_pos (intOff_row hx i), ← row_smul, ← row_smul, smul_comm e (sF D) x]
    · rw [if_neg hx]
      obtain ⟨i, hi⟩ := not_intOff_row hx
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [← row_smul, (hη i).2.2.1, if_neg hi]
  refine ⟨fun x => F₀ (cA θ x) * Ψ x, ?_, good_mul θ he hΨgood (fun z => F₀ z), ?_, ?_⟩
  · apply Submodule.subset_span
    refine ⟨F₀, fun z => ∏ i, G i fun _ j => z i j, prodSB G hGSB, ?_⟩
    funext x
    rw [hΨG x]
  · intro x
    exact re_im_mul (hF₀ _) (re_im_prod _ _ fun i => ⟨((hη i).2.2.2.1 _).1, ((hη i).2.2.2.1 _).2.2⟩)
  · rintro x hx ⟨k, hk, hxk⟩
    have hfin : ∀ i j, finPart D (x i j) = finPart D (k i j) := by
      intro i j
      have h0 := congrFun (congrFun hxk i) j
      simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.zero_apply] at h0
      exact sub_eq_zero.mp h0
    suffices h1 : Ψ x = 1 by
      show F₀ (cA θ x) * Ψ x = F₀ (cA θ x)
      rw [h1, mul_one]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← row_smul, (hη i).2.2.1, if_pos (intOff_row hx i), ← row_smul, smul_comm e (sF D) x, row_smul, hGeq i]
    have hfun : (fun i' j => finPart D ((row i (e • x)) i' j)) = (fun i' j => finPart D ((row i (e • k)) i' j)) := by
      funext i' j
      show finPart D (e * x i j) = finPart D (e * k i j)
      rw [map_mul, map_mul, hfin]
    rw [hfun, ← hGeq i, ← row_smul]
    exact (hη i).2.2.2.2 _ ⟨k, hk, rfl⟩

end PositivityTheory.Rg.Rsw.L.LMajor

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LNullSing
section
namespace PositivityTheory.Rg.Rsw.L

theorem nullSing : IdemEx → NullSing := GlobalTheory.CompanionTheory.NullFr.nullSing_of_idemEx

end PositivityTheory.Rg.Rsw.L
end

