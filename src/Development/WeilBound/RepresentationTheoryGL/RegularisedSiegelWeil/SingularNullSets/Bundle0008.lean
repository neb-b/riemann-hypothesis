module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0005

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.MulVecInt
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

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Rg.Rsw.L.LGenK

variable {D : D7} {n : ℕ}

theorem mat_proj (v : Pl D) (g : G D n) :
    ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) :
      Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) = (mat g).map (cv D v) := rfl

theorem mulVec_int (v : Pl D) {m : ℕ} (A : Matrix (Fin m) (Fin m) (Fv D.host.F v ⊗[D.host.F] D.host.E))
    (x : Fin m → Fv D.host.F v ⊗[D.host.F] D.host.E) (hA : ∀ i j, A i j ∈ intLoc D.host.F D.host.E v)
    (hx : ∀ j, x j ∈ intLoc D.host.F D.host.E v) (i : Fin m) : (A *ᵥ x) i ∈ intLoc D.host.F D.host.E v := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hA i j) (hx j)

theorem single_int (v : Pl D) {m : ℕ} (j : Fin m) (i : Fin m) :
    (Pi.single j (1 : Fv D.host.F v ⊗[D.host.F] D.host.E) : Fin m → _) i ∈ intLoc D.host.F D.host.E v := by
  rw [Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem KOff_props {D : D7} {n : ℕ} {S : Finset (Pl D)} {k : G D n} (hk : k ∈ KOff D n S) :
    (mat k).map (infPart D) = 1 ∧ (∀ v ∈ S, (mat k).map (cv D v) = 1) ∧
    ∀ v ∉ S, ∀ i j, cv D v (mat k i j) ∈ intLoc D.host.F D.host.E v := by
  obtain ⟨⟨hfin, haway⟩, hoff⟩ := Subgroup.mem_inf.1 hk
  refine ⟨congrArg Units.val (MonoidHom.mem_ker.1 hfin), fun v hv => ?_, fun v hv i j => ?_⟩
  · have h1 := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 haway v) hv)
    rw [← mat_proj, h1, map_one, Units.val_one]
  · have h1 := Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hoff v) hv)
    have h2 := Subgroup.mem_comap.1 h1
    have hs : (Pi.single j 1 : Fin (n + n) → Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
        latLoc D.host.F (stdLattice D.host.E (n + n)) v :=
      mem_latLoc_stdLattice.2 (single_int v j)
    have h3 := mem_latLoc_stdLattice.1 ((h2 _).1 hs) i
    rw [mat_proj] at h3
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h3

theorem mem_KOff {D : D7} {n : ℕ} {S : Finset (Pl D)} (g : G D n) (hinf : (mat g).map (infPart D) = 1)
    (hS : ∀ v ∈ S, (mat g).map (cv D v) = 1)
    (hint : ∀ v ∉ S, ∀ i j, cv D v (mat g i j) ∈ intLoc D.host.F D.host.E v ∧
      cv D v (mat g⁻¹ i j) ∈ intLoc D.host.F D.host.E v) :
    g ∈ KOff D n S := by
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (Units.ext hinf), ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => MonoidHom.mem_ker.2 ?_
    refine matHom_injective _ _ _ (Units.ext ?_)
    rw [mat_proj, hS v hv, map_one, Units.val_one]
  · refine Subgroup.mem_iInf.2 fun v => Subgroup.mem_iInf.2 fun hv => ?_
    refine Subgroup.mem_comap.2 (Subgroup.mem_comap.2 ?_)
    have hM : ∀ i j, ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) i j ∈ intLoc D.host.F D.host.E v := by
      intro i j; rw [mat_proj]; exact (hint v hv i j).1
    have hM' : ∀ i j, ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g⁻¹) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) i j ∈ intLoc D.host.F D.host.E v := by
      intro i j; rw [mat_proj]; exact (hint v hv i j).2
    have hinv : ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g⁻¹) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) *
        ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
        (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) = 1 := by
      rw [← Units.val_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Units.val_one]
    intro x
    rw [mem_latLoc_stdLattice, mem_latLoc_stdLattice]
    constructor
    · intro hx i
      exact mulVec_int v _ x hM hx i
    · intro hx i
      have e : x = ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
          (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g⁻¹) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) *ᵥ
          (((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n)
          (GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g) : GL (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) : Matrix (Fin (n + n)) (Fin (n + n)) (Fv D.host.F v ⊗[D.host.F] D.host.E)) *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      rw [e]
      exact mulVec_int v _ _ hM' hx i

end PositivityTheory.Rg.Rsw.L.LGenK
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.NatCastMulGen
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

variable {D : D7}

theorem norm_mem {v : Pl D} (hv : IsGood D.host.F D.host.E v) {x : Fv D.host.F v ⊗[D.host.F] D.host.E}
    (hx : x ∈ intLoc D.host.F D.host.E v) :
    Algebra.norm (Fv D.host.F v) x ∈ v.adicCompletionIntegers D.host.F := by
  classical
  rw [Algebra.norm_eq_matrix_det (bV (E := D.host.E) v), Matrix.det_apply]
  have hM : ∀ i j, Algebra.leftMulMatrix (bV (E := D.host.E) v) x i j ∈ v.adicCompletionIntegers D.host.F := by
    intro i j
    rw [Algebra.leftMulMatrix_eq_repr_mul]
    have hb : bV (E := D.host.E) v j ∈ intLoc D.host.F D.host.E v := by
      rw [bV_apply]; exact one_tmul_b_mem hv j
    exact (mem_intLoc_iff hv _).1 (mul_mem hx hb) i
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => hM _ _) _

theorem absEv_eq_one {v : Pl D} (hv : IsGood D.host.F D.host.E v) (x : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ)
    (h1 : (x : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v)
    (h2 : ((x⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
      intLoc D.host.F D.host.E v) :
    absEv D.host.F D.host.E v x = 1 := by
  have k : ∀ y : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, (y : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
      intLoc D.host.F D.host.E v → absEv D.host.F D.host.E v y ≤ 1 := fun y hy => by
    rw [absEv_apply]
    exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 (norm_mem hv hy)
  have a1 := k x h1
  have a2 := k _ h2
  have hm : absEv D.host.F D.host.E v x * absEv D.host.F D.host.E v x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  refine le_antisymm a1 ?_
  calc (1 : ℝ≥0) = absEv D.host.F D.host.E v x * absEv D.host.F D.host.E v x⁻¹ := hm.symm
    _ ≤ absEv D.host.F D.host.E v x * 1 := mul_le_mul_of_nonneg_left a2 (by positivity)
    _ = absEv D.host.F D.host.E v x := mul_one _

def cN (D : D7) (N : ℕ) : AE D := algebraMap D.host.F (AF D.host.F) ((N : D.host.F)⁻¹) ⊗ₜ[D.host.F] (1 : D.host.E)

theorem cv_cN (v : Pl D) (N : ℕ) :
    cv D v (cN D N) = algebraMap D.host.F (Fv D.host.F v) ((N : D.host.F)⁻¹) ⊗ₜ[D.host.F] (1 : D.host.E) := by
  show evFin D.host.F v (algebraMap D.host.F (AF D.host.F) _) ⊗ₜ[D.host.F] (1 : D.host.E) = _
  rw [AlgHom.commutes]

theorem natCast_mul_gen {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A] {N : ℕ}
    (hN : (N : F) ≠ 0) : (N : A ⊗[F] E) * (algebraMap F A ((N : F)⁻¹) ⊗ₜ[F] (1 : E)) = 1 := by
  rw [(map_natCast (Algebra.TensorProduct.includeLeftRingHom (R := F) (A := A) (B := E)) N).symm]
  show ((N : A) ⊗ₜ[F] (1 : E)) * _ = 1
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_natCast (algebraMap F A) N, ← map_mul,
    mul_inv_cancel₀ hN, map_one]
  rfl

theorem natCast_mul_cN {N : ℕ} (hN : 0 < N) : (N : AE D) * cN D N = 1 :=
  natCast_mul_gen (by exact_mod_cast hN.ne')

end PositivityTheory.Rg.Rsw.L.LFixW.U2

end
end

