module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0392
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0006
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOfEntries
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta GlobalTheory.Mem.Th Filter Topology MeasureTheory
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC
attribute [local instance] GlobalTheory.Mem.Col2.starE
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

theorem sum_ite_val {m : ℕ} (f : Fin m → ℂ) (c : ℕ) (hc : c < m) :
    ∑ j : Fin m, (if (j : ℕ) = c then f j else 0) = f ⟨c, hc⟩ := by
  rw [Finset.sum_eq_single ⟨c, hc⟩]
  · simp
  · intro j _ hj
    rw [if_neg]
    exact fun h => hj (Fin.ext h)
  · simp

theorem sum_ite_val_zero {m : ℕ} (f : Fin m → ℂ) (c : ℕ) (hc : m ≤ c) :
    ∑ j : Fin m, (if (j : ℕ) = c then f j else 0) = 0 :=
  Finset.sum_eq_zero fun j _ => if_neg (by have := j.2; omega)

theorem isBlock_of_frame {p q N n : ℕ} (hp : p = N) (hq : q = n) (hN : N = n + 1) (M : Matrix (Fin p) (Fin p) ℂ)
    (M' : Matrix (Fin q) (Fin q) ℂ)
    (h1 : M * Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) =
      Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) * M')
    (h2 : M *ᵥ (fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) = fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) :
    GlobalTheory.BranchFormula.IsBlock hN (fun i j : Fin N => M (Fin.cast hp.symm i) (Fin.cast hp.symm j))
      (fun a b : Fin n => M' (Fin.cast hq.symm a) (Fin.cast hq.symm b)) 1 := by
  subst hp hq hN
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · have e := congrFun (congrFun h1 (Br.iC rfl a)) b
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul] at e
    simp only [eq_comm (a := ((Br.iC rfl a : Fin (q+1)) : ℕ))] at e
    rw [sum_ite_val _ _ (by have := b.2; omega), sum_ite_val _ _ (show ((Br.iC rfl a : Fin (q+1)) : ℕ) < q from a.2)] at e
    exact e
  · have e := congrFun h2 (Br.iC rfl a)
    simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero] at e
    rw [sum_ite_val _ _ (by omega), if_neg (by have := a.2; simp [Br.iC]; omega)] at e
    exact e
  · have e := congrFun (congrFun h1 (Br.iL rfl)) a
    simp only [Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul] at e
    simp only [eq_comm (a := ((Br.iL rfl : Fin (q+1)) : ℕ))] at e
    rw [sum_ite_val _ _ (by have := a.2; omega), sum_ite_val_zero _ _ (by simp [Br.iL])] at e
    exact e
  · have e := congrFun h2 (Br.iL rfl)
    simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero] at e
    rw [sum_ite_val _ _ (by omega), if_pos (by simp [Br.iL])] at e
    exact e

end GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

namespace GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

theorem isBlock_of_entries {p q N n : ℕ} (hp : p = N) (hq : q = n) (hN : N = n + 1) (M : Matrix (Fin p) (Fin p) ℂ)
    (M' : Matrix (Fin q) (Fin q) ℂ) (A : Matrix (Fin N) (Fin N) ℂ) (A' : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, A i j = M (Fin.cast hp.symm i) (Fin.cast hp.symm j))
    (hA' : ∀ i j, A' i j = M' (Fin.cast hq.symm i) (Fin.cast hq.symm j))
    (h1 : M * Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) =
      Matrix.of (fun (i : Fin p) (a : Fin q) => if (i : ℕ) = a then (1 : ℂ) else 0) * M')
    (h2 : M *ᵥ (fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) = fun i : Fin p => if (i : ℕ) = q then (1 : ℂ) else 0) :
    GlobalTheory.BranchFormula.IsBlock hN A A' 1 := by
  have e1 : A = fun i j => M (Fin.cast hp.symm i) (Fin.cast hp.symm j) := funext fun i => funext fun j => hA i j
  have e2 : A' = fun i j => M' (Fin.cast hq.symm i) (Fin.cast hq.symm j) := funext fun i => funext fun j => hA' i j
  subst e1 e2
  exact isBlock_of_frame hp hq hN M M' h1 h2

end GlobalTheory.Mem.Col2.TC.BlockMatrixCriteria

namespace GlobalTheory.Mem.Col2.TC

end GlobalTheory.Mem.Col2.TC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProdLevelStdFrameTwoBlockUnipotentLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MtInProd

section Cut

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

def cutMat (e : R) (M : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R := e • M + (1 - e) • 1

theorem cutMat_one (e : R) : cutMat e (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [cutMat, ← add_smul, add_sub_cancel, one_smul]

theorem cutMat_one_left (M : Matrix (Fin n) (Fin n) R) : cutMat 1 M = M := by
  rw [cutMat, one_smul, sub_self, zero_smul, add_zero]

theorem cutMat_zero_left (M : Matrix (Fin n) (Fin n) R) : cutMat 0 M = 1 := by
  rw [cutMat, zero_smul, sub_zero, one_smul, zero_add]

theorem cutMat_mul {e : R} (he : e * e = e) (M N : Matrix (Fin n) (Fin n) R) :
    cutMat e (M * N) = cutMat e M * cutMat e N := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [cutMat, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one, he, h1,
    h2, h3, zero_smul, add_zero, zero_add]

theorem cutMat_mul_compl {e : R} (he : e * e = e) (M : Matrix (Fin n) (Fin n) R) :
    cutMat e M * cutMat (1 - e) M = M := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he, sub_self]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, h2, sub_zero]
  simp only [cutMat, sub_sub_cancel, add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul,
    Matrix.mul_one, he, h1, h2, h3, zero_smul, add_zero, zero_add]
  rw [← add_smul, sub_add_cancel, one_smul]

theorem map_cutMat (f : R →+* S) (e : R) (M : Matrix (Fin n) (Fin n) R) :
    (cutMat e M).map f = cutMat (f e) (M.map f) := by
  ext i j
  by_cases h : i = j <;> simp [cutMat, Matrix.one_apply, h]

theorem conjT_cutMat (σ : R →+* R) {e : R} (hσ : σ e = e) (M : Matrix (Fin n) (Fin n) R) :
    ReciprocityTheory.Aut.conjT σ (cutMat e M) = cutMat e (ReciprocityTheory.Aut.conjT σ M) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [ReciprocityTheory.Aut.conjT, cutMat, hσ]
  · simp [ReciprocityTheory.Aut.conjT, cutMat, hσ, Matrix.one_apply, h, Ne.symm h]

def cutHom {e : R} (he : e * e = e) : Matrix (Fin n) (Fin n) R →* Matrix (Fin n) (Fin n) R where
  toFun := cutMat e
  map_one' := cutMat_one e
  map_mul' := cutMat_mul he

end Cut

section Adelic

open ReciprocityTheory.Aut

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

open Classical

def idemF (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AFplus L :=
  ⟨fun w => if w = v then 1 else 0, Filter.Eventually.of_forall fun w => by
    dsimp only
    split_ifs
    · exact one_mem _
    · exact zero_mem _⟩

theorem idemF_apply (v w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    (idemF (L := L) v) w = if w = v then 1 else 0 := rfl

theorem idemF_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : idemF (L := L) v * idemF v = idemF v := by
  apply Subtype.ext
  funext w
  show (if w = v then (1 : w.adicCompletion (maximalRealSubfield L)) else 0) * (if w = v then 1 else 0) = (if w = v then 1 else 0)
  split_ifs <;> simp


variable (L) in
def eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : AL L := (1 : L) ⊗ₜ[maximalRealSubfield L] idemF v

theorem eA_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : eA L v * eA L v = eA L v := by
  rw [eA, Algebra.TensorProduct.tmul_mul_tmul, one_mul, idemF_mul]

theorem conj_eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : conjAL L (eA L v) = eA L v := by
  simp [conjAL, eA, Algebra.TensorProduct.map_tmul]

theorem compAt_eA (w v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    compAt L w (eA L v) = if w = v then 1 else 0 := by
  have : compAt L w (eA L v) = (1 : L) ⊗ₜ[maximalRealSubfield L] ((idemF (L := L) v) w) := rfl
  rw [this, idemF_apply]
  split_ifs
  · rfl
  · exact TensorProduct.tmul_zero _ _

theorem eA_mem (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) : eA L v ∈ ALint L :=
  Subring.subset_closure (Or.inr ⟨idemF v, fun w => by
    rw [idemF_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _, rfl⟩)

def cutGA {e : AL L} (he : e * e = e) (hc : conjAL L e = e) : GA L n →* GA L n :=
  ((Units.map (cutHom (n := n) he)).comp (GA L n).subtype).codRestrict _ (fun g => by
    have hg : (g.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) g.1 = 1 := g.2
    show cutMat e (g.1 : Matrix (Fin n) (Fin n) (AL L)) * conjT (conjAL L) (cutMat e g.1) = 1
    rw [conjT_cutMat _ hc, ← cutMat_mul he, hg, cutMat_one])

theorem cutGA_val {e : AL L} (he : e * e = e) (hc : conjAL L e = e) (g : GA L n) :
    ((cutGA he hc g).1 : Matrix (Fin n) (Fin n) (AL L)) = cutMat e g.1 := rfl

theorem cutGA_mem_Umax {e : AL L} (he : e * e = e) (hc : conjAL L e = e) (heI : e ∈ ALint L) {g : GA L n}
    (hg : g ∈ Umax L n) : cutGA he hc g ∈ Umax L n := by
  have hg' : ∀ i j, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := hg
  show ∀ i j, ((cutGA he hc g).1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L
  intro i j
  rw [cutGA_val]
  simp only [cutMat, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  refine Subring.add_mem _ (Subring.mul_mem _ heI (hg' i j)) (Subring.mul_mem _ (Subring.sub_mem _ (Subring.one_mem _) heI) ?_)
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

end Adelic

section Adelic2

open ReciprocityTheory.Aut

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem cut_map_compAt {e : AL L} (he : e * e = e) (hc : conjAL L e = e) (g : GA L n)
    (w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    ((cutGA he hc g).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w) =
      cutMat (compAt L w e) ((g.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L w)) := by
  rw [cutGA_val, map_cutMat]

theorem one_sub_eA_mul (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    (1 - eA L v) * (1 - eA L v) = 1 - eA L v := by
  rw [mul_sub, mul_one, sub_mul, one_mul, eA_mul, sub_self, sub_zero]

theorem conj_one_sub_eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) :
    conjAL L (1 - eA L v) = 1 - eA L v := by
  rw [map_sub, map_one, conj_eA]

theorem triv_cut_eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GA L n) :
    TrivOutside {v} (cutGA (eA_mul v) (conj_eA v) g) := by
  intro w hw
  rw [cut_map_compAt, compAt_eA, if_neg (fun h => hw (Set.mem_singleton_iff.2 h)), cutMat_zero_left]

theorem triv_cut_one_sub_eA (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GA L n) :
    TrivOutside {v}ᶜ (cutGA (one_sub_eA_mul v) (conj_one_sub_eA v) g) := by
  intro w hw
  have hwv : w = v := by simpa using hw
  rw [cut_map_compAt, map_sub, map_one, compAt_eA, if_pos hwv, sub_self, cutMat_zero_left]

theorem cut_eA_at (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GA L n) :
    ((cutGA (eA_mul v) (conj_eA v) g).1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) =
      (g.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L v) := by
  rw [cut_map_compAt, compAt_eA, if_pos rfl, cutMat_one_left]

theorem cut_mul_cut (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GA L n) :
    cutGA (eA_mul v) (conj_eA v) g * cutGA (one_sub_eA_mul v) (conj_one_sub_eA v) g = g :=
  Subtype.ext (Units.ext (cutMat_mul_compl (eA_mul v) _))

end Adelic2

theorem main : ∀ (D : D7) (n : ℕ) (hr : D.R.r ≤ n) (Pg Q : Finset (Pl D.host.E)) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ)
    (chi xi : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), NG.IsProdLevel (stdJ (datV D n hr Pg Q (P0 Pg D.R.r ψ) chi xi)) := by
  intro D n hr Pg Q ψ chi xi κ hκ v
  obtain ⟨hUA, hSt, hred, -⟩ := _root_.GlobalTheory.MtRed.km_reduction D n
  set κ1 := cutGA (eA_mul v) (conj_eA v) κ with hκ1
  set κ2 := cutGA (one_sub_eA_mul v) (conj_one_sub_eA v) κ with hκ2
  have hκ' := Subgroup.mem_comap.1 hκ
  rw [mem_lev, mem_parLev] at hκ'
  obtain ⟨⟨-, hSκ, hPg, hQ⟩, hT⟩ := hκ'
  have hUm : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n := (hSt κ).1 hSκ
  have hUm1 : κ1 ∈ ReciprocityTheory.Aut.Umax D.host.E n := cutGA_mem_Umax _ _ (eA_mem v) hUm
  have hUm2 : κ2 ∈ ReciprocityTheory.Aut.Umax D.host.E n :=
    cutGA_mem_Umax _ _ (Subring.sub_mem _ (Subring.one_mem _) (eA_mem v)) hUm
  have key : ∀ PP, redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ1) = redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ) ∨
      redFn (1 : GL (Fin n) (EAf D)) PP (km D n κ1) = 1 := by
    intro PP
    have hov : NG.OverPl PP (underPl (maximalRealSubfield D.host.E) PP) := (underPl_asIdeal (F := maximalRealSubfield D.host.E) PP).symm
    by_cases h : underPl (maximalRealSubfield D.host.E) PP = v
    · left
      rw [← cut_mul_cut v κ, map_mul, redFn_mul ((hSt _).2 hUm1) ((hSt _).2 hUm2),
        hred κ2 hUm2 {v}ᶜ _ PP (triv_cut_one_sub_eA v κ) (h ▸ hov) (by simp), mul_one]
    · right
      exact hred κ1 hUm1 {v} _ PP (triv_cut_eA v κ) hov h
  refine ⟨κ1, ?_, triv_cut_eA v κ, cut_eA_at v κ⟩
  apply Subgroup.mem_comap.2
  rw [mem_lev, mem_parLev]
  refine ⟨⟨hUA κ1, (hSt κ1).2 hUm1, fun PP hP => ?_, fun PP hP => ?_⟩, ?_⟩
  · rcases key PP with h | h <;> rw [h]
    · exact hPg PP hP
    · exact Subgroup.one_mem _
  · rcases key PP with h | h <;> rw [h]
    · exact hQ PP hP
    · exact Subgroup.one_mem _
  · intro PP _
    have hT' := hT PP (Set.mem_univ _)
    show upperLeftBlock _ (redFn _ PP.1 (km D n κ1)) ∈ _
    rcases key PP.1 with h | h <;> rw [h]
    · exact hT'
    · have h2 : upperLeftBlock (MtIn.datV D n hr Pg Q (P0 Pg D.R.r ψ) chi xi).hr (1 : GL (Fin n) (kP PP.1)) = 1 := blockDiagonalExtendByOnePrimeField_one _ _
      show upperLeftBlock (MtIn.datV D n hr Pg Q (P0 Pg D.R.r ψ) chi xi).hr (1 : GL (Fin n) (kP PP.1)) ∈ unip (kP PP.1) D.R.r
      rw [h2]
      exact (unip (kP PP.1) D.R.r).one_mem

end GlobalTheory.MtInProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LayeredAutomorphicDataExistsOfTwoPasses
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem untw_set_eq (B : Base) (pl : Finset ℕ) (f : Fr B.toPre) :
    (TwDat.untw B pl).set f = {1, f.del, f.del'} := by
  refine Set.union_eq_left.2 ?_
  rintro _ ⟨w, rfl⟩
  change (if _ then f.del' else f.del) * 1 ∈ _
  rw [mul_one]
  split_ifs
  · exact .inr (.inr rfl)
  · exact .inr (.inl rfl)

theorem recAtG_of_two_passes : (∀ D : D7, Formalism.L2.Theta.VolTieG D → StandardLattice.VolumeEqMass₂ D) →
    ∀ (KP : GroupRetwisting.BaseP) (Q Q' : V4.Slot), GroupRetwisting.BaseCond KP → GroupRetwisting.FirstG KP Q → GroupRetwisting.ExportF KP Q → GroupRetwisting.SecondG KP Q Q' →
      RecAtG (fun K D Y => GroupRetwisting.FromCoreAt Q' K D Y ∧ DQ.TupUsedAt D ∧ DQ.TwAllAt D Y.nch Y.xd ∧ DQ.MtStableAt D) := by
  intro h2v KP Q Q' hK hF hX hS
  have hL := EvG.imp (EvG.inter hF (EvG.inter hX hS)) fun K _ _ _ _ H =>
    (large₂.inter (large₂.inter H.1 (lg_forced K)) (large₂.inter H.2.1 H.2.2))
  refine EvG.imp (EvG.inter (EvG.inter hK.ex hL) (evG_of_ev GlobalTheory.Mem.Top.LayOfCore.lay_of_core)) ?_
  rintro K _ _ _ _ ⟨⟨⟨P, f₀, hO, hks⟩, S₁, P₁, A, S₂, a₁, a₂, hlg⟩, hlay⟩
  obtain ⟨B, f, hB, hf, hKP, hH₁, hH₂⟩ := hks (S₁ P f₀) (fun F F₀ => S₂ P f₀ F F₀ {1, f₀.del, f₀.del'}) (a₁ _ _)
    (fun F F₀ => a₂ _ _ F F₀ _)
  subst hB
  obtain rfl := eq_of_heq hf
  obtain ⟨⟨h1, hfo⟩, h2, h3⟩ := hlg B f (TwDat.untw B (P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex)) hO
    ⟨hH₁, by rw [untw_set_eq]; exact hH₂⟩ (Finset.Subset.refl _) (fun w v hv => absurd hv (Finset.notMem_empty _))
  obtain ⟨C, W, V, S, N, G, c, hQ⟩ := h1 hKP hfo rfl
  obtain ⟨B', f', T', -, -, -, -, -, C', W', V', S', N', G', c', -, hTw, hQ'⟩ :=
    h3 hKP rfl C W V S N G c hQ (h2 hKP rfl C W V S N G c hQ) (fun _ => ∅) (fun _ _ _ => ∅) (by simp)
  obtain ⟨Y, hY, k1, k2, k3, k4⟩ := hlay ⟨B', C', W', V', S', N', G'⟩ f' T' c' (h2v _ c'.real.vol)
  have hTw' : DQ.TwAllAt (Stages.toD7 ⟨B', C', W', V', S', N', G'⟩) Y.nch Y.xd := by
    have e1 : Y.nch = c'.O.nch := by rw [← hY]; rfl
    have e2 : Y.xd = c'.O.xd := by rw [← hY]; rfl
    rw [e1, e2]
    exact hTw
  exact ⟨_, Y, k1, k2, k3, hTw'.twAt, ⟨_, f', T', c', hQ', by rw [hY]⟩, k4, hTw', c'.mtStable⟩

end GlobalTheory.Mem.Top.GroupRetwisting
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharEqOneInertPrimeOffLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.R3.LiftInertChi


open GlobalTheory.FinZeta.LevelOff in
theorem redFn_eq_one_of_locAt {D : D7} {V : HSp D} (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (x : Bridge.Gf V)
    (hS : Formalism.UG.bc (swapAE D) (x : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) ∈ Formalism.L2.DIV.St β)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hx : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V v x) (PP : Formalism.L2.DIV.Pl D.host.E)
    (hPP : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ v) :
    Formalism.L2.DIV.redFn β PP (Formalism.UG.bc (swapAE D) (x : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))) = 1 := by
  classical
  set M : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    (x : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)).val with hM
  set Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)) := {(_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)} with hSb
  set b : FiniteAdeleRing (𝓞 D.host.F) D.host.F := 1 - GlobalTheory.AdeleIdem.ind Sb with hbdef
  have hb : b ∈ Formalism.UG.intAd D.host.F := sub_mem (one_mem _) (GlobalTheory.AdeleIdem.ind_mem Sb)
  have hz : ∀ (i j : Fin V.rank), ∀ w ∈ Sb, Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F w)
      (AlgHom.id D.host.F D.host.E) ((M - 1) i j) = 0 := by
    intro i j w hw
    rw [Finset.mem_singleton] at hw
    subst hw
    have h1 := congrFun (congrFun (hx ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) hPP) i) j
    rw [Matrix.map_apply] at h1
    rw [Matrix.sub_apply, map_sub, h1, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  refine GlobalTheory.LevSplit.redFn_eq_one β PP _ hS ⟨_, GlobalTheory.AdeleIdem.one_tmul_mem hb⟩ ?_ ?_
  · refine GlobalTheory.AdeleIdem.resS_eq_zero PP ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) rfl hb ?_
    simp [hbdef, GlobalTheory.AdeleIdem.ind_apply, hSb]
  · ext i j
    have h2 := one_sub_ind_tmul_mul Sb _ (hz i j)
    have e1 : ((Formalism.UG.bc (swapAE D) (x : GL (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))).val - 1) i j =
        swapAE D ((M - 1) i j) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, RingHom.map_sub]
      congr 1
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs
      · exact (RingHom.map_one _).symm
      · exact (RingHom.map_zero _).symm
    rw [Matrix.smul_apply, smul_eq_mul, e1]
    show swapAE D (b ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = _
    rw [← RingHom.map_mul, h2]

theorem locAt_of_isLocElt {D : D7} (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (x : Bridge.Gf V)
    (h : Formalism.IndefR.Links.IsLocElt V P x) : GlobalTheory.IndefiniteRowSideFullHecke.HeckeIntertwinersInert.LocAt V (P.under (𝓞 D.host.F)) x := by
  obtain ⟨e, f, g, hpi, hg, hx, hs⟩ := h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨-, ε, hε, rfl⟩ := GlobalTheory.IdemSupport.of_isPrimeIdem hΦ hpi
  have h1 := (GlobalTheory.HeckeRowsCompare.suppF_iff V hε hg).1 hs
  rw [GlobalTheory.HeckeRowsCompare.mem_locGrp] at h1
  have h2 : GlobalTheory.HeckeRowsCompare.fin V g = x := Subtype.ext hx.symm
  rw [h2] at h1
  exact (GlobalTheory.HeckeRowsCompare.locAt_iff V _ x).2 h1

theorem levChi_eq_one_of_isLocElt : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cV : ∀ i, CoefA (Vc X.toD7 i)) (i : Fin X.toD7.R.m) (t : TupU I U) (q : ↑((famR X I hX U Xg tr).okI t) × List ℕ) (j : (LiftBrg.envL X I hX U Xg tr L cV i t).lev.J),
    IsLocElt (Vc X.toD7 i) (q.1.1 : PlI X.B px).1 (j : Bridge.Gf (Vc X.toD7 i)) → (LiftBrg.envL X I hX U Xg tr L cV i t).lev.χ j = 1 := by
  intro X px I hX U Xg tr L eG hI hV hL hG cV i t q j hj
  set Q0 : Formalism.L2.DIV.Pl X.toD7.host.E := (q.1.1 : PlI X.B px).1 with hQ0
  have e : (LiftBrg.envL X I hX U Xg tr L cV i t).lev.χ j = Formalism.L2.DIV.levFn (L.βV i) (flag1L (L.datVt i t))
      (Formalism.UG.bc (swapAE X.toD7) (j : Bridge.Gf (Vc X.toD7 i)).1) := rfl
  have hm : Formalism.UG.bc (swapAE X.toD7) (j : Bridge.Gf (Vc X.toD7 i)).1 ∈
      Formalism.L2.DIV.lev X.toD7.sp.cm (Vc X.toD7 i).gram (L.βV i) (flag1L (L.datVt i t)) := j.2
  have hSt := Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hm)
  have hloc := locAt_of_isLocElt (Vc X.toD7 i) _ _ hj

  have hoff : Q0 ∉ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    have h := q.1.2
    exact fun hm => h (Or.inr hm)
  have hconj : Formalism.DivisionValues.conjPl Q0 = Q0 := by
    rw [← GlobalTheory.PlaceDict.conjP_eq_conjPl X.toD7]
    exact (q.1.1 : PlI X.B px).2.1
  have hunder : ∀ PP : Formalism.L2.DIV.Pl X.toD7.host.E, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 →
      PP.under (𝓞 X.toD7.host.F) ≠ Q0.under (𝓞 X.toD7.host.F) := by
    intro PP hPP hu
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq hu with h | h
    · exact hoff (h ▸ hPP)
    · exact hoff ((h.trans hconj) ▸ hPP)
  have hred : ∀ PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1,
      Formalism.L2.DIV.redFn (L.βV i) PP (Formalism.UG.bc (swapAE X.toD7) (j : Bridge.Gf (Vc X.toD7 i)).1) = 1 :=
    fun PP hPP => redFn_eq_one_of_locAt _ _ hSt _ hloc PP (hunder PP hPP)
  have hPg : ∀ PP ∈ (flag1L (L.datVt i t)).Pg, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L (L.datVt i t)).Pg = L.Pg from rfl, hL.Pg] at hPP
    classical
    exact Finset.mem_union.2 (Or.inl hPP)
  have hQ : ∀ PP ∈ (flag1L (L.datVt i t)).Q, PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := by
    intro PP hPP
    rw [show (flag1L (L.datVt i t)).Q = L.Q t from rfl, hL.Q t] at hPP
    have e4 : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel t.1 := by
      simp only [ColIn.Q, tup_ixOf]
    rw [e4] at hPP
    classical
    exact Finset.mem_union.2 (Or.inr hPP)
  have hr1 : Formalism.L2.DIV.rTup (L.βV i) (flag1L (L.datVt i t)) (Formalism.UG.bc (swapAE X.toD7) (j : Bridge.Gf (Vc X.toD7 i)).1) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn _ PP.1 _) = 1
    rw [hred PP.1 (hPg PP.1 PP.2)]
    exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  rw [e]
  unfold Formalism.L2.DIV.levFn
  rw [hr1, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · intro PP hPP
    rw [hred PP (hQ PP hPP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hPP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [hred PP (hPg PP hPP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]

end GlobalTheory.Mem.R3.LiftInertChi
end

