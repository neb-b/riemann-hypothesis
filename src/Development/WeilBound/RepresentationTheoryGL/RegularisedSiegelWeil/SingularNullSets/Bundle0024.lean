module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1751
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterConductorCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLocalFieldDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LToSA

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixThA
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

namespace PositivityTheory.Rg.Rsw.L.LFixTh

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open PositivityTheory.Rg.Rsw.L

variable {D : D7} {n : ℕ}

theorem mat_mul (g h : G D n) : mat (g * h) = mat g * mat h := by simp [mat]

theorem mat_mul_inv (g : G D n) : mat g * mat g⁻¹ = 1 := by simp [mat]

theorem mat_proj (g : G D n) (v : Pl D) :
    ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v g)).1 : Matrix _ _ _) =
      (mat g).map (cv D v) := rfl

theorem compInf_eq (w : InfinitePlace D.host.F) (x : AE D) :
    compInf D.host.F D.host.E w x = Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]

theorem kOff_inf {S : Finset (Pl D)} {g : G D n} (hg : g ∈ KOff D n S) (w : InfinitePlace D.host.F) (i j : Fin (n + n)) :
    compInf D.host.F D.host.E w (mat g i j) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) i j := by
  have h1 := (mem_levelOff.1 hg).1
  have h2 : (mat g).map (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom = 1 := by
    exact congrArg Units.val (MonoidHom.mem_ker.1 h1)
  have h3 := congrFun (congrFun h2 i) j
  simp only [Matrix.map_apply] at h3
  rw [compInf_eq]
  change _ = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) i j
  rw [show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (mat g i j) = _ from h3]
  by_cases e : i = j
  · subst e; simp
  · simp [Matrix.one_apply_ne e]

theorem kOff_at {S : Finset (Pl D)} {g : G D n} (hg : g ∈ KOff D n S) {v : Pl D} (hv : v ∈ S) (i j : Fin (n + n)) :
    cv D v (mat g i j) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) _) i j := by
  have h := (mem_levelOff.1 hg).2.1 v hv
  have := congrArg (fun x => ((matHom (Fv D.host.F v) D.sp.cm.sig (Jst D n) x).1 : Matrix _ _ _)) h
  simp only [mat_proj, map_one, Units.val_one] at this
  have := congrFun (congrFun this i) j
  simpa using this

theorem kOff_int {S : Finset (Pl D)} {g : G D n} (hg : g ∈ KOff D n S) {v : Pl D} (hv : v ∉ S) (i j : Fin (n + n)) :
    cv D v (mat g i j) ∈ intLoc D.host.F D.host.E v ∧ cv D v (mat g⁻¹ i j) ∈ intLoc D.host.F D.host.E v := by
  have h := (mem_levelOff.1 hg).2.2 v hv
  have hs : ∀ y, y ∈ latLoc D.host.F (stdLattice D.host.E (n + n)) v ↔
      (mat g).map (cv D v) *ᵥ y ∈ latLoc D.host.F (stdLattice D.host.E (n + n)) v := h
  have he : ∀ k : Fin (n + n), (Pi.single k 1 : Fin (n + n) → Fv D.host.F v ⊗[D.host.F] D.host.E) ∈
      latLoc D.host.F (stdLattice D.host.E (n + n)) v := fun k => by
    rw [mem_latLoc_stdLattice]
    intro l
    by_cases e : l = k
    · subst e; simp
    · simp [Pi.single_eq_of_ne e]
  have hM : (mat g).map (cv D v) * (mat g⁻¹).map (cv D v) = 1 := by
    have := (RingHom.mapMatrix (cv D v)).map_mul (mat g) (mat g⁻¹)
    rw [mat_mul_inv, map_one] at this
    exact this.symm
  constructor
  · have := mem_latLoc_stdLattice.1 ((hs _).1 (he j)) i
    simpa [Matrix.mulVec_single_one] using this
  · have h2 : (mat g⁻¹).map (cv D v) *ᵥ Pi.single j 1 ∈ latLoc D.host.F (stdLattice D.host.E (n + n)) v := by
      refine (hs _).2 ?_
      rw [Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]
      exact he j
    have := mem_latLoc_stdLattice.1 h2 i
    simpa [Matrix.mulVec_single_one] using this

end PositivityTheory.Rg.Rsw.L.LFixTh

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LToSB
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.Rsw.L.LToS

variable {D : D7} {a b c r t : ℕ}

theorem adj_smul (e : AE D) (x : Mx D a b) : adj (e • x) = cA D e • adj x := by
  ext i j
  show cA D (e * x j i) = cA D e * cA D (x j i)
  exact map_mul _ _ _

theorem ip_smul {e : AE D} (he : e * e = e ∧ cA D e = e) (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V (e • x) (e • y) = e • ip V x y := by
  simp only [ip, mm, adj_smul, he.2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he.1]

theorem yv_smul {e : AE D} (he : e * e = e ∧ cA D e = e) (V : HSp D) (b₀ : HermE D r)
    (z : Mx D V.rank r × Mx D V.rank t) : yv V b₀ (e • z.1, e • z.2) = e • yv V b₀ z := by
  simp only [yv, ip_smul he, mm, Matrix.mul_smul]

theorem pr_smul {e : AE D} (he : e * e = e ∧ cA D e = e) (b₀ : HermE D r) (x y : Mx D r t) :
    pr b₀ (e • x) (e • y) = e • pr b₀ x y := by
  simp only [pr, adj_smul, he.2, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he.1]

theorem qv_smul {e : AE D} (he : e * e = e ∧ cA D e = e) (V : HSp D) (b₀ : HermE D r)
    (z : Mx D V.rank r × Mx D V.rank t) : qv V b₀ (e • z.1, e • z.2) = e • qv V b₀ z := by
  simp only [qv, yv_smul he, ip_smul he, pr_smul he, smul_sub]

theorem continuous_ip (V : HSp D) : Continuous fun p : Mx D V.rank a × Mx D V.rank b => ip V p.1 p.2 := by
  show Continuous fun p : Mx D V.rank a × Mx D V.rank b => adj p.1 * (gA V * p.2)
  exact (continuous_adj.comp continuous_fst).matrix_mul (continuous_const.matrix_mul continuous_snd)

theorem continuous_yv (V : HSp D) (b₀ : HermE D r) :
    Continuous fun z : Mx D V.rank r × Mx D V.rank t => yv V b₀ z := by
  show Continuous fun z : Mx D V.rank r × Mx D V.rank t => rat b₀.1⁻¹ * ip V z.1 z.2
  exact continuous_const.matrix_mul (continuous_ip V)

theorem isClosed_qv (V : HSp D) (b₀ : HermE D r) :
    IsClosed {z : Mx D V.rank r × Mx D V.rank t | qv V b₀ z = 0} := by
  have hy := continuous_yv (t := t) V b₀
  have h1 : Continuous fun z : Mx D V.rank r × Mx D V.rank t => ip V z.2 z.2 := by
    show Continuous fun z : Mx D V.rank r × Mx D V.rank t => adj z.2 * (gA V * z.2)
    exact (continuous_adj.comp continuous_snd).matrix_mul (continuous_const.matrix_mul continuous_snd)
  have h2 : Continuous fun z : Mx D V.rank r × Mx D V.rank t => pr b₀ (yv V b₀ z) (yv V b₀ z) := by
    show Continuous fun z : Mx D V.rank r × Mx D V.rank t => adj (yv V b₀ z) * ((b₀.1.map (incA D)) * yv V b₀ z)
    exact (continuous_adj.comp hy).matrix_mul (continuous_const.matrix_mul hy)
  have e : {z : Mx D V.rank r × Mx D V.rank t | qv V b₀ z = 0} =
      {z | ip V z.2 z.2 = pr b₀ (yv V b₀ z) (yv V b₀ z)} := Set.ext fun z => sub_eq_zero
  rw [e]
  exact isClosed_eq h1 h2

theorem map_transport {X : Type*} [MeasurableSpace X] {ν : Measure X} {A : Set X} (hA : MeasurableSet A)
    {f φ ψ : X → X} (hf : Measurable f) (hφ : Measurable φ) (hψ : Measurable ψ) (hA' : φ ⁻¹' A = A)
    (hc : ∀ z, ψ (f z) = f (φ z)) {κ : ℝ≥0} (hν : ν.map φ = κ • ν) :
    ((ν.restrict A).map f).map ψ = κ • (ν.restrict A).map f := by
  have h1 : (ν.restrict A).map φ = κ • ν.restrict A := by
    conv_lhs => rw [← hA']
    rw [← Measure.restrict_map hφ hA, hν, Measure.restrict_smul]
  rw [Measure.map_map hψ hf, show ψ ∘ f = f ∘ φ from funext hc, ← Measure.map_map hf hφ, h1, Measure.map_smul]
  exact hf.aemeasurable

end PositivityTheory.Rg.Rsw.L.LToS

end
end

