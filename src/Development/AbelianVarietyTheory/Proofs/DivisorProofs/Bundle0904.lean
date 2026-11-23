module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupOperatorDepthMulDisjointColumns
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstCoeffOperatorLinearSubstitutionProof
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv.LinChange

open MvPowerSeries GlobalTheory.FGDepth

section Rules

variable {K : Type} [Field K] {σ : Type}

private theorem mfact_eq_prod_factorial [Fintype σ] (α : σ →₀ ℕ) :
    (mfact α : K) = ∏ x, ((α x).factorial : K) := by
  unfold mfact
  exact Finsupp.prod_fintype _ _ (fun _ => by simp)

theorem mfact_add_single [Fintype σ] [DecidableEq σ] (α : σ →₀ ℕ) (l : σ) :
    (mfact (α + Finsupp.single l 1) : K) = mfact α * ((α l : K) + 1) := by
  rw [mfact_eq_prod_factorial, mfact_eq_prod_factorial, ← Finset.mul_prod_erase _ _ (Finset.mem_univ l),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ l)]
  have hrest : ∏ x ∈ Finset.univ.erase l, (((α + Finsupp.single l 1 : σ →₀ ℕ) x).factorial : K) =
      ∏ x ∈ Finset.univ.erase l, ((α x).factorial : K) := by
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm (Finset.ne_of_mem_erase hx)), add_zero]
  rw [hrest, Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ, Nat.cast_mul]
  push_cast
  ring

theorem derivAt0_add' (P Q : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 (P + Q) g = derivAt0 P g + derivAt0 Q g := by
  classical
  rw [derivAt0_eq_sum_of_subset (P + Q) g MvPolynomial.support_add,
    derivAt0_eq_sum_of_subset P g (Finset.subset_union_left (s₂ := Q.support)),
    derivAt0_eq_sum_of_subset Q g (Finset.subset_union_right (s₁ := P.support)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem derivAt0_smulP (b : K) (P : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 (b • P) g = b * derivAt0 P g := by
  classical
  rw [derivAt0_eq_sum_of_subset (b • P) g MvPolynomial.support_smul, derivAt0, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

theorem derivAt0_smulG (b : K) (P : MvPolynomial σ K) (g : MvPowerSeries σ K) :
    derivAt0 P (b • g) = b * derivAt0 P g := by
  unfold derivAt0
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [MvPowerSeries.coeff_smul]
  ring

theorem derivAt0_sumG {κ : Type} (s : Finset κ) (P : MvPolynomial σ K) (f : κ → MvPowerSeries σ K) :
    derivAt0 P (∑ i ∈ s, f i) = ∑ i ∈ s, derivAt0 P (f i) := by
  unfold derivAt0
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem derivAt0_C' (a : K) (g : MvPowerSeries σ K) :
    derivAt0 (MvPolynomial.C a) g = a * constantCoeff g := by
  rw [MvPolynomial.C_apply, DepthAdd.derivAt0_monomial, DepthAdd.mfact_zero',
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, mul_one]

theorem derivAt0_mul_X [Fintype σ] (P : MvPolynomial σ K) (l : σ) (g : MvPowerSeries σ K) :
    derivAt0 (P * MvPolynomial.X l) g = derivAt0 P (pderiv l g) := by
  classical
  have hP : P * MvPolynomial.X l =
      ∑ α ∈ P.support, MvPolynomial.monomial (α + Finsupp.single l 1) (P.coeff α) := by
    conv_lhs => rw [P.as_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [show (MvPolynomial.X l : MvPolynomial σ K) = MvPolynomial.monomial (Finsupp.single l 1) 1 from rfl,
      MvPolynomial.monomial_mul, mul_one]
  rw [hP, DepthAdd.derivAt0_sum]
  conv_rhs => unfold derivAt0
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [DepthAdd.derivAt0_monomial, MvPowerSeries.coeff_pderiv, mfact_add_single]
  ring

private theorem constantCoeff_subst_of_constantCoeff_zero' {K ι Λ : Type} [Field K] [Finite ι] (A : ι → MvPowerSeries Λ K)
    (hA : ∀ l, constantCoeff (A l) = 0) (Ψ : MvPowerSeries ι K) :
    constantCoeff (subst A Ψ) = constantCoeff Ψ := by
  have hs : HasSubst A := hasSubst_of_constantCoeff_zero hA
  have h := constantCoeff_subst_eq_zero hs hA (f := Ψ - C (constantCoeff Ψ)) (by simp)
  rw [subst_sub hs, subst_C, map_sub, constantCoeff_C, sub_eq_zero] at h
  exact h

private theorem pderiv_sum_smul_X_eq_C {K ι Λ : Type} [Field K] [Fintype Λ] [DecidableEq Λ] (β : Λ → ι → K)
    (lam : Λ) (l : ι) :
    pderiv lam (∑ lam', β lam' l • (X lam' : MvPowerSeries Λ K)) = C (β lam l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single lam]
  · rw [Derivation.map_smul, pderiv_X_self, MvPowerSeries.smul_eq_C_mul, mul_one]
  · intro b _ hb
    rw [Derivation.map_smul, pderiv_X_of_ne hb, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ lam) h

end Rules

end GlobalTheory.IsoTriv.LinChange

namespace GlobalTheory.IsoTriv

open MvPowerSeries GlobalTheory.FGDepth GlobalTheory.IsoTriv.LinChange

theorem linSt_holds : LinSt := by
  unfold LinSt
  intro K _ _ ι Λ _ _ β P
  classical
  have hA0 : ∀ l : ι, constantCoeff (∑ lam, β lam l • (X lam : MvPowerSeries Λ K)) = 0 := by
    intro l
    simp [MvPowerSeries.smul_eq_C_mul]
  induction P using MvPolynomial.induction_on
  · rename_i a
    intro Ψ
    rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, derivAt0_C', derivAt0_C',
      constantCoeff_subst_of_constantCoeff_zero' _ hA0]
  · rename_i p q hp hq
    intro Ψ
    rw [map_add (f := _), derivAt0_add', derivAt0_add', hp, hq]
  · rename_i p lam hp
    intro Ψ
    have hterm : ∀ l : ι, MvPolynomial.aeval
        (fun lam => ∑ l, MvPolynomial.C (β lam l) * (MvPolynomial.X l : MvPolynomial ι K)) p *
          (MvPolynomial.C (β lam l) * MvPolynomial.X l) =
        β lam l • (MvPolynomial.aeval
          (fun lam => ∑ l, MvPolynomial.C (β lam l) * (MvPolynomial.X l : MvPolynomial ι K)) p *
            MvPolynomial.X l) := by
      intro l
      rw [MvPolynomial.smul_eq_C_mul]
      ring
    rw [map_mul]
    simp only [MvPolynomial.aeval_X]
    rw [Finset.mul_sum]
    simp_rw [hterm]
    rw [DepthAdd.derivAt0_sum, derivAt0_mul_X,
      ReciprocityTheory.ChartRestriction.G.TB.ChartChgPfTP.pderiv_subst _ hA0, derivAt0_sumG]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [derivAt0_smulP, derivAt0_mul_X, hp, pderiv_sum_smul_X_eq_C, mul_comm _ (C (β lam l)), ← MvPowerSeries.smul_eq_C_mul,
      derivAt0_smulG]

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUnitaryAdelicComponentAtPlaceExplicit
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

theorem continuous_tensorMap {R R' : Type} [CommRing R] [Algebra ℚ R] [TopologicalSpace R] [IsTopologicalRing R]
    [CommRing R'] [Algebra ℚ R'] [TopologicalSpace R'] [IsTopologicalRing R']
    {C : Type} [Ring C] [Algebra ℚ C] [Module.Finite ℚ C] (f : R →ₐ[ℚ] R') (hf : Continuous f) :
    letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
    letI : TopologicalSpace (R' ⊗[ℚ] C) := moduleTopology R' (R' ⊗[ℚ] C)
    Continuous (Algebra.TensorProduct.map f (AlgHom.id ℚ C)) := by
  letI : TopologicalSpace (R ⊗[ℚ] C) := moduleTopology R (R ⊗[ℚ] C)
  letI : TopologicalSpace (R' ⊗[ℚ] C) := moduleTopology R' (R' ⊗[ℚ] C)
  haveI : IsModuleTopology R (R ⊗[ℚ] C) := ⟨rfl⟩
  haveI : IsModuleTopology R' (R' ⊗[ℚ] C) := ⟨rfl⟩
  haveI : ContinuousAdd (R' ⊗[ℚ] C) := IsModuleTopology.toContinuousAdd R' _
  haveI : ContinuousSMul R' (R' ⊗[ℚ] C) := IsModuleTopology.toContinuousSMul R' _
  let b := Module.finBasis ℚ C
  let bA := Algebra.TensorProduct.basis R b
  let bB := Algebra.TensorProduct.basis R' b
  have key : ∀ x, Algebra.TensorProduct.map f (AlgHom.id ℚ C) x = ∑ i, f (bA.repr x i) • bB i := by
    intro x
    conv_lhs => rw [← bA.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [bA, bB, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have e : (⇑(Algebra.TensorProduct.map f (AlgHom.id ℚ C))) = fun x => ∑ i, f (bA.repr x i) • bB i := funext key
  rw [e]
  refine continuous_finsetSum _ fun i _ => ?_
  exact (hf.comp (IsModuleTopology.continuous_of_linearMap (bA.coord i))).smul continuous_const

theorem continuous_piV : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : AwayP p), Continuous (piV G v) := by
  intro p _ G v
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) _
  letI : TopologicalSpace (Qv v ⊗[ℚ] G.C) := moduleTopology (Qv v) _
  have hf : Continuous (AfP.eval v) := RestrictedProduct.continuous_eval v
  have hφ := continuous_tensorMap (C := G.C) (AfP.eval v) hf
  have h1 := Units.continuous_map (f := (Algebra.TensorProduct.map (AfP.eval v) (AlgHom.id ℚ G.C)).toRingHom.toMonoidHom) hφ
  have h2 := Units.continuous_map (f := (AfP.eval v).toRingHom.toMonoidHom) hf
  refine continuous_induced_rng.2 ?_
  exact (h1.comp (continuous_fst.comp continuous_subtype_val)).prodMk (h2.comp (continuous_snd.comp continuous_subtype_val))

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordL
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.AwayOrb

variable {p : ℕ} [Fact p.Prime]

def compL (G : HTGroup p) (w : AwayP p) : G.GAf →* UPts G.star (w.1.adicCompletion ℚ) :=
  ubcMap (AfP.eval w)

def coordL (G : HTGroup p) (w : AwayP p) (a : w.1.adicCompletion ℚ ⊗[ℚ] G.C) :
    Fin (Module.finrank ℚ G.C) → w.1.adicCompletion ℚ :=
  (Algebra.TensorProduct.basis (w.1.adicCompletion ℚ) (Module.finBasis ℚ G.C)).repr a

def intPts (G : HTGroup p) (w : AwayP p) : Set (UPts G.star (w.1.adicCompletion ℚ)) :=
  {h | (∀ i, coordL G w (((h : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1 :
          (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) i ∈
        w.1.adicCompletionIntegers ℚ) ∧
      (∀ i, coordL G w ((((h : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).1)⁻¹ :
          (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : w.1.adicCompletion ℚ ⊗[ℚ] G.C) i ∈
        w.1.adicCompletionIntegers ℚ) ∧
      (((h : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).2 : (w.1.adicCompletion ℚ)ˣ) :
        w.1.adicCompletion ℚ) ∈ w.1.adicCompletionIntegers ℚ ∧
      ((((h : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ × (w.1.adicCompletion ℚ)ˣ).2)⁻¹ : (w.1.adicCompletion ℚ)ˣ) :
        w.1.adicCompletion ℚ) ∈ w.1.adicCompletionIntegers ℚ}

end GlobalTheory.AwayOrb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinatePolynomialsFormMemKernelDifferential
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

namespace GlobalTheory.FormsLocus

theorem cstT_comp_affπ {Rg : Type} [CommRing Rg] {T : Scheme.{0}} {n : ℕ}
    (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) (r : Rg) :
    cstT (g ≫ affπ Rg n) r = ringOf g (MvPolynomial.C r) := by
  have n2 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv (MvPolynomial.C r) =
      (affπ Rg n).appTop ((Scheme.ΓSpecIso (CommRingCat.of Rg)).inv r) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]; rfl
  simp only [cstT, ringOf, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [n2]

theorem polys_ker : ∀ (Rg : Type) [CommRing Rg] (A₀ T : Scheme.{0}) (f : A₀ ⟶ Sp Rg) (N : LB A₀) (mA mB : ℕ) (Q : ∀ d : ℕ, GlobalTheory.AbLaw.Perf f (GlobalTheory.AbLaw.pw N (d : ℤ))) (a : Fin mA → LB.Sec N) (g : T ⟶ Sp (MvPolynomial (Fin (mA * mB)) Rg)) (d : ℕ) (F : MvPolynomial (Fin mB) Rg), ((Q d).D₀.map (GlobalTheory.FormsLocus.cstT (g ≫ affπ Rg (mA * mB)))).mulVec (fun k => GlobalTheory.FormsLocus.ringOf g (GlobalTheory.FormsLocus.polys Q a d F k)) = 0 := by
  intro Rg _ A₀ T f N mA mB Q a g d F
  have hC : ((Q d).D₀.map MvPolynomial.C).mulVec (fun k => polys Q a d F k) = 0 := by
    funext l
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, polys, Finset.mul_sum, Pi.zero_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun ν _ => ?_
    have h0 := congrFun (vecOf_ker (Q d) (monSec a d ν)) l
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, RingHom.id_apply, Pi.zero_apply] at h0
    calc ∑ k, MvPolynomial.C ((Q d).D₀ l k) * ((expand mA mB F).coeff ν * MvPolynomial.C (vecOf (Q d) (monSec a d ν) k))
        = (expand mA mB F).coeff ν * MvPolynomial.C (∑ k, (Q d).D₀ l k * vecOf (Q d) (monSec a d ν) k) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul]; ring
      _ = 0 := by rw [h0, map_zero, mul_zero]
  have hm : (Q d).D₀.map (cstT (g ≫ affπ Rg (mA * mB))) = ((Q d).D₀.map MvPolynomial.C).map (ringOf g) := by
    rw [Matrix.map_map]; congr 1; funext r; exact cstT_comp_affπ g r
  rw [hm]
  funext l
  have e := RingHom.map_mulVec (ringOf g) ((Q d).D₀.map MvPolynomial.C) (fun k => polys Q a d F k) l
  rw [hC] at e
  simp only [Pi.zero_apply, map_zero] at e
  exact e.symm

end GlobalTheory.FormsLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeTheoremPicardGroup
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section
namespace GlobalTheory.CubeThm

variable {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B]

theorem comp_psum {T T' : Over S} {n : ℕ} (f : T' ⟶ T) (v : Fin n → (T ⟶ B)) (I : Finset (Fin n)) :
    f ≫ psum B v I = psum B (fun i => f ≫ v i) I := by
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil => simp [pzero]
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ← ih]
    simp only [padd]
    rw [← Category.assoc, comp_lift]

theorem lift_comp_cubeCoordinates (x y z : B ⟶ B) :
    (fun i => lift x (lift y z) ≫ x3 B i) = ![x, y, z] := by
  funext i
  fin_cases i <;> simp [x3]

theorem cube_pic (M : GlobalTheory.UU.CP B) (x y z : B ⟶ B) :
    GlobalTheory.CechPic.pull (x * y * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
                 GlobalTheory.CechPic.pull x.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
                 GlobalTheory.CechPic.pull y.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
                 GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) =
      GlobalTheory.CechPic.pull (x * y).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
        GlobalTheory.CechPic.pull (x * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
        GlobalTheory.CechPic.pull (y * z).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) +
        GlobalTheory.CechPic.pull (1 : B ⟶ B).left (GlobalTheory.CechPic.cls M.L.L M.L.isLB) := by
  set c := GlobalTheory.CechPic.cls M.L.L M.L.isLB
  have hT : (Theta B M.L.L).IsLB := LB.isLB_linComb M.L.isLB _ _
  have h0 : GlobalTheory.CechPic.cls (Theta B M.L.L) hT = 0 :=
    (GlobalTheory.CechPic.cls_eq_zero_iff hT).2 ⟨M.c.t, M.c.isGen⟩
  have h1 : (∑ I : ULift.{0} (Finset (Fin 3)),
      ((-1 : ℤ) ^ (3 - I.down.card)) • GlobalTheory.CechPic.pull (psum B (x3 B) I.down).left c) = 0 :=
    (GlobalTheory.CechPic.cls_linComb M.L.isLB (fun I : ULift.{0} (Finset (Fin 3)) => (psum B (x3 B) I.down).left)
      (fun I => (-1 : ℤ) ^ (3 - I.down.card)) hT).symm.trans h0
  have h2 := congrArg (GlobalTheory.CechPic.pull (lift x (lift y z)).left) h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at h2
  simp only [map_zsmul, ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, comp_psum, lift_comp_cubeCoordinates] at h2
  rw [← Equiv.ulift.symm.sum_comp] at h2
  simp only [Equiv.ulift_symm_down] at h2
  rw [show (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide] at h2
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton] at h2
  have e0 : psum B ![x, y, z] ∅ = 1 := rfl
  have e1 : psum B ![x, y, z] {0} = x := (show _ = x * 1 from rfl).trans (mul_one x)
  have e2 : psum B ![x, y, z] {1} = y := (show _ = y * 1 from rfl).trans (mul_one y)
  have e3 : psum B ![x, y, z] {2} = z := (show _ = z * 1 from rfl).trans (mul_one z)
  have e4 : psum B ![x, y, z] {0, 1} = x * y :=
    (show _ = x * (y * 1) from rfl).trans (congrArg (x * ·) (mul_one y))
  have e5 : psum B ![x, y, z] {0, 2} = x * z :=
    (show _ = x * (z * 1) from rfl).trans (congrArg (x * ·) (mul_one z))
  have e6 : psum B ![x, y, z] {1, 2} = y * z :=
    (show _ = y * (z * 1) from rfl).trans (congrArg (y * ·) (mul_one z))
  have e7 : psum B ![x, y, z] {0, 1, 2} = x * y * z :=
    (show _ = x * (y * (z * 1)) from rfl).trans
      ((congrArg (x * ·) (congrArg (y * ·) (mul_one z))).trans (mul_assoc x y z).symm)
  rw [e0, e1, e2, e3, e4, e5, e6, e7] at h2
  have c0 : (∅ : Finset (Fin 3)).card = 0 := rfl
  have c1 : ({0} : Finset (Fin 3)).card = 1 := rfl
  have c2 : ({1} : Finset (Fin 3)).card = 1 := rfl
  have c3 : ({2} : Finset (Fin 3)).card = 1 := rfl
  have c4 : ({0, 1} : Finset (Fin 3)).card = 2 := rfl
  have c5 : ({0, 2} : Finset (Fin 3)).card = 2 := rfl
  have c6 : ({1, 2} : Finset (Fin 3)).card = 2 := rfl
  have c7 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := rfl
  rw [c0, c1, c2, c3, c4, c5, c6, c7] at h2
  norm_num at h2
  rw [← sub_eq_zero]
  rw [← h2]
  abel

end GlobalTheory.CubeThm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsAgreementContainsFormIndependentFields
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem tieIn_of_nonempty_tie :
    ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) , Nonempty (FWTie T R κ v₀) → TieIn T R κ v₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ ⟨fw⟩ => ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenBoundCombinePadicPrimeToPStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.den_bound_combine_padic_primeToP : ∀ (p D K k : ℕ), p.Prime → ∀ q : ℚ, (∃ m : ℕ, m.Coprime p ∧ ∃ a : ℤ, ((p ^ K * m : ℕ) : ℚ) * q = a) → (∃ a : ℤ, ((D * p ^ k : ℕ) : ℚ) * q = a) → ∃ a : ℤ, ((D * p ^ K : ℕ) : ℚ) * q = a := by
  first | (exact @GlobalTheory.den_comb) | (exact GlobalTheory.den_comb) | (intros; apply GlobalTheory.den_comb  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyRationalUnitary
section
open scoped TensorProduct Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RatUDiscrete

theorem discreteTopology_ratU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), DiscreteTopology (ratU σ J) := by
  intro F E _ _ _ _ _ σ n J
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := F) (E := E)
  obtain ⟨U, hU, h⟩ := GlobalTheory.RationalDiscrete.exists_nhds_zero_inclR (F := F) (E := E)
  refine discreteTopology_of_isOpen_singleton_one ?_
  let f : ratU σ J → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
    fun g => ((g.1.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1
  have hf : Continuous f :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).sub
      continuous_const
  have hf1 : f 1 = 0 := sub_self _
  rw [isOpen_singleton_iff_nhds_eq_pure]
  refine le_antisymm (fun s hs => Filter.mem_of_superset (x := {1}) ?_ (Set.singleton_subset_iff.2 hs))
    (pure_le_nhds _)
  have hW : (⋂ i, ⋂ j, (fun g => f g i j) ⁻¹' U) ∈ 𝓝 (1 : ratU σ J) :=
    Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j =>
      (hf.matrix_elem i j).continuousAt.preimage_mem_nhds (by
        show U ∈ 𝓝 (f 1 i j)
        rw [hf1]; exact hU)
  refine Filter.mem_of_superset hW fun g hg => ?_
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.1 (Subgroup.mem_subgroupOf.1 g.2)
  have hfg : ∀ i j, f g i j =
      inclR (F := F) (AF F) (((γ : Matrix (Fin n) (Fin n) E) - 1 : Matrix (Fin n) (Fin n) E) i j) := by
    intro i j
    show (((g.1.1 : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) - 1) i j = _
    rw [← hγ, Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.one_apply, Matrix.one_apply,
      apply_ite (inclR (F := F) (AF F)), map_one, map_zero]
    rfl
  have hγ1 : γ = 1 := by
    refine Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => h _ ?_))
    rw [Units.val_one, ← hfg]
    exact Set.mem_iInter.1 (Set.mem_iInter.1 hg i) j
  refine Subtype.ext (Subtype.ext ?_)
  rw [← hγ, hγ1, map_one]
  rfl

end GlobalTheory.RatUDiscrete
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingReducedResidueFieldBijectiveUnramifiedStatement
section
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddingReducedResidueField_bijective_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p), UnramIn E p → Function.Bijective (red io X) := by
  first | exact @GlobalTheory.PrimePart.red_bijective | exact GlobalTheory.PrimePart.red_bijective | (intros; apply GlobalTheory.PrimePart.red_bijective <;> assumption)
end

