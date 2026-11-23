module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0917
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpanTprodOfCommuteAtEachPlace
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0935
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolySubComm
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.Divisibility.RowLatLemmas
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0821
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarRowsLevelCharacterEqLiftsLevelCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.ChiStarLev

variable {D : D7}

section Level

variable {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ V.rank}

theorem levChi_flag' (hs : L.s = 0) (hQ : L.Q = ∅) (κ : GA D V) : levChi V β (flagL L) κ = 1 := by
  have h2 : ext1 (flagL L).P.H (flagL L).P.chi (rTup β (flagL L) (finE V κ)) = 1 := subgroupCharExtension_one_apply _ _
  unfold levChi levFn
  rw [h2]
  simp [flagL, withP, hs, hQ]

theorem levChi_withP' (hs : L.s = 0) (hQ : L.Q = ∅) (P : LevelP L.Pg L.r ℂ) (κ : GA D V) :
    levChi V β (withP L P) κ = ((ext1 P.H P.chi (rTup β L (finE V κ)) : ℂˣ) : ℂ) := by
  have h := levChi_flag' (β := β) hs hQ κ
  unfold levChi at h ⊢
  rw [levFn_withP, Units.val_mul, h, mul_one]

end Level

theorem ext_by_one_apply_of_not_mem_subgroup {G N : Type} [Group G] [One N] [Mul N] {P : Subgroup G} (f : P → N) {x : G} (h : x ∉ P) :
    ext1 P f x = 1 := by
  unfold ext1; rw [dite_eq_right h]

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem star_levChi_levR (R : RealDat D A Ks) (F : Face D A) (b : Bool) (g : GA D (Yc D 0)) :
    star (levChi _ (R.βY 0) (R.dat0 (R.levR F b)) g) = levChi _ (R.βY 0) (R.dat0 (R.levL F b (sg0 D A))) g := by
  have hsg : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  rw [hsg]
  have h1 := levChi_withP' (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (R.levL F b D.what₂.embLL) g
  have h2 := levChi_withP' (β := R.βY 0) (L := R.dat0 R.triv) rfl rfl (R.levR F b) g
  have hH : (R.levL F b D.what₂.embLL).H = (R.levR F b).H := rfl
  by_cases hm : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) g) ∈ (R.levR F b).H
  · replace h2 := h2.trans (congrArg Units.val (extendOne_of_mem (P := (R.levR F b).H) (R.levR F b).chi hm))
    replace h1 := h1.trans (congrArg Units.val (extendOne_of_mem (P := (R.levL F b D.what₂.embLL).H) (R.levL F b D.what₂.embLL).chi hm))
    refine Eq.trans (congrArg star h2) (Eq.trans ?_ h1.symm)
    have h3 : (R.levL F b D.what₂.embLL).chi ⟨_, hm⟩ = ((R.levR F b).chi ⟨_, hm⟩)⁻¹ := by
      exact map_inv (Units.map D.what₂.embLL.toMonoidHom) _
    have h4 : IsOfFinOrder ((R.levR F b).chi ⟨_, hm⟩) := by
      have : Finite (G0 R.Pg D.R.r) := Finite.of_equiv _ R.eG.toEquiv
      exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
    have h5 : ‖(((R.levR F b).chi ⟨_, hm⟩ : ℂˣ) : ℂ)‖ = 1 := ((Units.coeHom ℂ).isOfFinOrder h4).norm_eq_one
    rw [h3, Units.val_inv_eq_inv_val, Complex.inv_eq_conj h5]
    rfl
  · have hm' : rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) g) ∉ (R.levL F b D.what₂.embLL).H := hm
    replace h2 := h2.trans (congrArg Units.val (ext_by_one_apply_of_not_mem_subgroup (P := (R.levR F b).H) (R.levR F b).chi hm))
    replace h1 := h1.trans (congrArg Units.val (ext_by_one_apply_of_not_mem_subgroup (P := (R.levL F b D.what₂.embLL).H) (R.levL F b D.what₂.embLL).chi hm'))
    refine Eq.trans (congrArg star h2) (Eq.trans ?_ h1.symm)
    simp

end GlobalTheory.ChiStarLev
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SylvesterInertiaInvariance
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.SigCong

theorem card_pos_le_of_conj {n : ℕ} (A B X : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hX : Xᴴ * A * X = B) :
    Fintype.card {i : Fin n // 0 < hB.eigenvalues i} ≤ Fintype.card {i : Fin n // 0 < hA.eigenvalues i} := by
  set φ : ({i // 0 < hB.eigenvalues i} → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    Matrix.mulVecLin X ∘ₗ Matrix.mulVecLin (hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) ∘ₗ
      GlobalTheory.SimSign.extZero (fun i => 0 < hB.eigenvalues i) with hφ
  have hq : ∀ w, w ≠ 0 → 0 < (star (φ w) ⬝ᵥ A *ᵥ φ w).re := fun w hw => by
    simp only [hφ, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply]
    rw [GlobalTheory.SimSign.quad_mulVec, hX, GlobalTheory.SimSign.re_quad_ext]
    exact GlobalTheory.SimSign.sum_pos B hB w hw
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have := hq w hne
    rw [hw] at this
    simp at this
  have hS : ∀ u ∈ LinearMap.range φ, u ≠ 0 → 0 < (star u ⬝ᵥ A *ᵥ u).re := by
    rintro u ⟨w, rfl⟩ hu
    exact hq w (fun h0 => hu (by rw [h0, map_zero]))
  have h1 := GlobalTheory.SimSign.finrank_le_pos A hA _ hS
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card] at h1
  exact h1

theorem sigPosH_congr : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 →
    ∀ (Z : GL (Fin n) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) (hB : B.IsHermitian),
      B = (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A * (Z : Matrix (Fin n) (Fin n) ℂ) → sigPosH hB = sigPosH hA := by
  intro n A hA _ Z B hB hBZ
  unfold sigPosH
  refine le_antisymm (card_pos_le_of_conj A B _ hA hB hBZ.symm)
    (card_pos_le_of_conj B A ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) hB hA ?_)
  have h1 : (Z : Matrix (Fin n) (Fin n) ℂ) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = 1 :=
    Units.mul_inv Z
  rw [hBZ]
  calc (((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᴴ * ((Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * A *
        (Z : Matrix (Fin n) (Fin n) ℂ)) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
      = ((Z : Matrix (Fin n) (Fin n) ℂ) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᴴ * A *
        ((Z : Matrix (Fin n) (Fin n) ℂ) * ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = A := by rw [h1]; simp

end GlobalTheory.SigCong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TCAlt
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

namespace GlobalTheory.CentCls

def TC (D : Type) [Ring D] [Algebra ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (R : Type) [CommRing R] [Algebra ℚ R]
    (z : (R ⊗[ℚ] D)ˣ × Rˣ) : Prop :=
  (z.1 : R ⊗[ℚ] D) * ((1 : R) ⊗ₜ β) * (starT σ R (z.1 : R ⊗[ℚ] D)).unop =
      algebraMap R (R ⊗[ℚ] D) (z.2 : R) * ((1 : R) ⊗ₜ β) ∧
    Commute (z.1 : R ⊗[ℚ] D) ((1 : R) ⊗ₜ y)

end GlobalTheory.CentCls
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistLocalToGlobalStrictlyHenselianStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etC_b3 : GlobalTheory.EtC.B3 := by
  first | (exact @GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian) | (exact GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian) | (intros; apply GlobalTheory.EtC.tateTwist_local_to_global_strictlyHenselian  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPlaceActionInjective
section
open scoped TensorProduct

namespace GlobalTheory.FactorKernel

variable {ι : Type} [Fintype ι] [hd : DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def contrML (w₀ : ι) (μ : ι → Module.Dual ℂ V) : (ι → V) →ₘₗ[ℂ] V where
  toFun x := (∏ i ∈ Finset.univ.erase w₀, μ i (x i)) • x w₀
  map_update_add' := by
    intro inst x i a b
    obtain rfl : inst = hd := Subsingleton.elim _ _
    by_cases h : i = w₀
    · subst h
      have e : ∀ c, ∏ k ∈ Finset.univ.erase i, μ k (Function.update x i c k) =
          ∏ k ∈ Finset.univ.erase i, μ k (x k) := fun c =>
        Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_self, smul_add]
    · have hi : i ∈ Finset.univ.erase w₀ := Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩
      have e : ∀ c, ∏ k ∈ Finset.univ.erase w₀, μ k (Function.update x i c k) =
          μ i c * ∏ k ∈ (Finset.univ.erase w₀).erase i, μ k (x k) := fun c => by
        rw [← Finset.mul_prod_erase _ _ hi, Function.update_self]
        congr 1
        exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_of_ne (Ne.symm h), map_add (f := _), add_mul, add_smul]
  map_update_smul' := by
    intro inst x i c a
    obtain rfl : inst = hd := Subsingleton.elim _ _
    simp only [RingHom.id_apply]
    by_cases h : i = w₀
    · subst h
      have e : ∀ c, ∏ k ∈ Finset.univ.erase i, μ k (Function.update x i c k) =
          ∏ k ∈ Finset.univ.erase i, μ k (x k) := fun c =>
        Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_self, smul_comm c]
    · have hi : i ∈ Finset.univ.erase w₀ := Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩
      have e : ∀ c, ∏ k ∈ Finset.univ.erase w₀, μ k (Function.update x i c k) =
          μ i c * ∏ k ∈ (Finset.univ.erase w₀).erase i, μ k (x k) := fun c => by
        rw [← Finset.mul_prod_erase _ _ hi, Function.update_self]
        congr 1
        exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
      simp only [e, Function.update_of_ne (Ne.symm h), map_smul, smul_eq_mul, mul_assoc, smul_smul]

noncomputable def contr (w₀ : ι) (μ : ι → Module.Dual ℂ V) : (⨂[ℂ] _ : ι, V) →ₗ[ℂ] V :=
  PiTensorProduct.lift (contrML w₀ μ)

theorem contr_tprod (w₀ : ι) (μ : ι → Module.Dual ℂ V) (x : ι → V) :
    contr w₀ μ (PiTensorProduct.tprod ℂ x) = (∏ i ∈ Finset.univ.erase w₀, μ i (x i)) • x w₀ := by
  rw [contr, PiTensorProduct.lift.tprod]; rfl

theorem dual_contr (w₀ : ι) (μ : ι → Module.Dual ℂ V) (ν : Module.Dual ℂ V) (T : ⨂[ℂ] _ : ι, V) :
    ν (contr w₀ μ T) =
      PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ (Function.update μ w₀ ν)) T := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, contr_tprod, PiTensorProduct.dualDistrib_apply, map_smul,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ w₀), Function.update_self, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    congr 1
    rw [mul_comm]
    congr 1
    exact Finset.prod_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]

theorem contr_atPl (w₀ : ι) (μ : ι → Module.Dual ℂ V) (L : Module.End ℂ V) (T : ⨂[ℂ] _ : ι, V) :
    contr w₀ μ (GlobalTheory.RealLift.atPl (V := fun _ : ι => V) w₀ L T) = L (contr w₀ μ T) := by
  induction T using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    rw [map_smul, map_smul, map_smul, GlobalTheory.RealLift.atPl, PiTensorProduct.map_tprod, contr_tprod, contr_tprod,
      map_smul, Function.update_self, L.map_smul]
    congr 2
    exact Finset.prod_congr rfl fun k hk => by
      simp [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end GlobalTheory.FactorKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TieInOfFwTie
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Div

theorem tieIn_of_fwTie : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), FWTie T R κ v₀ → TieIn T R κ v₀ :=
  fun _ _ _ _ _ t => ⟨t.laws, t.alg_eq, t.kap, t.hv₀, t.chiR, t.x0⟩

end GlobalTheory.Div
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemDegLE
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.RealLift

namespace GlobalTheory.KFixIrr

variable (ι : Type) [Fintype ι] (P Q R S : ℕ)

def degLE (k : ℕ) : Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) :=
  Submodule.span ℂ {T | ∃ f : ι → Formalism.BasicNotions.TH.Pol P Q R S, ∑ w, (f w).totalDegree ≤ k ∧ T = PiTensorProduct.tprod ℂ f}

def chiPart [DecidableEq ι] (x : ι → ℚ) : Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) :=
  ⨅ w : ι, ⨅ X : {X : Mat P Q // IsKC X},
    LinearMap.ker (atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct1 P Q R S X.1) - ((x w : ℂ) * X.1.trace) • 1)

variable {ι P Q R S}

theorem mem_chiPart [DecidableEq ι] (x : ι → ℚ) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S) :
    T ∈ chiPart ι P Q R S x ↔ ∀ w (X : Mat P Q), IsKC X →
      atPl (V := fun _ : ι => Formalism.BasicNotions.TH.Pol P Q R S) w (fockAct1 P Q R S X) T = ((x w : ℂ) * X.trace) • T := by
  simp only [chiPart, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, sub_eq_zero, Subtype.forall]

theorem degLE_mono : Monotone (degLE ι P Q R S) := fun _ _ h =>
  Submodule.span_mono fun _ ⟨f, hf, e⟩ => ⟨f, hf.trans h, e⟩

theorem tprod_mem_degLE (f : ι → Formalism.BasicNotions.TH.Pol P Q R S) {k : ℕ} (h : ∑ w, (f w).totalDegree ≤ k) :
    PiTensorProduct.tprod ℂ f ∈ degLE ι P Q R S k :=
  Submodule.subset_span ⟨f, h, rfl⟩

end GlobalTheory.KFixIrr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjOfTwistedNormEqGLOneUnramifiedStatement
section
open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_conj_of_twistedNorm_eq_GL_one_unramified : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ δ δ' : GL (Fin 1) (Qr p r), nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ = nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ' → ∃ h : GL (Fin 1) (Qr p r), δ' = h⁻¹ * δ * GlobalTheory.LKLoc.sig p (Q0 p) 1 r h := by
  first | (exact @GlobalTheory.LKMid.exists_sig_twisted_conj_of_nrmG_eq) | (exact GlobalTheory.LKMid.exists_sig_twisted_conj_of_nrmG_eq) | (intros; apply GlobalTheory.LKMid.exists_sig_twisted_conj_of_nrmG_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormConjNormalizeAndDegreeOne
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem nrm_exact : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), (∀ (r : ℕ) (γ : Gp G) (δ z : Gr G r), 0 < r →
    IsNrm G r γ δ z → IsNrm G r γ (z * δ * (sigG G r z)⁻¹) 1) ∧ ∀ γ : Gp G, IsNrm G 1 γ (inclG G 1 γ) 1 := by
  intro p _ G
  refine ⟨fun r γ δ z hr h => ?_, fun γ => ?_⟩
  · unfold IsNrm at h ⊢
    have e := (GlobalTheory.T.twistedNormProductIterate_twistedConj (sigG G r) r δ z⁻¹).1
    have hit := (GlobalTheory.T.hermitianTripleFrobeniusTwist_order_fixed_points p G r hr).1 z⁻¹
    rw [inv_inv] at e
    rw [← map_inv, e, h, hit]
    group
  · unfold IsNrm nrmG
    simp
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix

namespace GlobalTheory.LiftLower

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def csumAt {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) (σ : K →+* ℂ) (f g : S.Forms) : ℂ :=
  star (fun a => σ (S.basis.repr f a)) ⬝ᵥ (S.H.map σ) *ᵥ fun a => σ (S.basis.repr g a)

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

abbrev levSW (i : Fin D.R.m) : Set (GA D (Wc D i)) := levS _ (R.βW i) (R.datWp i R.triv)

abbrev chiW (i : Fin D.R.m) : GA D (Wc D i) → ℂ := Lev.levChi _ (R.βW i) (R.datWp i R.triv)

def partH (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) : Submodule ℂ (R.HW i σ).H :=
  (partFull R.θ (R.MW i σ) (levSW R i) (chiW R i) (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) c).comap (R.HW i σ).e

def IsNormSys (i : Fin D.R.m) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) : Prop :=
  ∀ P d, (¬ ∃ Rp, Hecke₂ (Wc D i) (levSW R i) (chiW R i) (GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R) P d Rp) → c P d = 0

def projH (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : (R.HW i σ).H →ₗ[ℂ] (R.HW i σ).H :=
  ∑ g, RealDat.eC (A := A) σ g • R.gW i σ g


variable (D) in
def hookPlus (i : Fin D.R.m) : ℝ :=
  ∑ ρ : D.what₂.Tau, Real.log (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.hookOf (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D i ρ) (aPl D i (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.pW D i ρ) ρ) : ℝ)

variable {R}

theorem Q_base (h : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro PP hPP
  refine (h.Q_ram A.μ0 PP).2 (Or.inl hPP) ?_
  rw [h.xi_base]
  intro x _
  rfl

theorem typePart_base (h : R.toLevCh.Is A.μ0) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (c : GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.Sys D) :
    GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.typePart R i σ A.μ0 R.triv c = partH R i σ c := by
  classical
  have e : GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.finS R A.μ0 = GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF R := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.finS GlobalTheory.IndefiniteRowSideFullHecke.PolarisedDualSystem.badF
    rw [Q_base h]
    congr 1
    ext; simp
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.typePart partH
  rw [e]

theorem e_projH (h : R.models_gW) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (x : (R.HW i σ).H) :
    (R.HW i σ).e (projH R i σ x) = postOn _ (R.eWf i σ) ((R.HW i σ).e x) := by
  unfold projH RealDat.eWf gaL
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.sum_apply, map_sum]
  ext v g
  simp only [LinearMap.smul_apply, map_smul, h i σ, postOn_apply, LinearMap.sum_apply, MultilinearMap.sum_apply,
    MultilinearMap.smul_apply]
  rfl

end GlobalTheory.LiftLower

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypesSepOfOkIsFam
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.FamSep

theorem typesSep_of_ok_isFam : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {s : ℕ}, A.fam.Ok s → R.IsFam → A.fam.TypesSep :=
  fun {_ _ _ _ _ _ A _ _ _ _} _ _ hOk hF => typesSep_of_ok A hOk fun P => (hF.degR A.μ0 P).1

end GlobalTheory.FamSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointExtOfComponentsStatement
section
open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicPoint_ext_of_components : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (g g' : G.GAf), (∀ v : AwayP p, piV G v g = piV G v g') → g = g' := by
  first | (exact @GlobalTheory.OrbFinAf.ext_of_piV) | (exact GlobalTheory.OrbFinAf.ext_of_piV) | (intros; apply GlobalTheory.OrbFinAf.ext_of_piV  <;> assumption)
end

