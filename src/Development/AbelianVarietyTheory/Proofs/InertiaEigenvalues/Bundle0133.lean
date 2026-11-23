module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankMulLeFinrankDdROfSpans
section
noncomputable section

namespace GlobalTheory.DRFil

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module

theorem finrank_le_of_span_subspace {K F M : Type} [Field K] [CommRing F] [Nontrivial F] [Algebra K F]
    [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M] (D : Submodule K M)
    [FiniteDimensional K D] (h : Submodule.span F (D : Set M) = ⊤) :
    finrank F M ≤ finrank K D := by
  classical
  let bD := Module.finBasis K D
  let s : Finset M := Finset.univ.image fun i => ((bD i : D) : M)
  have hs : Submodule.span F (s : Set M) = ⊤ := by
    rw [eq_top_iff, ← h, Submodule.span_le]
    intro x hx
    have hx' := congrArg Subtype.val (bD.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at hx'
    rw [← hx']
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← algebraMap_smul F]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp [s]))
  calc finrank F M = finrank F (⊤ : Submodule F M) := (finrank_top F M).symm
    _ = finrank F (Submodule.span F (s : Set M)) := by rw [hs]
    _ ≤ s.card := finrank_span_finset_le_card s
    _ ≤ (Finset.univ : Finset (Fin (finrank K D))).card := Finset.card_image_le
    _ = finrank K D := by simp

theorem finrank_mul_le_finrank_DdR_of_spans {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B F : Type} [CommRing B] [CommRing F]
    [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp F] [Algebra K₀ F] [Algebra K F]
    [IsScalarTower Qp K F] [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F] (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL] [FiniteDimensional Qp K] [CharZero Qp]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    (ρ : Representation LL G V) (hfin : FiniteDimensional LL ↥(DdR PD ρ)) (hs : Spans PD ρ) :
    Module.finrank Qp K * Module.finrank LL V ≤ Module.finrank LL ↥(DdR PD ρ) := by
  classical
  haveI : Nontrivial F := by
    refine nontrivial_of_ne (PD.ι PD.t) 0 fun h0 => PD.not_mem_filtration_two ?_
    rw [h0]
    exact (PD.Fil 2).zero_mem
  unfold Spans mulR at hs
  set W := DdR PD ρ with hW
  let e : V ⊗[Qp] F ≃ₗ[Qp] F ⊗[Qp] V := TensorProduct.comm Qp V F

  have he : ∀ (b : F) (x : V ⊗[Qp] F),
      e (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp b) x) = b • e x := by
    intro b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v y => simp [e, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]

  have hK : ∀ (c : K) (x : V ⊗[Qp] F), x ∈ W →
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c)) x ∈ W := by
    intro c x hx
    simp only [hW, DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    have hcomm : ∀ y : V ⊗[Qp] F, actVdR PD ρ g
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c)) y) =
        AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft Qp (algebraMap K F c))
          (actVdR PD ρ g y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v z => simp [actVdR]
      | add y y' hy hy' => simp only [map_add (f := _), hy, hy']
    rw [hcomm, hx g]

  let D' : Submodule K (F ⊗[Qp] V) :=
    { carrier := e '' (W : Set (V ⊗[Qp] F))
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, W.add_mem hx hy, map_add e x y⟩
      zero_mem' := ⟨0, W.zero_mem, map_zero e⟩
      smul_mem' := by
        rintro c _ ⟨x, hx, rfl⟩
        refine ⟨_, hK c x hx, ?_⟩
        rw [he, algebraMap_smul] }
  have hspan : Submodule.span F (D' : Set (F ⊗[Qp] V)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨m, b, d, hd, hy⟩ := hs (e.symm y)
    have hy' : y = ∑ i, b i • e (d i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← e.apply_symm_apply y, hy, map_sum]
      simp only [he]
    rw [hy']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (show e (d i) ∈ (D' : Set (F ⊗[Qp] V)) from ⟨d i, hd i, rfl⟩))
  haveI : FiniteDimensional LL W := hfin
  haveI : FiniteDimensional Qp W := Module.Finite.trans LL W
  let φ : W ≃ₗ[Qp] D' :=
    LinearEquiv.ofBijective
      ({ toFun := fun w => ⟨e (w : V ⊗[Qp] F), (w : V ⊗[Qp] F), w.2, rfl⟩
         map_add' := fun x y => Subtype.ext (map_add e (x : V ⊗[Qp] F) y)
         map_smul' := fun a x => Subtype.ext (map_smul e a (x : V ⊗[Qp] F)) } : W →ₗ[Qp] D')
      ⟨fun x y hxy => Subtype.ext (e.injective (congrArg Subtype.val hxy)),
        by rintro ⟨_, w, hw, rfl⟩; exact ⟨⟨w, hw⟩, rfl⟩⟩
  haveI : FiniteDimensional Qp D' := Module.Finite.equiv φ
  haveI : FiniteDimensional K D' := Module.Finite.of_restrictScalars_finite Qp K D'
  have h1 := finrank_le_of_span_subspace D' hspan
  rw [Module.finrank_baseChange] at h1
  have h2 : finrank Qp K * finrank K D' = finrank Qp LL * finrank LL W := by
    rw [Module.finrank_mul_finrank, ← φ.finrank_eq, Module.finrank_mul_finrank]
  have h3 : finrank Qp LL * finrank LL V = finrank Qp V := Module.finrank_mul_finrank _ _ _
  have hpos : 0 < finrank Qp LL := Module.finrank_pos
  have key : finrank Qp LL * (finrank Qp K * finrank LL V) ≤ finrank Qp LL * finrank LL W :=
    calc finrank Qp LL * (finrank Qp K * finrank LL V)
        = finrank Qp K * finrank Qp V := by rw [← h3]; ring
      _ ≤ finrank Qp K * finrank K D' := Nat.mul_le_mul_left _ h1
      _ = finrank Qp LL * finrank LL W := h2
  exact Nat.le_of_mul_le_mul_left key hpos

end GlobalTheory.DRFil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismTensorEquiv
section
noncomputable section

namespace GlobalTheory.FontCmp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

section Tools

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']


variable (LL) in
def mB (b : B) : V ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B :=
  AlgebraTensorModule.map LinearMap.id (LinearMap.mulLeft Qp b)

@[simp] theorem mB_tmul (b b' : B) (v : V) : mB (LL := LL) b (v ⊗ₜ[Qp] b') = v ⊗ₜ[Qp] (b * b') := by
  simp [mB]

theorem mulVB_eq (c : K₀) (x : V ⊗[Qp] B) :
    mulVB (K₀ := K₀) (LL := LL) c x = mB (LL := LL) (algebraMap K₀ B c) x := rfl

theorem mB_mul (b b' : B) (x : V ⊗[Qp] B) : mB (LL := LL) (b * b') x = mB (LL := LL) b (mB (LL := LL) b' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [mul_assoc]
  | add a c ha hc => simp only [map_add (f := _), ha, hc]

theorem mB_add (b b' : B) (x : V ⊗[Qp] B) : mB (LL := LL) (b + b') x = mB (LL := LL) b x + mB (LL := LL) b' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [add_mul, tmul_add]
  | add a c ha hc => simp only [map_add (f := _), ha, hc]; abel

theorem mB_one (x : V ⊗[Qp] B) : mB (LL := LL) (1 : B) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp
  | add a c ha hc => simp only [map_add (f := _), ha, hc]

theorem comm_smulB (b : B) (x : B ⊗[Qp] V) :
    TensorProduct.comm Qp B V (b • x) = mB (LL := LL) b (TensorProduct.comm Qp B V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul b v => simp [TensorProduct.smul_tmul']
  | add a c ha hc => simp only [smul_add, map_add (f := _), ha, hc]

def mK (ρ : Representation LL G V) (c : K₀) : ↥(Dcris PD ρ) →ₗ[LL] ↥(Dcris PD ρ) :=
  (mB (LL := LL) (algebraMap K₀ B c)).restrict (fun x hx => by
    rw [CrystallineSubrepresentation.mem_Dcris] at hx ⊢
    intro g
    rw [← mulVB_eq, CrystallineSubrepresentation.actVB_mulVB, hx])

theorem cmp_ind {ρ : Representation LL G V} (h : Function.Bijective (CrystallineSubrepresentation.comparison PD ρ))
    {P : V ⊗[Qp] B → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hb : ∀ (b : B) (d : ↥(Dcris PD ρ)), P (mB (LL := LL) b d)) (x : V ⊗[Qp] B) : P x := by
  obtain ⟨u, hu⟩ := h.2 ((TensorProduct.comm Qp B V).symm x)
  have : x = TensorProduct.comm Qp B V (CrystallineSubrepresentation.comparison PD ρ u) := by rw [hu]; simp
  subst this
  clear hu
  induction u using TensorProduct.induction_on with
  | zero => simpa using h0
  | tmul b d =>
    rw [CrystallineSubrepresentation.comparison_tmul, comm_smulB (LL := LL)]
    exact hb b ⟨_, d.2⟩
  | add a c ha hc => simpa only [map_add (f := _)] using hadd _ _ ha hc

include PD in
theorem exists_retr : ∃ lam : B →ₗ[K₀] K₀, lam 1 = 1 := by
  have : (1 : B) ≠ 0 := by
    intro h
    apply PD.not_mem_filtration_two
    rw [← mul_one PD.t, h, mul_zero, map_zero]
    exact Submodule.zero_mem _
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero K₀ this
  exact ⟨(f 1)⁻¹ • f, by simp [hf]⟩

theorem prod_mB_left (b : B) (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    CrystallineSubrepresentation.prodB (LL := LL) (mB (LL := LL) b x ⊗ₜ[LL] y) = mB (LL := LL) b (CrystallineSubrepresentation.prodB (x ⊗ₜ[LL] y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add (f := _), add_tmul, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add (f := _), tmul_add, ha, hc]
    | tmul v' c' => simp [CrystallineSubrepresentation.prodB_tmul, mul_assoc]

theorem prod_mB_right (b : B) (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    CrystallineSubrepresentation.prodB (LL := LL) (x ⊗ₜ[LL] mB (LL := LL) b y) = mB (LL := LL) b (CrystallineSubrepresentation.prodB (x ⊗ₜ[LL] y)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add (f := _), add_tmul, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add (f := _), tmul_add, ha, hc]
    | tmul v' c' => simp [CrystallineSubrepresentation.prodB_tmul, mul_left_comm]

theorem act_prod (ρ : Representation LL G V) (ρ' : Representation LL G V') (g : G)
    (x : V ⊗[Qp] B) (y : V' ⊗[Qp] B) :
    actVB PD (ρ.tprod ρ') g (CrystallineSubrepresentation.prodB (LL := LL) (x ⊗ₜ[LL] y)) =
      CrystallineSubrepresentation.prodB (actVB PD ρ g x ⊗ₜ[LL] actVB PD ρ' g y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add (f := _), add_tmul, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add (f := _), tmul_add, ha, hc]
    | tmul v' c' => simp [CrystallineSubrepresentation.prodB_tmul, actVB]

theorem prod_mem {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (x : ↥(Dcris PD ρ)) (y : ↥(Dcris PD ρ')) :
    CrystallineSubrepresentation.prodB (LL := LL) ((x : V ⊗[Qp] B) ⊗ₜ[LL] (y : V' ⊗[Qp] B)) ∈ Dcris PD (ρ.tprod ρ') := by
  rw [CrystallineSubrepresentation.mem_Dcris]
  intro g
  rw [act_prod, (CrystallineSubrepresentation.mem_Dcris PD ρ x).1 x.2, (CrystallineSubrepresentation.mem_Dcris PD ρ' y).1 y.2]

theorem unit_eq : Dcris PD (Representation.trivial LL G LL) =
      LinearMap.range (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL)
        (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap) := by
  obtain ⟨lam, hl⟩ := exists_retr PD
  ext x
  rw [CrystallineSubrepresentation.mem_Dcris]
  constructor
  · intro hx

    let ctr : (LL →ₗ[Qp] Qp) → (LL ⊗[Qp] B →ₗ[Qp] B) := fun f =>
      (TensorProduct.lid Qp B).toLinearMap ∘ₗ LinearMap.rTensor B f
    have hc : ∀ f g y, ctr f (actVB PD (Representation.trivial LL G LL) g y) =
        PD.actB g (ctr f y) := by
      intro f g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a c ha hc => simp only [map_add (f := _), ha, hc]
      | tmul a b =>
        simp only [ctr, actVB]
        simp
        rw [← IsScalarTower.algebraMap_smul K₀ (f a) b, map_smul, IsScalarTower.algebraMap_smul]
    let r : B →ₗ[Qp] K₀ := lam.restrictScalars Qp
    let j : K₀ →ₗ[Qp] B := (IsScalarTower.toAlgHom Qp K₀ B).toLinearMap
    have hr : ∀ f y, ctr f (AlgebraTensorModule.map (LinearMap.id : LL →ₗ[LL] LL) j
        (LinearMap.lTensor LL r y)) = j (r (ctr f y)) := by
      intro f y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a c ha hc => simp only [map_add (f := _), ha, hc]
      | tmul a b => simp [ctr]
    have hsep : ∀ y : LL ⊗[Qp] B, (∀ f, ctr f y = 0) → y = 0 := by
      intro y hy
      classical
      let bs := Module.Free.chooseBasis Qp LL
      apply (TensorProduct.comm Qp LL B).injective
      apply (TensorProduct.equivFinsuppOfBasisRight bs).injective
      ext i
      have : ∀ y : LL ⊗[Qp] B, TensorProduct.equivFinsuppOfBasisRight bs
          (TensorProduct.comm Qp LL B y) i = ctr (bs.coord i) y := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | add a c ha hc => simp only [map_add (f := _), Finsupp.add_apply, ha, hc]
        | tmul a b => simp [ctr]
      simp [this, hy]
    refine ⟨LinearMap.lTensor LL r x, ?_⟩
    rw [← sub_eq_zero]
    apply hsep
    intro f
    rw [map_sub, hr]
    obtain ⟨c, hc'⟩ := PD.invB (ctr f x) (fun g => by rw [← hc, hx])
    rw [← hc', sub_eq_zero]
    change algebraMap K₀ B (lam (algebraMap K₀ B c)) = _
    rw [Algebra.algebraMap_eq_smul_one c, map_smul, hl]
    simp [Algebra.algebraMap_eq_smul_one]
  · rintro ⟨y, rfl⟩ g
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add (f := _), ha, hc]
    | tmul a b => simp [actVB]


theorem mem_DcrisL (ρ : Representation LL G V) (τ : K₀ →ₐ[Qp] LL) (x : V ⊗[Qp] B) :
    x ∈ DcrisL PD ρ τ ↔ x ∈ Dcris PD ρ ∧ ∀ c : K₀, mB (LL := LL) (algebraMap K₀ B c) x = τ c • x := by
  simp [DcrisL, Submodule.mem_iInf, sub_eq_zero, mulVB_eq]

end Tools

variable (LL : Type) [Field LL] [Algebra Qp LL]

end Generic

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l)

end GlobalTheory.FontCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierTransformKProdLocallyConstantCompactSuppo
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.FourKTest

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def betaK (A : Et F E) : LinearMap.BilinForm F (A.K × A.K) :=
  (Algebra.traceForm F A.K).compl₁₂ (LinearMap.fst F A.K A.K) (LinearMap.snd F A.K A.K) +
    (Algebra.traceForm F A.K).compl₁₂ (LinearMap.snd F A.K A.K) (LinearMap.fst F A.K A.K)

theorem betaK_apply (A : Et F E) (x y : A.K × A.K) :
    betaK A x y = Algebra.trace F A.K (x.1 * y.2) + Algebra.trace F A.K (x.2 * y.1) := by
  simp [betaK, Algebra.traceForm_apply]

theorem betaK_isSymm (A : Et F E) : (betaK A).IsSymm :=
  ⟨fun x y => by rw [betaK_apply, betaK_apply, mul_comm x.1, mul_comm x.2, add_comm]⟩

theorem betaK_nondeg (A : Et F E) (h : (Algebra.traceForm F A.K).Nondegenerate) : (betaK A).Nondegenerate := by
  have hl : LinearMap.SeparatingLeft (betaK A) := by
    intro x hx
    have h1 : x.1 = 0 := h.1 x.1 fun z => by
      have := hx (0, z); rw [betaK_apply] at this; simpa [Algebra.traceForm_apply] using this
    have h2 : x.2 = 0 := h.1 x.2 fun z => by
      have := hx (z, 0); rw [betaK_apply] at this; simpa [Algebra.traceForm_apply] using this
    exact Prod.ext h1 h2
  refine ⟨hl, fun y hy => hl y fun x => ?_⟩
  rw [(betaK_isSymm A).eq]; exact hy x

theorem secondCountable [Unram F E] (A : Et F E) : SecondCountableTopology A.K := by
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  let e : A.K ≃ₗ[F] (Fin (Module.finrank F A.K) → F) := (Module.finBasis F A.K).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  exact (Homeomorph.mk e.toEquiv h1 h2).secondCountableTopology

theorem psi_continuous (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) : Continuous ψ := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [Metric.closedBall_mem_nhds x one_pos] with y hy
  have : ψ y = ψ x * ψ (y - x) := by rw [← AddChar.map_add_eq_mul]; congr 1; abel
  rw [this, hψ.1 (y - x) (by rwa [Metric.mem_closedBall, dist_eq_norm] at hy), mul_one]

theorem fourK_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ' : A.K × A.K → ℂ, IsTest φ' → IsTest (A.fourK μK ψ φ') := by
  intro F E _ _ _ _ _ A ψ hψ μK hsd φ' hφ
  haveI := secondCountable A
  haveI : μK.IsAddHaarMeasure := hsd.1
  haveI : (μK.prod μK).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hnd := (_root_.GlobalTheory.JR.EtFacts.main F E A).2.2.1
  have key := (_root_.GlobalTheory.JR.SelfDualUniq.selfDual_exists_unique_isTest F E ψ hψ (A.K × A.K) (betaK A) (betaK_isSymm A) (betaK_nondeg A hnd)).2
    (μK.prod μK) inferInstance φ' hφ
  have hψc := psi_continuous ψ hψ
  have heq : A.fourK μK ψ φ' = fourB (μK.prod μK) (fun x y => ψ (betaK A x y)) φ' := by
    funext p
    simp only [fourB, Et.fourK]
    rw [integral_prod]
    · refine integral_congr_ae (Eventually.of_forall fun b' => ?_)
      refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
      simp only [Et.psiK, betaK_apply, map_add (f := _)]
      congr 1
      rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, mul_comm p.1, mul_comm c' p.1]
      ring
    · apply Continuous.integrable_of_hasCompactSupport
      · exact hφ.1.continuous.mul (hψc.comp (IsModuleTopology.continuous_of_linearMap ((betaK A).flip p)))
      · exact hφ.2.mul_right
  rw [heq]; exact key

end GlobalTheory.FourKTest
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GalExtCContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.InertiaEigenvalues

variable {l : ℕ} [Fact l.Prime]

theorem norm_galAlgCl (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv g x).symm

theorem isometry_galAlgCl (g : GQ l) : Isometry (g : Om l → Om l) :=
  AddMonoidHomClass.isometry_of_norm g (norm_galAlgCl g)

noncomputable def galExtC (g : GQ l) : PadicComplex l ≃+* PadicComplex l :=
  UniformSpace.Completion.mapRingEquiv g.toRingEquiv (isometry_galAlgCl g).continuous
    (isometry_galAlgCl g.symm).continuous

theorem galExtC_coe (g : GQ l) (x : Om l) :
    galExtC g (x : PadicComplex l) = ((g x : Om l) : PadicComplex l) :=
  UniformSpace.Completion.map_coe (isometry_galAlgCl g).uniformContinuous x

theorem galExtC_continuous (g : GQ l) : Continuous (galExtC g) :=
  UniformSpace.Completion.continuous_map

theorem norm_galExtC (g : GQ l) (y : PadicComplex l) : ‖galExtC g y‖ = ‖y‖ := by
  induction y using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (galExtC_continuous g).norm continuous_norm
  | ih x => rw [galExtC_coe, PadicComplex.norm_extends, PadicComplex.norm_extends, norm_galAlgCl]

theorem galExtC_mul (g h : GQ l) : galExtC (g * h) = galExtC g * galExtC h := by
  ext y
  change galExtC (g * h) y = galExtC g (galExtC h y)
  induction y using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (galExtC_continuous _) ((galExtC_continuous g).comp (galExtC_continuous h))
  | ih x => rw [galExtC_coe, galExtC_coe, galExtC_coe, AlgEquiv.mul_apply]

noncomputable def galActC (l : ℕ) [Fact l.Prime] : GQ l →* (PadicComplex l ≃+* PadicComplex l) :=
  MonoidHom.mk' galExtC galExtC_mul

theorem isActC_galActC (l : ℕ) [Fact l.Prime] : IsActC (galActC l) :=
  ⟨galExtC_coe, norm_galExtC⟩

end GlobalTheory.InertiaEigenvalues
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitalIntegralDescendedEqUnitaryStatement
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegral_descended_eq_unitary : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (τ : A.K) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (hx : A.IsIsom x j) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ (lam : F) (ν : Measure (unitary A.L)), ν.IsHaarMeasure → ∀ (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → (∀ g, 0 ≤ α g) → ∀ Z : Set (Matrix (Fin r) (Fin r) E), (∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * Ax.1 * star g.1 ∈ Z → ∫ t, α (g * (A.uHom hx t)⁻¹) ∂ν = 1) → ∀ f₀ : Hn r F E → ℂ, Continuous f₀ → (∀ X, f₀ X ≠ 0 → X.1.1 ∈ Z) → ∀ y : A.L, (letI := M.mU; Integrable (fun g => f₀ (actU g (Ax, j y, lam))) M.μU) → A.orbL ν (A.descFn M Ax j lam α f₀) y = orbU M f₀ (Ax, j y, lam) := by
  first | exact @GlobalTheory.JR.DescOrb.orbL_descFn | exact GlobalTheory.JR.DescOrb.orbL_descFn | (intros; apply GlobalTheory.JR.DescOrb.orbL_descFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitTraceUnramifiedExtensionStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_trace_unramifiedInvolutionFieldExt : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∃ y : K'.O, ∃ a : K.O, IsUnit a ∧ @Algebra.trace K.E K'.E _ _ φ.toAlgebra (algebraMap K'.O K'.E y) = algebraMap K.O K.E a := by
  first | exact @GlobalTheory.UnitLemma.Unr.exists_trace_unit | exact GlobalTheory.UnitLemma.Unr.exists_trace_unit | (intros; apply GlobalTheory.UnitLemma.Unr.exists_trace_unit <;> assumption)
end

