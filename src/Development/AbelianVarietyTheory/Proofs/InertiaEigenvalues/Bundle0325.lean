module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.DiagonalQuotientEigen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0308
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTatePairingLatticeDual
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.BlochKatoDuality.Br

namespace GlobalTheory.TatePair

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]
    {A A' : GRep G Qp LL O} {LA : Lattice (O := O) A.ρ} {LA' : Lattice (O := O) A'.ρ}
    {P : A.V →ₗ[LL] A'.V →ₗ[LL] LL} (hd : IsDualLat1 PD LA LA' P)
    (L1 : Lattice (O := O) (charRep (cycLL PD LL))) (hL1 : L1.T = OL O LL)

theorem cup_coboundary_right (hopen : IsOpen (Set.range (algebraMap O LL))) (c : ↥(divisibleCocycles LA'))
    (d : ↥(latticeCocycles LA)) (hc : (c : G → A'.V ⧸ LA'.T) ∈ BD LA') :
    cupModuloIntegers PD hd L1 hL1 c d ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤ := by
  obtain ⟨w, hw⟩ := hc
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hcg : ∀ h, (c : G → A'.V ⧸ LA'.T) h =
      repD LA' h (Submodule.Quotient.mk v) - Submodule.Quotient.mk v := fun h =>
    (congrFun hw h).symm
  have hT : IsOpen (L1.T : Set LL) := integers_isOpen PD L1 hL1 hopen
  have hcont : Continuous fun g : G => P ((d : G → A.V) g) (A'.ρ g v) :=
    (IsModuleTopology.continuous_bilinear_of_finite_left P).comp
      (d.2.1.1.prodMk (A'.cont v))
  have hlc : IsLocallyConstant fun g : G =>
      -(Submodule.Quotient.mk (P ((d : G → A.V) g) (A'.ρ g v)) : LL ⧸ L1.T) :=
    (locConst_mk L1.T hT _ hcont).neg
  refine ⟨fun g => -torsionPairing PD hd L1 hL1 (repD LA' g (Submodule.Quotient.mk v)) (evT LA g d),
    ⟨hlc, fun _ => Submodule.mem_top⟩, ?_⟩
  funext x
  obtain ⟨g, h⟩ := x
  show repD L1 g (-torsionPairing PD hd L1 hL1 (repD LA' h (Submodule.Quotient.mk v)) (evT LA h d))
      - -torsionPairing PD hd L1 hL1 (repD LA' (g * h) (Submodule.Quotient.mk v)) (evT LA (g * h) d)
      + -torsionPairing PD hd L1 hL1 (repD LA' g (Submodule.Quotient.mk v)) (evT LA g d) =
    cupModuloIntegers PD hd L1 hL1 c d (g, h)
  rw [cup_apply_alt]
  simp only [hcg, map_neg, ← torsionPairing_equivariant, lattice_cocycle_mul, map_mul, Module.End.mul_apply, map_add (f := _),
    map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  abel

end Gen

theorem integral_pairing : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type)
    [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O →
    ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)),
    L1.T = LinearMap.range (Algebra.linearMap O LL) →
    ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ)
      (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m →
    ∃ β : ↥(latticeCocycles LA) →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ L1.T),
      (∀ d c, β d c = 0 ↔ CobO (P.PD K) L1 (cupLD LA' m d.1 c.1)) ∧
      (∀ d c, d.1 ∈ latticeCoboundaries LA → β d c = 0) ∧ ∀ d c, c.1 ∈ BD LA' → β d c = 0 := by
  intro hT l _ P K LL _ _ _ O _ _ hG L1 hL1 A A' LA LA' m hd
  obtain ⟨e⟩ := GlobalTheory.T.tate_H2_period_datum hT l P K LL O hG L1 hL1
  obtain ⟨⟨hO, hDVR, hFr⟩, -, -, htr, hopen⟩ := hG
  haveI := hO
  haveI := hDVR
  haveI := hFr
  haveI := htr
  obtain ⟨pr, hpr⟩ := exists_pr (P.PD K) hopen hd L1 hL1
  refine ⟨(pr.compr₂ e.toLinearMap).flip ∘ₗ Submodule.mkQ _, ?_, ?_, ?_⟩
  · intro d c
    show e (pr c (Submodule.Quotient.mk d)) = 0 ↔ _
    rw [LinearEquiv.map_eq_zero_iff]
    exact hpr c d
  · intro d c hdB
    show e (pr c (Submodule.Quotient.mk d)) = 0
    rw [LinearEquiv.map_eq_zero_iff, hpr c d]
    unfold CobO
    rw [← cup_eq_pairing (P.PD K) hd L1 hL1 c d]
    exact cup_mem_coboundaries (P.PD K) hd L1 hL1 c d hdB
  · intro d c hc
    show e (pr c (Submodule.Quotient.mk d)) = 0
    rw [LinearEquiv.map_eq_zero_iff, hpr c d]
    unfold CobO
    rw [← cup_eq_pairing (P.PD K) hd L1 hL1 c d]
    exact cup_coboundary_right (P.PD K) hd L1 hL1 hopen c d hc

end GlobalTheory.TatePair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.Per.CrisDR

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mem_Dcris_iff (d : V ⊗[Qp] B) : d ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g d = d := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem mem_DdR_iff (d : V ⊗[Qp] BdR) : d ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g d = d := by
  simp [DdR, Submodule.mem_iInf, sub_eq_zero]

theorem act_mul_ι (g : G) (c : K) (d : V ⊗[Qp] B) :
    actVdR PD ρ g (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (ιV PD (LL := LL) (V := V) d)) =
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (ιV PD (LL := LL) (V := V) (actVB PD ρ g d)) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [actVdR, mulVdR, ιV, actVB, PD.ι_comm]

theorem mul_ι_mem (c : K) {d : V ⊗[Qp] B} (hd : d ∈ Dcris PD ρ) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (ιV PD (LL := LL) (V := V) d) ∈ DdR PD ρ := by
  rw [mem_DdR_iff]
  intro g
  rw [act_mul_ι, (mem_Dcris_iff PD ρ d).1 hd g]

theorem coord_mul_ι {I : Type} [DecidableEq I] (b : Basis I Qp V) (j : I) (c : K) (d : V ⊗[Qp] B) :
    equivFinsuppOfBasisLeft b
      (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (ιV PD (LL := LL) (V := V) d)) j =
      algebraMap K BdR c * PD.ι (equivFinsuppOfBasisLeft b d j) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), Finsupp.add_apply, ha, hb, mul_add]
  | tmul v y =>
    have h : ∀ q : Qp, PD.ι (q • y) = q • PD.ι y := fun q =>
      (PD.ι.toLinearMap.restrictScalars Qp).map_smul q y
    simp [mulVdR, ιV, h]

theorem eq_zero_of_sum {m : ℕ} (x : Fin m → K)
    (hx : ∀ b : Fin m → B, ∑ i, algebraMap K BdR (x i) * PD.ι (b i) = 0 → ∀ i, b i = 0)
    (d : Fin m → V ⊗[Qp] B)
    (h : ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (x i) (ιV PD (LL := LL) (V := V) (d i)) = 0)
    (i : Fin m) : d i = 0 := by
  classical
  let b := Basis.ofVectorSpace Qp V
  apply (equivFinsuppOfBasisLeft (N := B) b).injective
  ext j
  rw [map_zero, Finsupp.zero_apply]
  refine hx (fun i => equivFinsuppOfBasisLeft b (d i) j) ?_ i
  have := congrArg (fun z => equivFinsuppOfBasisLeft b z j) h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finsupp.finsetSum_apply, coord_mul_ι, map_zero, Finsupp.zero_apply] at this
  exact this

def cmpMap {m : ℕ} (x : Fin m → K) : (Fin m → ↥(Dcris PD ρ)) →ₗ[LL] ↥(DdR PD ρ) :=
  LinearMap.codRestrict (DdR PD ρ)
    (∑ i, (mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (x i)) ∘ₗ (ιV PD (LL := LL) (V := V)) ∘ₗ
      (Dcris PD ρ).subtype ∘ₗ LinearMap.proj i)
    (fun d => by
      rw [LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun i _ => mul_ι_mem PD ρ (x i) (d i).2)

theorem cmpMap_apply {m : ℕ} (x : Fin m → K) (d : Fin m → ↥(Dcris PD ρ)) :
    (cmpMap PD ρ x d : V ⊗[Qp] BdR) =
      ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (x i) (ιV PD (LL := LL) (V := V) (d i)) := by
  simp [cmpMap, LinearMap.sum_apply]

theorem abstract_cmp
    (hT : ∀ (m : ℕ) (x : Fin m → K), LinearIndependent K₀ x →
      ∀ b : Fin m → B, ∑ i, algebraMap K BdR (x i) * PD.ι (b i) = 0 → ∀ i, b i = 0)
    (hfd : FiniteDimensional LL ↥(DdR PD ρ))
    (hle : finrank LL ↥(DdR PD ρ) ≤ finrank Qp K * finrank LL V)
    (hc : IsCrys PD ρ) :
    finrank LL ↥(DdR PD ρ) = finrank Qp K * finrank LL V ∧
      ∀ y ∈ DdR PD ρ, ∃ (m : ℕ) (c : Fin m → K) (d : Fin m → V ⊗[Qp] B), (∀ i, d i ∈ Dcris PD ρ) ∧
        y = ∑ i, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (c i) (ιV PD (LL := LL) (V := V) (d i)) := by
  haveI := PD.finK
  haveI : FiniteDimensional K₀ K := Module.Finite.of_restrictScalars_finite Qp K₀ K
  let x := Module.finBasis K₀ K
  have hinj : Function.Injective (cmpMap PD ρ x) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro d hd
    funext i
    apply Subtype.ext
    refine eq_zero_of_sum PD (LL := LL) x (hT _ x x.linearIndependent) (fun i => (d i : V ⊗[Qp] B)) ?_ i
    rw [← cmpMap_apply, hd]
    rfl
  haveI hfdS : FiniteDimensional LL (Fin (finrank K₀ K) → ↥(Dcris PD ρ)) :=
    FiniteDimensional.of_injective _ hinj
  have hpos : 0 < finrank K₀ K := finrank_pos
  haveI : FiniteDimensional LL ↥(Dcris PD ρ) :=
    Module.Finite.of_surjective
      (LinearMap.proj (R := LL) (φ := fun _ : Fin (finrank K₀ K) => ↥(Dcris PD ρ)) ⟨0, hpos⟩)
      (fun y => ⟨fun _ => y, rfl⟩)
  have hS : finrank LL (Fin (finrank K₀ K) → ↥(Dcris PD ρ)) = finrank Qp K * finrank LL V := by
    rw [finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    unfold IsCrys at hc
    rw [hc, ← finrank_mul_finrank Qp K₀ K]
    ring
  have hge := LinearMap.finrank_le_finrank_of_injective hinj
  have heq : finrank LL ↥(DdR PD ρ) = finrank Qp K * finrank LL V := le_antisymm hle (hS ▸ hge)
  refine ⟨heq, fun y hy => ?_⟩
  have hsurj : Function.Surjective (cmpMap PD ρ x) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hS.trans heq.symm)).1 hinj
  obtain ⟨d, hd⟩ := hsurj ⟨y, hy⟩
  refine ⟨_, x, fun i => d i, fun i => (d i).2, ?_⟩
  rw [← cmpMap_apply, hd]

end Abstract

theorem isDR_of_isCrys : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → IsDR (P.PD K) ρ ∧ ∀ y ∈ DdR (P.PD K) ρ, ∃ (m : ℕ) (c : Fin m → ↥K.1) (d : Fin m → V ⊗[ℚ_[l]] P.R.B), (∀ i, d i ∈ Dcris (P.PD K) ρ) ∧ y = ∑ i, mulVdR (K := ↥K.1) (BdR := P.R.BdR) (V := V) (LL := ↥LL.1) (c i) (ιV (P.PD K) (LL := ↥LL.1) (V := V) (d i)) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ hc
  obtain ⟨hfd, hle⟩ := _root_.GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ
  refine abstract_cmp (P.PD K) ρ (fun m x hx b hb => GlobalTheory.T.injective_tensor_Bcris_to_BdR l P AI T K m x hx b ?_) hfd hle hc
  simpa only [P.PD_ι] using hb

end GlobalTheory.Per.CrisDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInvMultOfIsGenWith
section
noncomputable section

namespace GlobalTheory.SenCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc TensorProduct GlobalTheory.IndefiniteRowSideFullHecke

section Operators

variable {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module A D] [Module O D]
  [IsScalarTower O A D]

variable {π : A} {g : D →ₗ[O] D} {P Q : Submodule O D}

end Operators

section Residue

variable {O : Type} [CommRing O]

end Residue

section Sen

variable {O A D : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup D] [Module A D] [Module O D]
  [IsScalarTower O A D] [IsDomain O] [IsDiscreteValuationRing O]

end Sen

section Wach

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

section RankOne

variable {r : ℕ} (hr : r = 1) (β : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (hβ : ∀ k, (β k : W.DD T) ∈ W.NΔ T)
include hr hβ

end RankOne

end Wach

section Prime

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P)

variable {K LL : FinExt l} (hA : CaseA K LL)

theorem standing_iff {hg : Good K 1 LL} (lam : ↥(OL LL)) :
    Standing P K LL (H.W K 1 LL hg).emb lam ↔ 5 ≤ l ∧ CaseA K LL ∧ Irreducible lam :=
  ⟨fun h => ⟨h.1, h.2.1, h.2.2.2.2.2⟩, fun h => ⟨h.1, h.2.1, by rw [show K0 K = K.1 from inf_eq_left.2 h.2.1.1],
    (H.W K 1 LL hg).emb_bij, (H.W K 1 LL hg).emb_σ, h.2.2⟩⟩

end Prime

end GlobalTheory.SenCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeftExactFunctorRepresentableTorsionModules
section
open CategoryTheory GlobalTheory.SelFun

namespace GlobalTheory.SelFun.Level

variable {Λ : Type} [CommRing Λ] [IsLocalRing Λ]

def IsMin (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) (A : ModuleCat.{0} Λ) (x : F.obj A) : Prop :=
  ∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ φ : A ⟶ B, (F.map φ).hom x = 0 → φ = 0

def LeftEx (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) : Prop :=
  ∀ (B' B B'' : ModuleCat.{0} Λ), Tors Λ B → Tors Λ B'' → ∀ (f : B' ⟶ B) (g : B ⟶ B''), Function.Injective f.hom →
      Function.Exact f.hom g.hom → Function.Injective (F.map f).hom ∧ Function.Exact (F.map f).hom (F.map g).hom

theorem map_map (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) {A B C : ModuleCat.{0} Λ} (f : A ⟶ B) (g : B ⟶ C)
    (x : F.obj A) : (F.map g).hom ((F.map f).hom x) = (F.map (f ≫ g)).hom x := by
  rw [F.map_comp]; rfl

theorem exists_min (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) (hF : LeftEx F) (A : ModuleCat.{0} Λ) [Finite A]
    (hA : Tors Λ A) (x : F.obj A) :
    ∃ (C : ModuleCat.{0} Λ) (f : C ⟶ A) (z : F.obj C), Function.Injective f.hom ∧ (F.map f).hom z = x ∧
      IsMin F C z := by
  classical
  have hex : ∃ m : ℕ, ∃ (C : ModuleCat.{0} Λ) (f : C ⟶ A) (z : F.obj C), Function.Injective f.hom ∧
      (F.map f).hom z = x ∧ Nat.card C = m :=
    ⟨_, A, 𝟙 A, x, Function.injective_id, by rw [F.map_id]; rfl, rfl⟩
  obtain ⟨C, f, z, hf, hz, hm⟩ := Nat.find_spec hex
  refine ⟨C, f, z, hf, hz, fun B hB φ hφ => ?_⟩
  haveI : Finite C := Finite.of_injective _ hf
  have hC : Tors Λ C := fun c => by
    obtain ⟨n, hn⟩ := hA (f.hom c)
    exact ⟨n, fun r hr => hf (by rw [map_smul, hn r hr, map_zero])⟩
  obtain ⟨-, h2⟩ := hF (ModuleCat.of Λ (LinearMap.ker φ.hom)) C B hC hB
    (ModuleCat.ofHom (LinearMap.ker φ.hom).subtype) φ Subtype.val_injective
    (LinearMap.exact_subtype_ker_map φ.hom)
  obtain ⟨w, hw⟩ := (h2 z).1 hφ
  have hle : Nat.find hex ≤ Nat.card (LinearMap.ker φ.hom) :=
    Nat.find_min' hex ⟨ModuleCat.of Λ (LinearMap.ker φ.hom),
      ModuleCat.ofHom (LinearMap.ker φ.hom).subtype ≫ f, w, hf.comp Subtype.val_injective,
      by rw [← map_map, hw, hz], rfl⟩
  rw [← hm] at hle
  have hbij : Function.Bijective (LinearMap.ker φ.hom).subtype :=
    Function.Injective.bijective_of_nat_card_le Subtype.val_injective hle
  ext c
  obtain ⟨k, rfl⟩ := hbij.2 c
  exact k.2

theorem card_le_of_min [IsNoetherianRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
    (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) [F.Additive]
    (hfin : Finite (F.obj (ModuleCat.of Λ (IsLocalRing.ResidueField Λ)))) (n : ℕ) :
    ∃ N : ℕ, ∀ (A : ModuleCat.{0} Λ) (x : F.obj A), Finite A →
      (∀ r ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : A, r • y = 0) → IsMin F A x → Nat.card A ≤ N := by
  set c := Nat.card (F.obj (ModuleCat.of Λ (IsLocalRing.ResidueField Λ))) with hc
  haveI : Finite (Λ ⧸ IsLocalRing.maximalIdeal Λ) := ‹Finite (IsLocalRing.ResidueField Λ)›
  haveI : Finite (Λ ⧸ IsLocalRing.maximalIdeal Λ ^ n) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian _) n
  refine ⟨Nat.card (Fin c → Λ ⧸ IsLocalRing.maximalIdeal Λ ^ n), fun A x hA hn hmin => ?_⟩
  have hk : Tors Λ (IsLocalRing.ResidueField Λ) := fun b => ⟨1, fun r hr => by
    rw [pow_one] at hr
    rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
      (IsLocalRing.residue_eq_zero_iff r).2 hr, zero_mul]⟩
  have hinj : Function.Injective (fun φ : A →ₗ[Λ] IsLocalRing.ResidueField Λ =>
      (F.map (ModuleCat.ofHom φ : A ⟶ ModuleCat.of Λ (IsLocalRing.ResidueField Λ))).hom x) := by
    intro φ ψ h
    have := hmin (ModuleCat.of Λ (IsLocalRing.ResidueField Λ)) hk
      ((ModuleCat.ofHom φ : A ⟶ ModuleCat.of Λ (IsLocalRing.ResidueField Λ)) - ModuleCat.ofHom ψ) (by
        rw [F.map_sub]
        exact sub_eq_zero.2 h)
    have h2 := sub_eq_zero.1 this
    exact congrArg ModuleCat.Hom.hom h2
  have h1 : Nat.card (A →ₗ[Λ] IsLocalRing.ResidueField Λ) ≤ c := Nat.card_le_card_of_injective _ hinj
  have h2 : c ≤ Nat.card (IsLocalRing.ResidueField Λ) ^ c :=
    (Nat.lt_pow_self Finite.one_lt_card).le
  obtain ⟨v, hv⟩ := GlobalTheory.T.exists_generators_of_card_hom_residueField_le Λ A c (h1.trans h2)
  let p : Fin c → (Λ ⧸ IsLocalRing.maximalIdeal Λ ^ n) →ₗ[Λ] A := fun i =>
    (IsLocalRing.maximalIdeal Λ ^ n).liftQ (LinearMap.toSpanSingleton Λ A (v i)) (fun r hr => hn r hr _)
  refine Nat.card_le_card_of_surjective (fun t => ∑ i, p i (t i)) (fun a => ?_)
  have ha : a ∈ Submodule.span Λ (Set.range v) := hv ▸ Submodule.mem_top
  obtain ⟨t, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Λ).1 ha
  exact ⟨fun i => Submodule.Quotient.mk (t i), rfl⟩

theorem level : ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [Finite (IsLocalRing.ResidueField Λ)]
  (F : ModuleCat.{0} Λ ⥤ ModuleCat.{0} Λ) [F.Additive] [F.Linear Λ],
  (∀ (B' B B'' : ModuleCat.{0} Λ), Tors Λ B → Tors Λ B'' → ∀ (f : B' ⟶ B) (g : B ⟶ B''), Function.Injective f.hom →
      Function.Exact f.hom g.hom → Function.Injective (F.map f).hom ∧ Function.Exact (F.map f).hom (F.map g).hom) →
  Finite (F.obj (ModuleCat.of Λ (IsLocalRing.ResidueField Λ))) → ∀ n : ℕ,
  ∃ (M : ModuleCat.{0} Λ) (ξ : F.obj M), Finite M ∧ (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : M, x • y = 0) ∧
    (∀ B : ModuleCat.{0} Λ, Tors Λ B → ∀ φ : M ⟶ B, (F.map φ).hom ξ = 0 → φ = 0) ∧
    ∀ B : ModuleCat.{0} Λ, Finite B → (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : B, x • y = 0) →
      ∀ η : F.obj B, ∃ φ : M ⟶ B, (F.map φ).hom ξ = η := by
  classical
  intro Λ _ _ _ _ F _ _ hF hfin n
  obtain ⟨N, hN⟩ := card_le_of_min F hfin n
  let P : ℕ → Prop := fun m => ∃ (M : ModuleCat.{0} Λ) (ξ : F.obj M), Finite M ∧
    (∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : M, x • y = 0) ∧ IsMin F M ξ ∧ Nat.card M = m
  have h0 : P (Nat.card (ModuleCat.of Λ PUnit)) :=
    ⟨ModuleCat.of Λ PUnit, 0, inferInstanceAs (Finite PUnit), fun _ _ _ => rfl, fun B _ φ _ => by
      ext c
      exact map_zero φ.hom, rfl⟩
  have hle : ∀ m, P m → m ≤ N := by
    rintro m ⟨M, ξ, h1, h2, h3, rfl⟩
    exact hN M ξ h1 h2 h3
  obtain ⟨M, ξ, hM, hMn, hmin, hcard⟩ : P (Nat.findGreatest P N) := Nat.findGreatest_spec (hle _ h0) h0
  refine ⟨M, ξ, hM, hMn, hmin, fun B hB hBn η => ?_⟩
  let A : ModuleCat.{0} Λ := ModuleCat.of Λ (M × B)
  haveI : Finite A := inferInstanceAs (Finite (M × B))
  have hAn : ∀ x ∈ IsLocalRing.maximalIdeal Λ ^ n, ∀ y : A, x • y = 0 := fun r hr y =>
    Prod.ext (hMn r hr y.1) (hBn r hr y.2)
  let i1 : M ⟶ A := ModuleCat.ofHom (LinearMap.inl Λ M B)
  let i2 : B ⟶ A := ModuleCat.ofHom (LinearMap.inr Λ M B)
  let q1 : A ⟶ M := ModuleCat.ofHom (LinearMap.fst Λ M B)
  let q2 : A ⟶ B := ModuleCat.ofHom (LinearMap.snd Λ M B)
  have e11 : i1 ≫ q1 = 𝟙 M := rfl
  have e22 : i2 ≫ q2 = 𝟙 B := rfl
  have e12 : i1 ≫ q2 = 0 := rfl
  have e21 : i2 ≫ q1 = 0 := rfl
  obtain ⟨C, f, z, hf, hz, hC⟩ := exists_min F hF A (fun a => ⟨n, fun r hr => hAn r hr a⟩)
    ((F.map i1).hom ξ + (F.map i2).hom η)
  have hz1 : (F.map (f ≫ q1)).hom z = ξ := by
    rw [← map_map, hz, map_add (f := _), map_map, map_map, e11, e21, F.map_id, F.map_zero]
    exact add_zero _
  have hz2 : (F.map (f ≫ q2)).hom z = η := by
    rw [← map_map, hz, map_add (f := _), map_map, map_map, e12, e22, F.map_id, F.map_zero]
    exact zero_add _
  haveI hCf : Finite C := Finite.of_injective _ hf
  set g := f ≫ q1 with hg
  have hsurj : Function.Surjective g.hom := by
    have := hmin (ModuleCat.of Λ (M ⧸ LinearMap.range g.hom)) (fun b => ⟨n, fun r hr => by
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      rw [← Submodule.Quotient.mk_smul, hMn r hr, Submodule.Quotient.mk_zero]⟩)
      (ModuleCat.ofHom (LinearMap.range g.hom).mkQ) (by
        have e : g ≫ ModuleCat.ofHom (LinearMap.range g.hom).mkQ = 0 := by
          ext c
          exact (Submodule.Quotient.mk_eq_zero _).2 ⟨c, rfl⟩
        rw [← hz1, map_map, e, F.map_zero]
        rfl)
    intro m
    have h3 : (LinearMap.range g.hom).mkQ m = 0 :=
      congrArg (fun φ : M ⟶ ModuleCat.of Λ (M ⧸ LinearMap.range g.hom) => φ.hom m) this
    exact (Submodule.Quotient.mk_eq_zero _).1 h3
  have hPC : P (Nat.card C) := ⟨C, z, hCf, fun r hr y => hf (by rw [map_smul, hAn r hr, map_zero]), hC, rfl⟩
  have hcle : Nat.card C ≤ Nat.card M := hcard ▸ Nat.le_findGreatest (hle _ hPC) hPC
  have hbij : Function.Bijective g.hom := hsurj.bijective_of_nat_card_le hcle
  let e := LinearEquiv.ofBijective g.hom hbij
  refine ⟨(ModuleCat.ofHom e.symm.toLinearMap : M ⟶ C) ≫ f ≫ q2, ?_⟩
  have e3 : g ≫ (ModuleCat.ofHom e.symm.toLinearMap : M ⟶ C) = 𝟙 C := by
    ext c
    exact e.symm_apply_apply c
  rw [← hz1, map_map, ← Category.assoc, e3, Category.id_comp, hz2]

end GlobalTheory.SelFun.Level
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntAddFilClosedInDeRhamPeriodRingStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_add_fil_closed_in_deRhamPeriodRing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (M : ℕ), 1 ≤ M → ∀ v : P.R.BdR, (∀ n : ℕ, ∃ z : ℤ_[l], qB P (z : ℚ_[l]) - v ∈ Lat AI M n) → NearZ P M v := by
  first | exact @GlobalTheory.ExpImage.nearZ_of_forall_Lat | exact GlobalTheory.ExpImage.nearZ_of_forall_Lat | (intros; apply GlobalTheory.ExpImage.nearZ_of_forall_Lat <;> assumption)
end

