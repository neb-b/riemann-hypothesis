module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AutomorphicArithmetic.CyclotomicBounds.PlaceOfLetterInjective
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0039
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0038

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsMemBoxNegMH
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem HTW.WordData.jumps_mem_box {n : ℕ} (W : WordData n) (hsz : ∀ i, 0 ≤ W.sz i) (hT : W.T1) :
    ∀ i, ∀ u ∈ W.J1 i, -(W.Mi i : ℤ) ≤ u ∧ u ≤ W.hi i := by
  intro i u hu
  have h0 := hsz i
  have ht := Int.self_le_toNat (W.sz i + W.S)
  have hT' := hT i u hu
  have hm1 : (W.η : ℤ) ≤ max (W.η : ℤ) ((W.sz i + W.S).toNat : ℤ) := le_max_left _ _
  have hm2 : (((W.sz i + W.S).toNat : ℕ) : ℤ) ≤ max (W.η : ℤ) ((W.sz i + W.S).toNat : ℤ) :=
    le_max_right _ _
  rcases hT' with h | h
  · by_cases hup : W.up i
    · rw [if_pos hup] at h
      simp only [WordData.Mi, WordData.hi, if_pos hup, Nat.cast_max]
      omega
    · rw [if_neg hup] at h
      simp only [WordData.Mi, WordData.hi, if_neg hup, Nat.cast_max]
      omega
  · have h' := abs_le.mp h
    by_cases hup : W.up i
    · simp only [WordData.Mi, WordData.hi, if_pos hup, Nat.cast_max]
      omega
    · simp only [WordData.Mi, WordData.hi, if_neg hup, Nat.cast_max]
      omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeastPowerDepthSpec
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem depth_spec : ∀ {D : D7} (L : SizeData₂ D) (_ : ParameterChoice' D L) (l : ℕ), 11 ≤ l →
    LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ depth L l ∧ 2 * depth L l + 2 ≤ D.host.Lw ∧
      ((l : ℝ) < LevelStarExponents.lA L → 2 ≤ depth L l) := by
  intro D L P l hl
  obtain ⟨j, hj, hjL⟩ := P.Lw_j l hl
  have hne : ({j : ℕ | LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ j} : Set ℕ).Nonempty := ⟨j, hj⟩
  have hmem : LevelStarExponents.lA L ≤ ((l : ℝ) - 1) ^ depth L l := Nat.sInf_mem hne
  have hle : depth L l ≤ j := Nat.sInf_le hj
  refine ⟨hmem, by omega, fun hlt => ?_⟩
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  by_contra hc
  push_neg at hc
  interval_cases h : depth L l
  · simp at hmem
    linarith
  · simp at hmem
    linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LtPrime
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.InertPrimeLarge

theorem lt_prime : ∀ {D : D7} (L : SizeData₂ D) (l : ℕ), l.Prime → l ≠ 2 →
    jacobiSym (-(D.host.d : ℤ)) l ≠ 1 → L.sc.x ^ (L.sc.ez / 5) < l := by
  intro D L l hl h2 hj
  by_contra hlt
  push_neg at hlt
  have hle : l ≤ D.host.splitBound := le_trans (Nat.le_floor hlt) L.split_tie
  exact hj (D.host.split_small l hl h2 hle)

end GlobalTheory.InertPrimeLarge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OrderOfEqMaxTwoOfSignNegImplicit
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory

theorem orderOf_moving (fr : Formalism.HC.Frame) (φ : fr.GG) (h : φ.1.2 = -1) : orderOf φ = Nat.lcm 2 (orderOf φ.2) :=
  UpperTheory.KStar.Words.orderOf_moving φ h

theorem orderOf_moving_stmt : ∀ {fr : Formalism.HC.Frame} (φ : fr.GG), φ.1.2 = -1 → orderOf φ = Nat.lcm 2 (orderOf φ.2) :=
  fun {fr} φ h => orderOf_moving fr φ h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicAlgClFiniteDenseEqAdjoin
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

theorem GlobalTheory.padicAlgCl_finite_dense_eq_adjoin : ∀ (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (c : E →+* PadicAlgCl l) (K : IntermediateField ℚ_[l] (PadicAlgCl l)), (∀ x, c x ∈ K) → FiniteDimensional ℚ_[l] K → (K : Set (PadicAlgCl l)) ⊆ closure (Set.range c) → K = IntermediateField.adjoin ℚ_[l] (Set.range c) := by
  intro l _ E _ _ c K hc hfin hdense
  have hle : IntermediateField.adjoin ℚ_[l] (Set.range c) ≤ K := by
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨x, rfl⟩; exact hc x
  have hKfin : FiniteDimensional ℚ_[l] K.toSubalgebra.toSubmodule := hfin
  have hAfin : FiniteDimensional ℚ_[l]
      (IntermediateField.adjoin ℚ_[l] (Set.range c)).toSubalgebra.toSubmodule :=
    Submodule.finiteDimensional_of_le (S₂ := K.toSubalgebra.toSubmodule) hle
  have hclosed : IsClosed ((IntermediateField.adjoin ℚ_[l] (Set.range c)).toSubalgebra.toSubmodule
      : Set (PadicAlgCl l)) :=
    Submodule.closed_of_finiteDimensional _
  apply le_antisymm _ hle
  intro y hy
  have h1 : closure (Set.range c) ⊆
      ((IntermediateField.adjoin ℚ_[l] (Set.range c)).toSubalgebra.toSubmodule : Set (PadicAlgCl l)) := by
    apply closure_minimal _ hclosed
    rintro _ ⟨x, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩
  exact h1 (hdense hy)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PageWordSEtaM
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_S_eta_m : ∀ {D : D7} (L : SizeData₂ D) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), ((pageWord L j ε τ φ).S : ℝ) ≤ L.Sc ∧ ((pageWord L j ε τ φ).η : ℝ) ≤ L.etaSz + D.R.t + 2 ∧ (pageWord L j ε τ φ).m = D.R.m := by
  intro D L j ε τ φ
  refine ⟨?_, ?_, rfl⟩
  · exact Nat.floor_le L.Sc_pos.le
  · have h := Nat.floor_le L.etaSz_pos.le
    show ((⌊L.etaSz⌋₊ + D.R.t + 2 : ℕ) : ℝ) ≤ _
    push_cast
    linarith

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParUpRecOfTies
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.RowTie

theorem parUpRec_of_ties : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → GlobalTheory.RowCopy.ThetaOne D →
    (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) →
    (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.RepOfLoc D.nd D.naut i) →
    ∀ i, GlobalTheory.RowCopy.ParUpRec D.nd D.naut i := by
  intro D T hθ hpair hbc hsplit hrep i x hx Sig hSig
  have h := GlobalTheory.ParUpRoad.main _ _ _ D.nd D.naut hθ (_root_.GlobalTheory.RowLaws.main _ _ _ D.nd D.naut T).1
    (fun i => splitLift_of_pairLift _ _ _ D.nd D.naut i (hpair i))
    (fun i => _root_.GlobalTheory.PtOfLocSplit.main _ _ _ D.nd D.naut i (hbc i) (hsplit i) (hrep i))
  exact (GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage.thetaTMapsIntoEig_iff_map_le D.nd D.naut).1 h i x Sig hx hSig

end GlobalTheory.RowTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodDataDeRhamAdmissible
section
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits

open TensorProduct Module

noncomputable section

namespace GlobalTheory.CrysSub

section Alg

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]

theorem mem_Dcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  simp [Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem rTensor_act (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (g : G) (x : V ⊗[Qp] B) :
    AlgebraTensorModule.rTensor Qp B f (actVB PD ρ g x) =
      actVB PD σ g (AlgebraTensorModule.rTensor Qp B f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hf]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def Dmap (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) : Dcris PD ρ →ₗ[LL] Dcris PD σ :=
  (AlgebraTensorModule.rTensor Qp B f).restrict (fun x hx => by
    rw [mem_Dcris] at hx ⊢
    intro g
    rw [← rTensor_act PD ρ σ f hf, hx])

theorem coe_Dmap (ρ : Representation LL G V) (σ : Representation LL G W) (f : V →ₗ[LL] W)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (x : Dcris PD ρ) :
    (Dmap PD ρ σ f hf x : W ⊗[Qp] B) = AlgebraTensorModule.rTensor Qp B f x := rfl

theorem rTensor_eq (f : V →ₗ[LL] W) (x : V ⊗[Qp] B) :
    AlgebraTensorModule.rTensor Qp B f x = (f.restrictScalars Qp).rTensor B x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem exact_Dmap (ρ : Representation LL G V) (σ : Representation LL G W)
    (τ : Representation LL G U) (f : V →ₗ[LL] W) (q : W →ₗ[LL] U)
    (hf : ∀ g v, f (ρ g v) = σ g (f v)) (hq : ∀ g v, q (σ g v) = τ g (q v))
    (hi : Function.Injective f) (he : Function.Exact f q) (hs : Function.Surjective q) :
    LinearMap.ker (Dmap PD σ τ q hq) ≤ LinearMap.range (Dmap PD ρ σ f hf) := by
  intro x hx
  have h0 : (q.restrictScalars Qp).rTensor B (x : W ⊗[Qp] B) = 0 := by
    rw [← rTensor_eq, ← coe_Dmap PD σ τ q hq, LinearMap.mem_ker.mp hx]
    rfl
  have hex : Function.Exact ((f.restrictScalars Qp).rTensor B) ((q.restrictScalars Qp).rTensor B) :=
    rTensor_exact B (f := f.restrictScalars Qp) (g := q.restrictScalars Qp) he hs
  have hinj : Function.Injective ((f.restrictScalars Qp).rTensor B) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ hi
  obtain ⟨y, hy⟩ := (hex _).mp h0
  rw [← rTensor_eq] at hy
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  rw [mem_Dcris]
  intro g
  apply hinj
  rw [← rTensor_eq, ← rTensor_eq, rTensor_act PD ρ σ f hf, hy]
  exact (mem_Dcris PD σ _).mp x.2 g

theorem finrank_le_of_ker_le {A₁ A₂ A₃ : Type} [AddCommGroup A₁] [Module LL A₁]
    [AddCommGroup A₂] [Module LL A₂] [AddCommGroup A₃] [Module LL A₃]
    [Module.Finite LL A₁] [Module.Finite LL A₃] (f : A₁ →ₗ[LL] A₂) (q : A₂ →ₗ[LL] A₃)
    (h : LinearMap.ker q ≤ LinearMap.range f) :
    Module.Finite LL A₂ ∧ finrank LL A₂ ≤ finrank LL A₁ + finrank LL A₃ := by
  have hk : Module.Finite LL (LinearMap.ker q) := Submodule.finiteDimensional_of_le h
  have hq : Module.Finite LL (A₂ ⧸ LinearMap.ker q) :=
    Module.Finite.equiv (q.quotKerEquivRange).symm
  have h2 : Module.Finite LL A₂ := Module.Finite.of_submodule_quotient (LinearMap.ker q)
  refine ⟨h2, ?_⟩
  have h3 := q.finrank_range_add_finrank_ker
  have h4 := Submodule.finrank_mono h
  have h5 := f.finrank_range_le
  have h6 := (LinearMap.range q).finrank_le
  omega

def piRep {m : ℕ} (ρ : Fin m → Representation LL G V) : Representation LL G (Fin m → V) where
  toFun g := LinearMap.pi fun a => (ρ a g).comp (LinearMap.proj a)
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem piRep_apply {m : ℕ} (ρ : Fin m → Representation LL G V) (g : G) (v : Fin m → V)
    (a : Fin m) : piRep ρ g v a = ρ a g (v a) := rfl

theorem sum_le_finrank_piRep {m : ℕ} (ρ : Fin m → Representation LL G V)
    [Module.Finite LL (Dcris PD (piRep ρ))] :
    ∑ a, finrank LL (Dcris PD (ρ a)) ≤ finrank LL (Dcris PD (piRep ρ)) := by
  have hp : ∀ a g v, (LinearMap.proj a : (Fin m → V) →ₗ[LL] V) (piRep ρ g v) =
      ρ a g ((LinearMap.proj a : (Fin m → V) →ₗ[LL] V) v) := fun a g v => rfl
  have hs : ∀ a g v, (LinearMap.single LL (fun _ : Fin m => V) a) (ρ a g v) =
      piRep ρ g (LinearMap.single LL (fun _ : Fin m => V) a v) := by
    intro a g v
    funext b
    rw [piRep_apply]
    by_cases h : b = a
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  let F : Dcris PD (piRep ρ) →ₗ[LL] (∀ a, Dcris PD (ρ a)) :=
    LinearMap.pi fun a => Dmap PD _ _ _ (hp a)
  have key : ∀ (a b : Fin m) (x : V ⊗[Qp] B),
      AlgebraTensorModule.rTensor Qp B (LinearMap.proj b : (Fin m → V) →ₗ[LL] V)
        (AlgebraTensorModule.rTensor Qp B (LinearMap.single LL (fun _ : Fin m => V) a) x) =
        if a = b then x else 0 := by
    intro a b x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v c =>
      by_cases h : a = b
      · subst h; simp
      · simp [h, Pi.single_eq_of_ne (Ne.symm h)]
    | add x y hx hy =>
      simp only [map_add (f := _), hx, hy]
      split_ifs <;> simp
  have hF : Function.Surjective F := by
    intro y
    refine ⟨∑ a, Dmap PD _ _ _ (hs a) (y a), ?_⟩
    funext b
    apply Subtype.ext
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, LinearMap.pi_apply, coe_Dmap, Submodule.coe_sum, map_sum, key]
    simp
  have h1 : Module.Finite LL (∀ a, Dcris PD (ρ a)) := Module.Finite.of_surjective F hF
  have h2 : ∀ a, Module.Finite LL (Dcris PD (ρ a)) := fun a =>
    Module.Finite.of_surjective (LinearMap.proj a : (∀ a, Dcris PD (ρ a)) →ₗ[LL] _)
      (LinearMap.proj_surjective a)
  rw [← Module.finrank_pi_fintype]
  exact LinearMap.finrank_le_finrank_of_surjective hF

end Alg

theorem isCrys_of_isSubOfSums : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL], Formalism.MainNotions.LocalSituation.fontCore PD → GoodO (Qp := Qp) LL O → ∀ (A : GRep G Qp LL O) {ι : Type} {k : ℕ} (Ms : ι → (G →* Matrix (Fin k) (Fin k) LL)), (∀ x, Continuous (Ms x)) → IsSubOfSums A.ρ (fun x g => Ms x g) → (∀ x, IsCrys PD (matRep (Ms x))) → IsCrys PD A.ρ := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ O _ _ hF hO A ι k Ms
    hc hsub hcr
  obtain ⟨m, xs, j, hj, hjg⟩ := hsub
  have htr : IsTopologicalRing LL := hO.2.2.2.1
  let σ : Representation LL G (Fin m → Fin k → LL) := piRep fun a => matRep (Ms (xs a))
  have hσ : ∀ g v a, σ g v a = (Ms (xs a) g).mulVec (v a) := by
    intro g v a
    simp [σ, piRep_apply, matRep, Matrix.toLinAlgEquiv'_apply]
  have hjσ : ∀ g v, j (A.ρ g v) = σ g (j v) := by
    intro g v
    rw [hjg]
    funext a
    rw [hσ]
  have hst : ∀ g, LinearMap.range j ≤ (LinearMap.range j).comap (σ g) := by
    rintro g _ ⟨v, rfl⟩
    exact ⟨A.ρ g v, hjσ g v⟩
  have hσc : ∀ v, Continuous fun g => σ g v := by
    intro v
    refine continuous_pi fun a => ?_
    simp only [hσ]
    exact (hc (xs a)).matrix_mulVec continuous_const
  let τ := σ.quotient (LinearMap.range j) hst
  have hτ : ∀ g v, (LinearMap.range j).mkQ (σ g v) = τ g ((LinearMap.range j).mkQ v) :=
    fun g v => rfl
  have : ContinuousSMul LL ((Fin m → Fin k → LL) ⧸ LinearMap.range j) :=
    IsModuleTopology.toContinuousSMul _ _
  let Q : GRep G Qp LL O :=
    { V := (Fin m → Fin k → LL) ⧸ LinearMap.range j
      ρ := τ
      cont := by
        intro x
        obtain ⟨v, rfl⟩ := (LinearMap.range j).mkQ_surjective x
        simp only [← hτ]
        exact continuous_quot_mk.comp (hσc v) }
  obtain ⟨⟨fA, lA⟩, -⟩ := hF LL O hO A
  obtain ⟨⟨fQ, lQ⟩, -⟩ := hF LL O hO Q
  have fQ' : Module.Finite LL (Dcris PD τ) := fQ
  have lQ' : finrank LL (Dcris PD τ) ≤
    finrank Qp K₀ * finrank LL ((Fin m → Fin k → LL) ⧸ LinearMap.range j) := lQ
  obtain ⟨fS, lS⟩ := finrank_le_of_ker_le _ _
    (exact_Dmap PD A.ρ σ τ j (LinearMap.range j).mkQ hjσ hτ hj
      (LinearMap.exact_map_mkQ_range j) (LinearMap.range j).mkQ_surjective)
  have h1 := sum_le_finrank_piRep PD (fun a => matRep (Ms (xs a)))
  have h2 : ∀ a, finrank LL (Dcris PD (matRep (Ms (xs a)))) = finrank Qp K₀ * k := by
    intro a
    have := hcr (xs a)
    rw [IsCrys] at this
    rw [this]
    simp
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  have h3 := (LinearMap.range j).finrank_quotient_add_finrank
  rw [LinearMap.finrank_range_of_inj hj] at h3
  have h4 : finrank LL (Fin m → Fin k → LL) = m * k := by
    simp [Module.finrank_pi_fintype]
  have h5 : m * (finrank Qp K₀ * k) =
      finrank Qp K₀ * finrank LL ((Fin m → Fin k → LL) ⧸ LinearMap.range j) +
        finrank Qp K₀ * finrank LL A.V := by
    rw [← mul_add, h3, h4]; ring
  have h6 : finrank LL (Dcris PD (piRep fun a => matRep (Ms (xs a)))) = finrank LL (Dcris PD σ) := rfl
  rw [IsCrys]
  omega

end GlobalTheory.CrysSub
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RoundedSizeBoundWindow
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem bHat_window : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C →
    L.sc.b - ((D.R.t : ℝ) + 1) / 2 ≤ (bHat L : ℝ) ∧
      (bHat L : ℝ) ≤ L.sc.b - ((D.R.t : ℝ) + 1) / 2 + 1 := by
  intro D L C h
  obtain ⟨hC, _, hw, hwb, -, hb⟩ := h
  obtain ⟨s, hs⟩ := D.R.t_odd
  have heta := L.etaSz_pos
  have hSc := L.Sc_pos
  have hLw : (0 : ℝ) ≤ (D.host.Lw : ℝ) := Nat.cast_nonneg _
  have hts : ((D.R.t : ℝ) + 1) / 2 = (s : ℝ) + 1 := by
    rw [hs]; push_cast; ring
  have hb'pos : 0 < L.sc.b' := by
    have : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  have hfac : (1 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbb' : L.sc.b' ≤ L.sc.b := by nlinarith
  have htb : (D.R.t : ℝ) + 2 ≤ L.sc.b := by
    have : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  have hdiv : (D.R.t + 1) / 2 = s + 1 := by omega
  have hb0 : 0 ≤ L.sc.b := by linarith
  have hc1 := Nat.le_ceil L.sc.b
  have hc2 := Nat.ceil_lt_add_one hb0
  have hle : s + 1 ≤ ⌈L.sc.b⌉₊ := by
    have : ((s + 1 : ℕ) : ℝ) ≤ ⌈L.sc.b⌉₊ := by
      have : (D.R.t : ℝ) = 2 * s + 1 := by rw [hs]; push_cast; ring
      push_cast; nlinarith
    exact_mod_cast this
  have hval : (bHat L : ℝ) = (⌈L.sc.b⌉₊ : ℝ) - ((s : ℝ) + 1) := by
    unfold bHat
    rw [hdiv, Nat.cast_sub hle]
    push_cast; ring
  rw [hval, hts]
  constructor <;> linarith

end GlobalTheory.HTW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaOneGenusOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.Proof.ThetaOneGenusOne

theorem thetaOne_of_ties : ∀ (D : D7), (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) → (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) → (∀ i, GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.RepOfLoc D.nd D.naut i) → GlobalTheory.RowCopy.ThetaOne D := by
  intro D hpos hpair horth hbc hsplit hrep
  exact GlobalTheory.Proof.HoweThetaLiftComponents.eachRowHasThetaLift_of_howe _ _ _ D.nd D.naut hpos
    (fun i => _root_.GlobalTheory.RowTie.howeUp_of_pairLift _ _ _ D.nd D.naut i (hpair i) (hbc i) (hsplit i) (hrep i)) horth

end GlobalTheory.Proof.ThetaOneGenusOne
end

