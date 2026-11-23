module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeSandwichAinf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0457
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0188
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0320
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DirectSumDeRhamCrystallineJumpsAdd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0439

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemInertiaQlIffResidueTrivial
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.IKRes

theorem norm_gal_ql {l : ℕ} [Fact l.Prime] (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv g x).symm

theorem mem_IK_ql_iff : ∀ (l : ℕ) [Fact l.Prime] (g : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ↔ ∀ x : Om l, ‖x‖ ≤ 1 → ‖(g : GQ l) x - x‖ < 1 := by
  intro l _ g
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem σ hσ => exact hσ
    | one => intro x _; simp
    | mul σ τ _ _ hσ hτ =>
      intro x hx
      have h1 : ‖(σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x‖ < 1 :=
        hσ _ (by rwa [norm_gal_ql])
      have h2 := hτ x hx
      have he : ((σ * τ : Gl l) : GQ l) x - x =
          ((σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x) + ((τ : GQ l) x - x) := by
        rw [Subgroup.coe_mul, AlgEquiv.mul_apply]; abel
      rw [he]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)
    | inv σ _ hσ =>
      intro x hx
      have hy : ‖((σ : GQ l)⁻¹) x‖ ≤ 1 := by rwa [norm_gal_ql]
      have h := hσ _ hy
      have hx' : (σ : GQ l) (((σ : GQ l)⁻¹) x) = x := by
        rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
      rw [hx', norm_sub_rev] at h
      simpa [Subgroup.coe_inv] using h
  · intro h
    exact Subgroup.subset_closure h

end GlobalTheory.IKRes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfFrob
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.FrobDenom

section Abstract

variable {O RA RW M : Type} [CommRing O] [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
  [AddCommGroup M] [Module O M]

theorem repr_incl {κ : Type} (tb : Module.Basis κ O M) (incl : RA →ₐ[O] RW) (u : RA ⊗[O] M) (k : κ) :
    (Algebra.TensorProduct.basis RW tb).repr
        (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M) u) k =
      incl ((Algebra.TensorProduct.basis RA tb).repr u k) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul r t => simp [Algebra.TensorProduct.basis_repr_tmul]
  | add a b ha hb => simp only [map_add (f := _), Finsupp.add_apply, ha, hb]

theorem map_smul_left (f : RW →ₐ[O] RW) (r : RW) (z : RW ⊗[O] M) :
    TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) (r • z) =
      f r • TensorProduct.map f.toLinearMap (LinearMap.id : M →ₗ[O] M) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x t => simp [TensorProduct.smul_tmul']
  | add a b ha hb => rw [smul_add, map_add (f := _), ha, hb, map_add (f := _), smul_add]

theorem mem_range_of_frob {κ : Type} [Fintype κ] (tb : Module.Basis κ O M) (incl : RA →ₐ[O] RW)
    (φ : RW →ₐ[O] RW)
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (S : Matrix p p RA)
      (S' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φ = S.map incl * Z * S'.map incl + Y.map incl → ∀ a b, Z a b ∈ Set.range incl)
    (r : RA) (z w : RW ⊗[O] M)
    (hw : w ∈ LinearMap.range (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M)))
    (h : TensorProduct.map φ.toLinearMap (LinearMap.id : M →ₗ[O] M) z = incl r • z + w) :
    z ∈ LinearMap.range (TensorProduct.map incl.toLinearMap (LinearMap.id : M →ₗ[O] M)) := by
  classical
  obtain ⟨w', rfl⟩ := hw
  set tt := Algebra.TensorProduct.basis RW tb with htt
  set ta := Algebra.TensorProduct.basis RA tb with hta
  have key := hA κ Unit (Matrix.of fun k _ => tt.repr z k) (Matrix.diagonal fun _ => r) 1
    (Matrix.of fun k _ => ta.repr w' k) (by
      ext k u
      have h1 := congrArg (fun x => tt.repr x k) h
      simp only [map_add (f := _), map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h1
      rw [htt, GlobalTheory.Sandwich.repr_phi, repr_incl, ← htt, ← hta] at h1
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.diagonal_map (map_zero _)]
      simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.diagonal_mul]
      exact h1)
  choose c hc using fun k => key k ()
  refine ⟨∑ k, c k ⊗ₜ[O] tb k, ?_⟩
  conv_rhs => rw [← tt.sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hc k
  simp only [Matrix.of_apply] at this
  rw [← this, htt, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul']
  simp

end Abstract

section Alg

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

theorem φ_prod (φ : A →ₐ[O] A) (X Q : A) (hXQ : φ X = X * Q) (m : ℕ) :
    φ (∏ j ∈ Finset.range (m + 1), (φ ^ j) X) =
      (∏ j ∈ Finset.range (m + 1), (φ ^ j) X) * ∏ j ∈ Finset.range (m + 1), (φ ^ j) Q := by
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← AlgHom.mul_apply, ← pow_succ', pow_succ, AlgHom.mul_apply, hXQ, map_mul]

theorem multiset_dvd (f : ℕ → A) (m : ℕ) (J : Multiset ℕ) (hJ : ∀ j ∈ J, j ≤ m) :
    (J.map f).prod ∣ (∏ j ∈ Finset.range (m + 1), f j) ^ Multiset.card J := by
  induction J using Multiset.induction_on with
  | empty => simp
  | cons j J ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, mul_comm]
    refine mul_dvd_mul (ih fun i hi => hJ i (Multiset.mem_cons_of_mem hi)) ?_
    exact Finset.dvd_prod_of_mem f
      (Finset.mem_range.2 (Nat.lt_succ_of_le (hJ j (Multiset.mem_cons_self j J))))

theorem X_dvd (φ : A →ₐ[O] A) (X : A) (m : ℕ) : X ∣ ∏ j ∈ Finset.range (m + 1), (φ ^ j) X := by
  have := Finset.dvd_prod_of_mem (fun j => (φ ^ j) X) (Finset.mem_range.2 (Nat.succ_pos m))
  simpa using this

end Alg

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {W : LocWach PD LL O v n}

theorem jD_smulA (E : EtTie W RA RW inclR φR gR πA) (T : LocLat G Qp LL O) (a : LetA O n)
    (x : W.DD T) : E.jD T (a • x) = inclR (E.io a) • E.jD T x := by
  rw [← algebraMap_smul W.EE a x, E.jD_smul, E.ioE_ext]


set_option maxHeartbeats 1000000 in
theorem of_sand (E : EtTie W RA RW inclR φR gR πA)
    (hφ : ∀ a, inclR (E.io (W.φA a)) = φR (inclR (E.io a)))
    (hA : ∀ (p q : Type) [Fintype p] [Fintype q] (Z : Matrix p q RW) (S : Matrix p p RA)
      (S' : Matrix q q RA) (Y : Matrix p q RA),
      Z.map φR = S.map inclR * Z * S'.map inclR + Y.map inclR → ∀ a b, Z a b ∈ Set.range inclR)
    (T : LocLat G Qp LL O) {κ : Type} [Fintype κ] (tb : Module.Basis κ O ↥T.L.T) (m₀ : ℕ)
    (hm₀ : ∀ x ∈ W.N T, ∃ y : TW RA T, TWincl inclR T y =
      TensorProduct.map (LinearMap.mulLeft O (inclR (E.io W.X) ^ m₀)) LinearMap.id (E.jD T x))
    (J : Multiset ℕ) (y : W.DD T) (hy : (J.map fun j => (W.φA ^ j) W.Q).prod • y ∈ W.N T)
    (b : TW RW T) (hb : TWmap φR T b - b = E.jD T y) (m : ℕ) (hJ : ∀ j ∈ J, j ≤ m) :
    ∃ a : ℕ, TensorProduct.map (LinearMap.mulLeft O
      (inclR (E.io (∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X)) ^ a)) LinearMap.id b ∈
        TAinf inclR T := by
  set Y := ∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X with hY
  set L := ∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.Q with hL
  set Jp := (J.map fun j => (W.φA ^ j) W.Q).prod with hJp
  have hYL : W.φA Y = Y * L := φ_prod W.φA W.X W.Q W.φA_X m
  refine ⟨m₀ + Multiset.card J, ?_⟩
  rw [GlobalTheory.NL.SandArb.map_mulLeft]
  have hdiv : W.X ^ m₀ * Jp ∣ (Y * L) ^ (m₀ + Multiset.card J) := by
    rw [mul_pow, pow_add, pow_add]
    refine (mul_dvd_mul (pow_dvd_pow_of_dvd (X_dvd W.φA W.X m) m₀) (multiset_dvd _ m J hJ)).trans ?_
    exact ⟨Y ^ Multiset.card J * L ^ m₀, by ring⟩
  obtain ⟨R, hR⟩ := hdiv
  set a := m₀ + Multiset.card J with ha
  have hb' : TWmap φR T b = E.jD T y + b := sub_eq_iff_eq_add.mp hb
  have hφc : TensorProduct.map φR.toLinearMap (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T)
      (inclR (E.io Y) ^ a • b) =
      inclR (E.io (L ^ a)) • (inclR (E.io Y) ^ a • b) + inclR (E.io ((Y * L) ^ a)) • E.jD T y := by
    rw [map_smul_left, map_pow, ← hφ, hYL]
    change inclR (E.io (Y * L)) ^ a • TWmap φR T b = _
    rw [hb', smul_add, add_comm, smul_smul, map_pow, map_pow, map_pow, map_pow, map_mul, map_mul,
      mul_pow, mul_comm]
  have hw : inclR (E.io ((Y * L) ^ a)) • E.jD T y ∈
      LinearMap.range (TensorProduct.map inclR.toLinearMap (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T)) := by
    obtain ⟨y', hy'⟩ := hm₀ _ hy
    rw [GlobalTheory.NL.SandArb.map_mulLeft, jD_smulA] at hy'
    rw [hR, map_mul, map_mul, map_mul, map_mul, mul_comm, mul_smul, mul_smul, map_pow, map_pow]
    refine GlobalTheory.Sandwich.incl_smul_mem inclR _ _ ?_
    rw [← hy']
    exact ⟨y', rfl⟩
  have key := mem_range_of_frob tb inclR φR hA (E.io (L ^ a)) _ _ hw hφc
  exact key

end Generic


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (J : Multiset ℕ) (y : W.DD T), (J.map fun j => (W.φA ^ j) W.Q).prod • y ∈ W.N T → ∀ b : TW (RW LL) T, TWmap (φRW LL) T b - b = E.jD T y → ∀ m : ℕ, (∀ j ∈ J, j ≤ m) → ∃ a : ℕ, TensorProduct.map (LinearMap.mulLeft ↥(OL LL) (inclR LL (E.io (∏ j ∈ Finset.range (m + 1), (W.φA ^ j) W.X)) ^ a)) LinearMap.id b ∈ TAinf (inclR LL) T := by
  intro D HW F l _ K s LL h W E T hT J y hy b hb m hJ
  obtain ⟨m₀, hm₀, -⟩ := GlobalTheory.NL.SandArb.sandwich D HW F l K s LL h T hT
  have : Module.Free ↥(OL LL) ↥T.L.T := T.L.free
  have : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  exact of_sand E (GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.1
    (GlobalTheory.FrobIntegralCoeff.frobenius_integrality_coeff l LL) T
    (Module.Free.chooseBasis ↥(OL LL) ↥T.L.T) m₀ hm₀ J y hy b hb m hJ

end GlobalTheory.NL.FrobDenom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemUnramifiedFieldOfMemMaxUnramifiedSupRoot
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.KunrDisj

theorem mem_Kunr_of_mem_Kur_of_mem_sup : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e]
    (ϖ : PiSys l e) (n : ℕ) (x : Om l), x ∈ MaximalUnramifiedExtension l →
    x ∈ Kunr l a ⊔ IntermediateField.adjoin ℚ_[l] {ϖ.seq n} → x ∈ Kunr l a := by
  intro l _ a e _ _ ϖ n x hxK hx
  have hN : 0 < l ^ n * e :=
    Nat.mul_pos (pow_pos (Fact.out : l.Prime).pos n) (Nat.pos_of_ne_zero (NeZero.ne e))
  have hπ : ϖ.seq n ^ (l ^ n * e) = -(l : Om l) := ϖ.seq_pow_mul n
  set U := Kunr l a with hU
  set π := ϖ.seq n with hπdef

  have hdeg := fun (E : Type) [Field E] [Algebra E (Om l)] (h : ∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) =>
    _root_.GlobalTheory.InertiaDeg.natDegree_minpoly_root_neg_l l (l ^ n * e) π hN hπ E h
  have hint : ∀ (E : Type) [Field E] [Algebra E (Om l)], (∀ y : E, algebraMap E (Om l) y ∈ MaximalUnramifiedExtension l) →
      IsIntegral E π := by
    intro E _ _ h
    by_contra hni
    have := hdeg E h
    rw [minpoly.eq_zero hni, Polynomial.natDegree_zero] at this
    omega
  let K2 : IntermediateField U (Om l) := IntermediateField.adjoin U {π}
  have hxK2 : x ∈ K2 := by
    have : x ∈ K2.restrictScalars ℚ_[l] := by
      rw [IntermediateField.restrictScalars_adjoin_eq_sup]; exact hx
    exact this
  let K1 : IntermediateField U (Om l) := IntermediateField.adjoin U {x}
  have hK1K2 : K1 ≤ K2 := IntermediateField.adjoin_simple_le_iff.2 hxK2
  have hUK : ∀ y : U, algebraMap U (Om l) y ∈ MaximalUnramifiedExtension l := fun y => Kunr_le_Kur l a y.2
  have hK1K : ∀ y : K1, algebraMap K1 (Om l) y ∈ MaximalUnramifiedExtension l := by
    intro y
    have hy : (y : Om l) ∈ K1.restrictScalars ℚ_[l] := y.2
    rw [IntermediateField.restrictScalars_adjoin] at hy
    refine (IntermediateField.adjoin_le_iff.2 ?_) hy
    rintro z (hz | hz)
    · exact Kunr_le_Kur l a hz
    · rw [Set.mem_singleton_iff.1 hz]; exact hxK

  let L : IntermediateField K1 (Om l) := IntermediateField.adjoin K1 {π}
  have hLK2 : L.restrictScalars U = K2 := by
    rw [IntermediateField.restrictScalars_adjoin]
    refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ Set.subset_union_right)
    rintro z (hz | hz)
    · exact hK1K2 hz
    · rw [Set.mem_singleton_iff.1 hz]; exact IntermediateField.mem_adjoin_simple_self U π
  have hK2r : Module.finrank U K2 = l ^ n * e := by
    rw [IntermediateField.adjoin.finrank (hint U hUK)]; exact hdeg U hUK
  have hLr : Module.finrank K1 L = l ^ n * e := by
    rw [IntermediateField.adjoin.finrank (hint K1 hK1K)]; exact hdeg K1 hK1K
  have hLU : Module.finrank U L = l ^ n * e := by
    rw [← hK2r, ← hLK2]; rfl
  have htower := Module.finrank_mul_finrank U K1 L
  rw [hLr, hLU] at htower
  have h1 : Module.finrank U K1 = 1 := by
    have := Nat.eq_of_mul_eq_mul_right hN (htower.trans (one_mul _).symm)
    exact this
  have hbot : K1 = ⊥ := IntermediateField.finrank_eq_one_iff.1 h1
  have : x ∈ K1 := IntermediateField.mem_adjoin_simple_self U x
  rw [hbot, IntermediateField.mem_bot] at this
  obtain ⟨y, rfl⟩ := this
  exact y.2

end GlobalTheory.KunrDisj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemZpowersOfTameGen
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.TameCycChoice

theorem zpow_iff {Γ L A F : Type} [Group Γ] [Field L] [CommRing A] [Field F] (e : L →+* F) (j : A →+* F)
    (hj : Function.Injective j) (ψ₀ : Γ →* Lˣ) (ψ : Γ →* Aˣ)
    (h : ∀ g, e ((ψ₀ g : Lˣ) : L) = j ((ψ g : Aˣ) : A)) (σ γ : Γ) (m : ℤ) :
    ψ σ = ψ γ ^ m ↔ ψ₀ σ = ψ₀ γ ^ m := by
  rw [← map_zpow, ← map_zpow, ← Units.val_inj, ← Units.val_inj, ← hj.eq_iff, ← e.injective.eq_iff, h, h]

theorem mem_zpowers_of_tameGen {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (B : ValuationSubring Ω) {Γ : Type} [Group Γ] (ψ : G E Ω →* Γ) (ho : IsOpen (ψ.ker : Set (G E Ω)))
    (hw : ∀ σ : G E Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → ψ σ = 1)
    {γ : G E Ω} (hγ : TameGenAt B γ) (σ : G E Ω) (hσ : σ ∈ Ine (F := E) B) :
    ψ σ ∈ Subgroup.zpowers (ψ γ) := by
  let K : Subgroup (G E Ω) := (Subgroup.zpowers (ψ γ)).comap ψ
  have hK : IsOpen (K : Set (G E Ω)) := Subgroup.isOpen_mono (H₁ := ψ.ker)
    (fun g hg => by rw [Subgroup.mem_comap, (MonoidHom.mem_ker).1 hg]; exact one_mem _) ho
  refine closure_minimal (t := (K : Set (G E Ω))) ?_ (K.isClosed_of_isOpen hK) (hγ.2 hσ)
  refine (Subgroup.closure_le K).2 ?_
  rintro g (rfl | hg)
  · exact Subgroup.mem_zpowers _
  · change ψ g ∈ Subgroup.zpowers _
    rw [hw g hg]; exact one_mem _

theorem tameCyc : ∀ (D : D7) (C : NChoice D), NChTie D C → TameCyc D C := by
  intro D C hT i v hv σ hσ
  obtain ⟨ψ₀, -, hW, hK⟩ := hT.psi_eq
  have hl : v ∉ placesOver D.host.E (D.nd.l i) := D.nd.SQ_l i v (Or.inr hv)
  have hmem := mem_zpowers_of_tameGen (D.nd.plOm.1 v) (D.ntw.psiL i) (D.ntw.psiL_open i)
    (fun g hg => GlobalTheory.WildInertiaChar.trivial_on_wild D.host.E D.nd.Om v (D.nd.plOm.1 v) (D.nd.l i)
      (D.nd.lPrime i).out hl (D.nd.plOm.2 v) _ (D.ntw.psiL i) (D.ntw.psiL_open i) (D.ntw.psiL_ord i) g hg)
    (D.nd.restN_tameGenerator_generates i v (Or.inr hv)) σ hσ
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
  refine ⟨m, ?_⟩
  have h0 := (zpow_iff (D.nd.embK i) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))
    (IsFractionRing.injective _ _) (ψ₀ (D.nd.w i)) (D.ntw.psiL i) (hK i) σ (D.nd.gam0 i v) m).1 hm.symm
  exact (zpow_iff (C.embW (D.nd.w i))
    ((algebraMap (C.Oe (D.nd.w i)) (FractionRing (C.Oe (D.nd.w i)))).comp
      (algebraMap (D.ntw.Ok (C.twI (D.nd.w i)) (C.k' (D.nd.w i))) (C.Oe (D.nd.w i))))
    ((IsFractionRing.injective (C.Oe (D.nd.w i)) (FractionRing (C.Oe (D.nd.w i)))).comp (C.Oe_inj (D.nd.w i)))
    (ψ₀ (D.nd.w i)) (psiG D C (D.nd.w i)) (hW (D.nd.w i)) σ (D.nd.gam0 i v) m).2 h0

end GlobalTheory.TameCycChoice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MinJumpSumLeOfPowMemOfInertiaEqTop
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem min_jumpSum_le_of_pow_mem_of_inertia_eq_top : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ) (B C : Subgroup (L ≃ₐ[F] L)), lowerRamificationGroup F L 0 = ⊤ → OrdIs L p E → (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → (∀ σ : L ≃ₐ[F] L, σ ^ p ∈ C → σ ∈ B) → min (2 * jumpSum (wild F L) ⊤ B) (jumpSum (wild F L) ⊤ B + E) ≤ jumpSum (wild F L) ⊤ C := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E B C h0 hE hcomm hpow
  by_cases hB : B = ⊤
  ·
    subst hB
    have hzero : jumpSum (wild F L) ⊤ (⊤ : Subgroup (L ≃ₐ[F] L)) = 0 := by
      simp [jumpSum]
    simp [hzero]
  ·
    obtain ⟨e, he, hEe, hram⟩ := _root_.GlobalTheory.PMon.Ram.ordIs_of_ordIs_ext F L p E hE
    have hcard : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) = Nat.card (L ≃ₐ[F] L) := by
      rw [hram, h0]; simp
    have hnpos : (0 : ℝ) < (Nat.card (L ≃ₐ[F] L) : ℝ) := by
      exact_mod_cast Nat.card_pos

    obtain ⟨σ, hσ, hσB⟩ := _root_.GlobalTheory.PMon.Ram.exists_mem_upperRamificationGroup_jumpSum_not_mem F L B h0 hB
    have hv : (0 : ℝ) ≤ (jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ) := by
      positivity

    obtain ⟨τ, hτ, hτC⟩ := _root_.GlobalTheory.PMon.Ram.pow_mem_upper_mod_commutator F L p e _ C hcomm hv he σ hσ

    have hτ' : τ ∉ C := by
      intro hτmem
      apply hσB
      apply hpow
      have hsplit : σ ^ p = τ * (τ⁻¹ * σ ^ p) := by group
      rw [hsplit]
      exact C.mul_mem hτmem hτC
    have key := _root_.GlobalTheory.PMon.Ram.card_mul_le_jumpSum_of_mem_upper_not_mem F L C _ h0 τ hτ hτ'
    have hR : ((min (2 * jumpSum (wild F L) ⊤ B) (jumpSum (wild F L) ⊤ B + E) : ℕ) : ℝ)
        ≤ (jumpSum (wild F L) ⊤ C : ℝ) := by
      refine le_trans (le_of_eq ?_) key
      rw [mul_min_of_nonneg _ _ hnpos.le, hEe, hcard]
      push_cast
      congr 1
      · field_simp
      · field_simp
    exact_mod_cast hR

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NegCycPowerBlockCrysDeRhamJumps
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory

noncomputable def negPowBlock {G LL : Type} [Group G] [Field LL] (χ : G →* LLˣ) (t : ℕ) :
    Representation LL G (Fin t → LL) where
  toFun g := LinearMap.pi fun c : Fin t =>
    (((χ g)⁻¹ ^ (c : ℕ) : LLˣ) : LL) • LinearMap.proj c
  map_one' := by ext; simp
  map_mul' g h := by
    refine LinearMap.ext fun v => funext fun c => ?_
    simp only [map_mul, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      Module.End.mul_apply, smul_eq_mul, mul_inv, mul_pow, Units.val_mul]
    ring

noncomputable def snocSplit (LL : Type) [Field LL] (t : ℕ) :
    (Fin (t + 1) → LL) ≃ₗ[LL] ((Fin t → LL) × LL) where
  toFun v := (fun c => v c.castSucc, v (Fin.last t))
  invFun p := Fin.snoc (α := fun _ => LL) p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := Fin.snoc_init_self v
  right_inv p := by
    ext <;> simp

theorem negCycBlock_jumps : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (t : ℕ) (ρ : Representation ↥LL.1 ↥(GK K) (Fin t → ↥LL.1)), (∀ g v (c : Fin t), ρ g v c = (((cycLL (P.PD K) ↥LL.1 g)⁻¹ ^ (c : ℕ) : (↥LL.1)ˣ) : ↥LL.1) * v c) → IsCrys (P.PD K) ρ ∧ IsDR (P.PD K) ρ ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) ρ τ a = if 0 ≤ a ∧ a < (t : ℤ) then 1 else 0 := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro l _ P AI hT K LL t
  induction t with
  | zero =>
    intro ρ _
    refine ⟨?_, ?_, fun τ a => ?_⟩
    · unfold IsCrys
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton (M := Fin 0 → ↥LL.1), mul_zero]
    · unfold IsDR
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton (M := Fin 0 → ↥LL.1), mul_zero]
    · unfold multV
      rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton, if_neg (by omega)]
      simp
  | succ t ih =>
    intro ρ hρ
    obtain ⟨c1, d1, m1⟩ := ih (negPowBlock (cycLL (P.PD K) ↥LL.1) t) (fun _ _ _ => rfl)
    obtain ⟨c2, d2, m2⟩ := _root_.GlobalTheory.CycPow.cyc_zpow_crys_dR_jump l P AI hT K LL (-(t : ℤ))
    obtain ⟨hd, hc, hm⟩ := _root_.GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l P AI hT K LL _ ρ _
      (negPowBlock (cycLL (P.PD K) ↥LL.1) t) _ (charRep (cycLL (P.PD K) ↥LL.1 ^ (-(t : ℤ))))
      (snocSplit ↥LL.1 t) (by
        intro g v
        refine Prod.ext (funext fun c => ?_) ?_
        · exact hρ g v c.castSucc
        · refine (hρ g v (Fin.last t)).trans ?_
          change _ = (((cycLL (P.PD K) ↥LL.1 ^ (-(t : ℤ))) g : (↥LL.1)ˣ) : ↥LL.1) * v (Fin.last t)
          rw [MonoidHom.zpow_apply, Fin.val_last, zpow_neg, zpow_natCast, inv_pow])
    refine ⟨hc.2 ⟨c1, c2⟩, hd.2 ⟨d1, d2⟩, fun τ a => ?_⟩
    rw [hm, m1, m2]
    push_cast
    split_ifs <;> omega

end GlobalTheory
end

