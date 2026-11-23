module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0287
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFinsetSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfMem
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0015
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGradedMapGlueD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0292
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
section
noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.Tf.Loc
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.LocVan

variable {n : ℕ}

theorem locallyCompact_GL (n : ℕ) : LocallyCompactSpace (GL (Fin n) ℂ) := by
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

theorem secondCountable_GL (n : ℕ) : SecondCountableTopology (GL (Fin n) ℂ) := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem isClosed_nilrad (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    IsClosed (nilrad W₁ W₂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  haveI : FiniteDimensional ℂ (Matrix (Fin n) (Fin n) ℂ) := inferInstance
  letI : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedAddCommGroup
  letI : NormedSpace ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.normedSpace
  exact Submodule.closed_of_finiteDimensional (nilrad W₁ W₂)

theorem nil_mul_mem {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂)
    {X Y : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ nilrad W₁ W₂) (hY : Y ∈ nilrad W₁ W₂) :
    X * Y ∈ nilrad W₁ W₂ := by
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
  · rw [← Matrix.mulVec_mulVec]; exact hW (hX.2.1 _ (hY.1 y))
  · rw [← Matrix.mulVec_mulVec, hX.2.2 _ (hY.2.1 y hy)]; exact W₁.zero_mem
  · rw [← Matrix.mulVec_mulVec, hY.2.2 y hy, Matrix.mulVec_zero]

def nmul {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) (Y X : nilrad W₁ W₂) : nilrad W₁ W₂ :=
  ⟨Y.1 + X.1 + Y.1 * X.1, (nilrad W₁ W₂).add_mem ((nilrad W₁ W₂).add_mem Y.2 X.2) (nil_mul_mem hW Y.2 X.2)⟩

theorem isClosed_twCent (d : GL (Fin n) ℂ) :
    IsClosed (twCent (thC n) d : Set (GL (Fin n) ℂ)) := by
  have h : Continuous fun g : GL (Fin n) ℂ => g⁻¹ * d * thC n g :=
    (continuous_inv.mul continuous_const).mul continuous_thC
  exact isClosed_eq h continuous_const

theorem locallyCompact_twCent (d : GL (Fin n) ℂ) : LocallyCompactSpace (twCent (thC n) d) := by
  haveI := locallyCompact_GL n
  exact (isClosed_twCent d).isClosedEmbedding_subtypeVal.locallyCompactSpace

theorem sigmaFinite_twCent [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (d : GL (Fin n) ℂ) (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure] : SigmaFinite μd := by
  haveI := locallyCompact_twCent d
  haveI := secondCountable_GL n
  haveI : SecondCountableTopology (twCent (thC n) d) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  infer_instance

theorem invInvariant_twCent [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (d : GL (Fin n) ℂ) (μd : Measure (twCent (thC n) d)) [μd.IsHaarMeasure]
    (hc : ∀ a ∈ twCent (thC n) d, ∀ b ∈ twCent (thC n) d, a * b = b * a) : μd.IsInvInvariant := by
  haveI := locallyCompact_twCent d
  haveI := secondCountable_GL n
  letI : CommGroup (twCent (thC n) d) :=
    { (inferInstance : Group (twCent (thC n) d)) with
      mul_comm := fun a b => Subtype.ext (hc a a.2 b b.2) }
  haveI : SecondCountableTopology (twCent (thC n) d) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  exact Measure.IsHaarMeasure.isInvInvariant_of_regular μd

end GlobalTheory.CompanionTheory.LocVan
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedComplexCohomology
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.ShiftCoh

variable {K : Type} [Field K]

def ev (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : (Sh ς k C).X n ≃ₗ[K] C.X m where
  toFun y := y ⟨m, h⟩
  invFun x := fun m' => (show m = m'.1 by have := m'.2; omega) ▸ x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv y := by
    funext ⟨m', h'⟩
    obtain rfl : m' = m := by omega
    rfl
  right_inv _ := rfl

theorem ev_apply (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) :
    ev ς k C h y = y ⟨m, h⟩ := rfl

theorem d_apply_succ (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) (h' : m + 1 + k = n + 1) :
    (Sh ς k C).d n y ⟨m + 1, h'⟩ = (ς : ℤ) • C.d m (y ⟨m, h⟩) := rfl

theorem d_apply_zero (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {n : ℕ} (y : (Sh ς k C).X n) (h' : 0 + k = n + 1) :
    (Sh ς k C).d n y ⟨0, h'⟩ = 0 := rfl

theorem unit_smul_eq_zero (ς : ℤˣ) {M : Type*} [AddCommGroup M] {x : M} : (ς : ℤ) • x = 0 ↔ x = 0 := by
  rcases Int.units_eq_one_or ς with rfl | rfl <;> simp

theorem unit_smul_smul (ς : ℤˣ) {M : Type*} [AddCommGroup M] (x : M) : (ς : ℤ) • (ς : ℤ) • x = x := by
  rcases Int.units_eq_one_or ς with rfl | rfl <;> simp

theorem ext_at (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) {y z : (Sh ς k C).X n}
    (e : y ⟨m, h⟩ = z ⟨m, h⟩) : y = z :=
  (ev ς k C h).injective e

theorem mem_Z_iff (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) :
    (Sh ς k C).d n y = 0 ↔ C.d m (y ⟨m, h⟩) = 0 := by
  have h' : m + 1 + k = n + 1 := by omega
  constructor
  · intro e
    have := congrFun e ⟨m + 1, h'⟩
    rw [d_apply_succ ς k C h y h'] at this
    exact (unit_smul_eq_zero ς).1 this
  · intro e
    refine ext_at ς k C h' ?_
    rw [d_apply_succ ς k C h y h', e, smul_zero]
    rfl

theorem mem_B_iff (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (y : (Sh ς k C).X n) :
    y ∈ (Sh ς k C).B n ↔ y ⟨m, h⟩ ∈ C.B m := by
  cases n with
  | zero =>
    obtain rfl : m = 0 := by omega
    constructor
    · intro e
      have e' : y = 0 := e
      rw [e']
      exact Submodule.zero_mem _
    · intro e
      have e' : y ⟨0, h⟩ = 0 := e
      have : y = 0 := ext_at ς k C h e'
      rw [this]
      exact Submodule.zero_mem _
  | succ n =>
    cases m with
    | zero =>
      constructor
      · rintro ⟨x, rfl⟩
        rw [d_apply_zero ς k C x h]
        exact Submodule.zero_mem _
      · intro e
        have e' : y ⟨0, h⟩ = 0 := e
        have : y = 0 := ext_at ς k C h e'
        rw [this]
        exact Submodule.zero_mem _
    | succ m =>
      have h0 : m + k = n := by omega
      constructor
      · rintro ⟨x, rfl⟩
        rw [d_apply_succ ς k C h0 x h]
        exact ⟨(ς : ℤ) • x ⟨m, h0⟩, by rw [map_zsmul]⟩
      · rintro ⟨z, hz⟩
        refine ⟨(ev ς k C h0).symm ((ς : ℤ) • z), ext_at ς k C h ?_⟩
        rw [d_apply_succ ς k C h0 _ h]
        change (ς : ℤ) • C.d m ((ev ς k C h0) ((ev ς k C h0).symm ((ς : ℤ) • z))) = _
        rw [LinearEquiv.apply_symm_apply, map_zsmul, unit_smul_smul, hz]

def evZ (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : C.Z m ≃ₗ[K] (Sh ς k C).Z n :=
  LinearEquiv.ofSubmodules (ev ς k C h).symm (C.Z m) ((Sh ς k C).Z n) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine (mem_Z_iff ς k C h _).2 ?_
      change C.d m ((ev ς k C h) ((ev ς k C h).symm x)) = 0
      rw [LinearEquiv.apply_symm_apply]
      exact hx
    · intro hy
      exact ⟨ev ς k C h y, (mem_Z_iff ς k C h y).1 hy, (ev ς k C h).symm_apply_apply y⟩)

theorem evZ_coe (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) (x : C.Z m) :
    ev ς k C h (evZ ς k C h x).1 = x.1 :=
  (ev ς k C h).apply_symm_apply x.1

def evH (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) {m n : ℕ} (h : m + k = n) : C.H m ≃ₗ[K] (Sh ς k C).H n :=
  Submodule.Quotient.equiv _ _ (evZ ς k C h) (by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x.1 ∈ C.B m := hx
      change (evZ ς k C h x).1 ∈ (Sh ς k C).B n
      refine (mem_B_iff ς k C h _).2 ?_
      have := evZ_coe ς k C h x
      rw [ev_apply] at this
      rw [this]
      exact hx'
    · intro hy
      have hy' : y.1 ∈ (Sh ς k C).B n := hy
      refine ⟨(evZ ς k C h).symm y, ?_, (evZ ς k C h).apply_symm_apply y⟩
      change ((evZ ς k C h).symm y).1 ∈ C.B m
      have := evZ_coe ς k C h ((evZ ς k C h).symm y)
      rw [LinearEquiv.apply_symm_apply, ev_apply] at this
      rw [← this]
      exact (mem_B_iff ς k C h _).1 hy')

theorem main : ∀ {K : Type} [Field K] (ς : ℤˣ) (k : ℕ) (C : Cx.{1} K) (n : ℕ), (n < k → Subsingleton ((Sh ς k C).H n)) ∧ ∀ (m : ℕ) (h : m + k = n), ∃ e : C.H m ≃ₗ[K] (Sh ς k C).H n, ∀ (y : (Sh ς k C).X n) (hy : (Sh ς k C).d n y = 0) (hy' : C.d m (y ⟨m, h⟩) = 0), e (C.cls (y ⟨m, h⟩) hy') = (Sh ς k C).cls y hy := by
  intro K _ ς k C n
  refine ⟨fun hn => ?_, fun m h => ⟨evH ς k C h, fun y hy hy' => ?_⟩⟩
  · have : IsEmpty {m : ℕ // m + k = n} := ⟨fun x => by have := x.2; omega⟩
    have hX : Subsingleton ((Sh ς k C).X n) :=
      inferInstanceAs (Subsingleton (∀ m : {m : ℕ // m + k = n}, C.X m.1))
    have hZ : Subsingleton ((Sh ς k C).Z n) := ⟨fun a b => Subtype.ext (hX.elim _ _)⟩
    exact Quotient.instSubsingletonQuotient _
  · refine congrArg (Submodule.Quotient.mk (p := ((Sh ς k C).B n).submoduleOf ((Sh ς k C).Z n))) (Subtype.ext ?_)
    exact (ev ς k C h).symm_apply_apply y

end GlobalTheory.CompanionTheory.KunGlue.ShiftCoh
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedSystemDescends
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.ShDesc

universe w

variable {R : Type} [CommRing R] {ι : Type} [DecidableEq ι]

def cechMap (P Q : PM.{w} R ι) (e : ∀ S, P.M S →ₗ[R] Q.M S) (n : ℕ) : P.cech.X n →ₗ[R] Q.cech.X n :=
  LinearMap.pi fun i => (e (ent i)).comp (LinearMap.proj i)

theorem cechMap_d (P Q : PM.{w} R ι) (e : ∀ S, P.M S →ₗ[R] Q.M S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (P.res h x) = Q.res h (e S x)) (n : ℕ) (x : P.cech.X n) :
    Q.cech.d n (cechMap P Q e n x) = cechMap P Q e (n + 1) (P.cech.d n x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Cos.d_apply, Cos.d_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  congr 1
  funext t
  exact (hn _ _).symm

theorem cechMap_aug (P Q : PM.{w} R ι) (e : ∀ S, P.M S →ₗ[R] Q.M S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (P.res h x) = Q.res h (e S x)) (x : P.M ∅) :
    Q.aug (e ∅ x) = cechMap P Q e 0 (P.aug x) := by
  funext t
  exact (hn _ _).symm

theorem ex_of_equiv (P Q : PM.{w} R ι) (e : ∀ S, Q.M S ≃ₗ[R] P.M S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (Q.res h x) = P.res h (e S x)) (hP : P.Ex) : Q.Ex := by
  have hn' : ∀ {S T : Finset ι} (h : S ⊆ T) x, (e T).symm (P.res h x) = Q.res h ((e S).symm x) := by
    intro S T h x
    apply (e T).injective
    rw [hn]
    simp
  let f : ∀ S, P.M S →ₗ[R] Q.M S := fun S => ((e S).symm : P.M S →ₗ[R] Q.M S)
  let g : ∀ S, Q.M S →ₗ[R] P.M S := fun S => ((e S) : Q.M S →ₗ[R] P.M S)
  have hf : ∀ {S T : Finset ι} (h : S ⊆ T) x, f T (P.res h x) = Q.res h (f S x) := hn'
  have hg : ∀ {S T : Finset ι} (h : S ⊆ T) x, g T (Q.res h x) = P.res h (g S x) := hn
  have fg : ∀ n (y : Q.cech.X n), cechMap P Q f n (cechMap Q P g n y) = y := by
    intro n y
    funext t
    exact (e _).symm_apply_apply _
  have gf0 : ∀ n (y : P.cech.X n), cechMap Q P g n (cechMap P Q f n y) = y := by
    intro n y
    funext t
    exact (e _).apply_symm_apply _
  obtain ⟨h0, h1, h2, h3⟩ := hP
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_, fun n y hy => ?_⟩
  · have : Q.aug y = cechMap P Q f 0 (P.aug (g ∅ y)) := by
      rw [← cechMap_aug P Q f hf]
      congr 1
      exact ((e ∅).symm_apply_apply y).symm
    change Q.cech.d 0 (Q.aug y) = 0
    rw [this, cechMap_d P Q f hf, show P.cech.d 0 (P.aug (g ∅ y)) = 0 from h0 _, map_zero]
  · have h := h1 (g ∅ y) (by
      have := cechMap_aug Q P g hg y
      rw [this]
      change cechMap Q P g 0 (Q.aug y) = 0 at *
      rw [hy, map_zero])
    rw [one_smul] at h ⊢
    exact (e ∅).injective (by rw [map_zero]; exact h)
  · obtain ⟨x, hx⟩ := h2 (cechMap Q P g 0 y) (by
      change P.cech.d 0 _ = 0
      rw [cechMap_d Q P g hg]
      have hy' : Q.cech.d 0 y = 0 := hy
      rw [hy', map_zero])
    refine ⟨f ∅ x, ?_⟩
    rw [one_smul] at hx ⊢
    rw [cechMap_aug P Q f hf]
    have hx' : P.aug x = cechMap Q P g 0 y := hx
    rw [hx', fg]
  · obtain ⟨x, hx⟩ := h3 n (cechMap Q P g (n + 1) y) (by
      change P.cech.d (n + 1) _ = 0
      rw [cechMap_d Q P g hg]
      have hy' : Q.cech.d (n + 1) y = 0 := hy
      rw [hy', map_zero])
    refine ⟨cechMap P Q f n x, ?_⟩
    rw [one_smul] at hx ⊢
    change Q.cech.d n _ = y
    rw [cechMap_d P Q f hf]
    have hx' : P.cech.d n x = cechMap Q P g (n + 1) y := hx
    rw [hx', fg]

theorem ex_of_subsingleton (P : PM.{w} R ι) (h : ∀ S, Subsingleton (P.M S)) : P.Ex := by
  have hX : ∀ n, Subsingleton (P.cech.X n) := fun n =>
    inferInstanceAs (Subsingleton (∀ i : Fin (n + 1) → ι, P.M (ent i)))
  refine ⟨fun x => Subsingleton.elim (α := P.cech.X 1) _ _, fun x _ => Subsingleton.elim _ _,
    fun y _ => ⟨0, Subsingleton.elim (α := P.cech.X 0) _ _⟩, fun n y _ => ⟨0, Subsingleton.elim (α := P.cech.X (n + 1)) _ _⟩⟩

variable {K : Type} [Field K]

def shEv (ς : ℤˣ) (k : ℕ) (C : Cx.{w} K) {m n : ℕ} (h : m + k = n) : (Sh ς k C).X n ≃ₗ[K] C.X m :=
  LinearEquiv.ofBijective
    (LinearMap.proj (φ := fun p : {p : ℕ // p + k = n} => C.X p.1) ⟨m, h⟩) (by
    constructor
    · intro y y' hyy
      funext ⟨p, hp⟩
      obtain rfl : p = m := by omega
      exact hyy
    · intro x
      refine ⟨fun p => (show m = p.1 by have := p.2; omega) ▸ x, rfl⟩)

theorem shSy_desc {ς : ℤˣ} {k : ℕ} {A : Sy.{w} K ι} (hA : A.Desc) : (shSy ς k A).Desc := by
  intro n
  by_cases hk : k ≤ n
  · have h : n - k + k = n := by omega
    exact ex_of_equiv (A.term (n - k)) ((shSy ς k A).term n) (fun S => shEv ς k (A.K S) h)
      (fun _ _ => rfl) (hA (n - k))
  · refine ex_of_subsingleton _ fun S => ?_
    have : IsEmpty {m : ℕ // m + k = n} := ⟨fun p => hk (by have := p.2; omega)⟩
    exact inferInstanceAs (Subsingleton (∀ m : {m : ℕ // m + k = n}, (A.K S).X m.1))

theorem sh_desc : ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] (ς : ℤˣ) (k : ℕ) (A : Sy.{1} K ι),
    A.Desc → (shSy ς k A).Desc :=
  fun _ _ _ h => shSy_desc h

end GlobalTheory.CompanionTheory.KunGlue.ShDesc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightTranslation
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

namespace GlobalTheory.CompanionTheory.ChainSum

theorem sdot_measurable {m : ℕ} (e : Fin m → SignType) : Measurable (sdot e) := by
  unfold sdot
  exact Finset.measurable_fun_sum _ fun i _ => (measurable_pi_apply i).const_mul _

theorem sdot_add' {m : ℕ} (e : Fin m → SignType) (a b : Fin m → ℝ) :
    sdot e (a + b) = sdot e a + sdot e b := by
  simp [sdot, mul_add, Finset.sum_add_distrib]

theorem chainSum_rest : ∀ m : ℕ, (∀ y : (Fin m → SignType) → ℝ, Measurable (gam y)) ∧
    (∀ (y : (Fin m → SignType) → ℝ) a b, gam (fun e => y e + sdot e b) (a + b) = gam y a) ∧
    ∀ (y y' : (Fin m → SignType) → ℝ) e s t a, (∀ e', SLe e e' ∨ SLe e' e → y e' = y' e') →
      gam (Function.update y e s) a - gam (Function.update y e t) a =
        gam (Function.update y' e s) a - gam (Function.update y' e t) a := by
  intro m
  refine ⟨fun y => ?_, fun y a b => ?_, fun y y' e s t a h => ?_⟩
  · unfold gam gamOn
    refine Finset.measurable_fun_sum _ fun c _ => ?_
    refine Measurable.const_mul (Finset.measurable_fun_prod _ fun e _ => ?_) _
    exact Measurable.ite (measurableSet_lt measurable_const (sdot_measurable e))
      measurable_const measurable_const
  · unfold gam gamOn
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun e _ => ?_
    have hiff : (y e + sdot e b < sdot e (a + b)) ↔ y e < sdot e a := by
      rw [sdot_add']
      exact add_lt_add_iff_right _
    exact if_congr hiff rfl rfl
  · unfold gam gamOn
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hchain : IsChain SLe (↑c : Set (Fin m → SignType)) := by
      simp only [Finset.mem_filter] at hc
      exact hc.2.2.1
    by_cases hec : e ∈ c
    · have key : ∀ u : ℝ, (∏ e' ∈ c, if Function.update y e u e' < sdot e' a then (1 : ℝ) else 0) =
          ∏ e' ∈ c, if Function.update y' e u e' < sdot e' a then (1 : ℝ) else 0 := by
        intro u
        refine Finset.prod_congr rfl fun e' he' => ?_
        by_cases hne : e' = e
        · subst hne
          simp only [Function.update_self]
        · have hcmp : SLe e e' ∨ SLe e' e :=
            hchain (Finset.mem_coe.2 hec) (Finset.mem_coe.2 he') (Ne.symm hne)
          simp only [Function.update_of_ne hne, h e' hcmp]
      rw [key s, key t]
    · have key : ∀ (z : (Fin m → SignType) → ℝ) (u v : ℝ),
          (∏ e' ∈ c, if Function.update z e u e' < sdot e' a then (1 : ℝ) else 0) =
            ∏ e' ∈ c, if Function.update z e v e' < sdot e' a then (1 : ℝ) else 0 := by
        intro z u v
        refine Finset.prod_congr rfl fun e' he' => ?_
        have hne : e' ≠ e := fun hh => hec (hh ▸ he')
        simp only [Function.update_of_ne hne]
      rw [key y s t, key y' s t, sub_self, sub_self]

end GlobalTheory.CompanionTheory.ChainSum
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulEqZeroOfEvEqZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
open GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue

theorem smul_eq_zero_of_ev_eq_zero : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (A : Type) [CommRing A] (P : Finset ι → Type) [∀ S, AddCommGroup (P S)] [∀ S, Module A (P S)] [∀ S, Module (MvPolynomial ι A) (P S)] [∀ S, IsScalarTower A (MvPolynomial ι A) (P S)] (res : ∀ S S' : Finset ι, S ⊆ S' → P S →ₗ[MvPolynomial ι A] P S'), (∀ S S' S'' (h : S ⊆ S') (h' : S' ⊆ S'') a, res S' S'' h' (res S S' h a) = res S S'' (h.trans h') a) → (∀ (T S : Finset ι) (a : P S), S.Nonempty → res S (S ∪ T) Finset.subset_union_left a = 0 → ∃ l : ℕ, xProd A T ^ l • a = 0) → ∀ (I : Finset ι) (hI : I.Nonempty) (m : glue res), ev res I hI m = 0 → ∃ l : ℕ, xProd A I ^ l • m = 0 := by
  intro ι _ _ A _ P _ _ _ _ res hcomp H I hI m hm
  have key : ∀ i, res {i} ({i} ∪ I) Finset.subset_union_left (m.1 i) = 0 := by
    intro i
    have hJ : ({i} ∪ I).Nonempty := ⟨i, Finset.mem_union_left I (Finset.mem_singleton_self i)⟩
    have h1 := ev_eq hcomp hJ (Finset.mem_union_left I (Finset.mem_singleton_self i)) m
    have h2 := res_ev hcomp hI hJ Finset.subset_union_right m
    rw [hm, map_zero] at h2
    exact h1.symm.trans h2.symm
  choose L hL using fun i => H I {i} (m.1 i) (Finset.singleton_nonempty i) (key i)
  refine ⟨∑ j, L j, ?_⟩
  apply Subtype.ext
  funext i
  simp only [Submodule.coe_smul, Pi.smul_apply, Submodule.coe_zero, Pi.zero_apply]
  have hsum : ∑ j, L j = (∑ j, L j - L i) + L i :=
    (Nat.sub_add_cancel (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))).symm
  rw [hsum, pow_add, mul_smul, hL i, smul_zero]

end GlobalTheory.CompanionTheory.FormalAlg.Lift.Glue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonReductionCompatStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_comparison_reduction_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n j : ℕ) (y : (HSW r M j).M (n + 1)), (redT r M (Nat.le_succ n)).pull j (bW r M (n + 1) j y) = bW r M n j ((HSW r M j).r n y) := by
  first | exact @GlobalTheory.CompanionTheory.CrisBaseChange.bW_red | exact GlobalTheory.CompanionTheory.CrisBaseChange.bW_red | (intros; apply GlobalTheory.CompanionTheory.CrisBaseChange.bW_red <;> assumption)
end

