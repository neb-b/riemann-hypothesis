module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

section Block

variable {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def blkV (bk : K₀ → K) (bx : ∀ k, J₀ k ≃ J (bk k)) : (Σ k, J₀ k) → Σ k, J k :=
  fun p => ⟨bk p.1, bx p.1 p.2⟩

theorem isBlockMap_blkV {bk : K₀ → K} (bx : ∀ k, J₀ k ≃ J (bk k)) (h : Function.Injective bk) :
    IsBlockMap bk (blkV bk bx) := by
  refine ⟨h, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, a⟩ ⟨k', a'⟩ e
    have e1 : bk k = bk k' := congrArg Sigma.fst e
    obtain rfl := h e1
    have e2 : bx k a = bx k a' := by simpa [blkV] using e
    rw [(bx k).injective e2]
  · rintro ⟨_, a⟩ ⟨k, rfl⟩
    exact ⟨⟨k, (bx k).symm a⟩, by simp [blkV]⟩

variable {κ : K₀ → K} {v : (Σ k, J₀ k) → Σ k, J k}

def restr (v : (Σ k, J₀ k) → Σ k, J k) : ((Σ k, J k) → ℂ) →L[ℝ] ((Σ k, J₀ k) → ℂ) :=
  ContinuousLinearMap.pi fun p => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Σ k, J k => ℂ) (v p)

theorem restr_ne (hv : IsBlockMap κ v) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (k : K₀) :
    ∃ i, z (v ⟨k, i⟩) ≠ 0 := by
  obtain ⟨i', hi'⟩ := hz (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : p.1 = k := hv.1 (by rw [← hv.2.2.1 p, hp])
  obtain ⟨pk, pi⟩ := p
  simp only at h2
  subst h2
  exact ⟨pi, by rw [hp]; exact hi'⟩

theorem isSmoothHerm_pull (hv : IsBlockMap κ v) {A : HermLine J₀} (hA : IsSmoothHerm A) :
    IsSmoothHerm (pullHerm hv A) := by
  have h := ContDiffOn.comp (s := {z : (Σ k, J k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}) hA
    (restr v).contDiff.contDiffOn (fun z hz => restr_ne hv hz)
  exact h

theorem isConj_pull (hv : IsBlockMap κ v) {A : HermLine J₀} (hA : IsConjInvariantH A) :
    IsConjInvariantH (pullHerm hv A) := fun z => hA fun p => z (v p)

theorem isConj_tensor {A B : HermLine J} (hA : IsConjInvariantH A) (hB : IsConjInvariantH B) :
    IsConjInvariantH (A.tensor B) := fun z => by
  show A.h _ * B.h _ = A.h _ * B.h _
  rw [hA, hB]

theorem mCoordIdeal_le_imageZ {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (i : Ω₀ →+* Ω) {y₀ : (Σ k, J₀ k) → Ω₀}
    {y : (Σ k, J k) → Ω} {bk : K₀ → K} (bx : ∀ k, J₀ k ≃ J (bk k))
    (hy : ∀ k a, y ⟨bk k, bx k a⟩ = i (y₀ ⟨k, a⟩)) :
    mCoordIdeal y₀ ≤ imageZ (blkV bk bx) (mCoordIdeal y) := by
  intro f hf
  let Φ : MvPolynomial K₀ Ω₀ →+* MvPolynomial K Ω :=
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp i) fun k => MvPolynomial.X (bk k)
  have key : ∀ f : MRing J₀, mConeMap y (rename (blkV bk bx) f) = Φ (mConeMap y₀ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap, Φ]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp =>
      obtain ⟨k, a⟩ := n
      simp only [map_mul, hp, rename_X]
      congr 1
      simp [mConeMap, Φ, blkV, hy]
  have hf' : mConeMap y₀ f = 0 := hf
  show mConeMap y (rename (blkV bk bx) f) = 0
  rw [key, hf', map_zero]

theorem mem_mcPts_restr (hv : IsBlockMap κ v) {P₀ : Ideal (MRing J₀)} {P : Ideal (MRing J)}
    (hP : P₀ ≤ imageZ v P) {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts P) : (fun p => z (v p)) ∈ mcPts P₀ := by
  refine ⟨restr_ne hv hz.1, fun f hf => ?_⟩
  have := hz.2 _ (hP hf)
  have e : (rename v : MRing J₀ →ₐ[ℤ] MRing J).toRingHom f = rename v f := rfl
  rw [e, map_rename, eval_rename] at this
  exact this

end Block

section Lines

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem log_h_smul (A : HermLine J) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (A.h fun p => c p.1 * z p) = Real.log (A.h z) + ∑ k, (A.a k : ℝ) * Real.log ‖c k‖ := by
  have h1 : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
  rw [A.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (h1 k)) (A.pos z hz).ne',
    Real.log_prod (fun k _ => zpow_ne_zero _ (h1 k)), add_comm]
  simp only [Real.log_zpow]

theorem prod_zpow_sum {R : Type} [Field R] {X : Type} (s : Finset X) {r : R} (hr : r ≠ 0) (a : X → ℤ) :
    ∏ x ∈ s, r ^ a x = r ^ ∑ x ∈ s, a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, zpow_add₀ hr, ih]

def stepLine {N : ℕ} (T : Fin N → HermLine J) (i : Fin N) : HermLine J where
  a := fun k => -∑ x ∈ Finset.Iic i, (T x).a k
  h z := ∏ x ∈ Finset.Iic i, ((T x).h z)⁻¹
  pos z hz := Finset.prod_pos fun x _ => inv_pos.2 ((T x).pos z hz)
  smul c z hc := by
    have h1 : ∀ k, (‖c k‖ : ℝ) ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    simp only [(T _).smul c z hc, mul_inv, Finset.prod_mul_distrib]
    congr 1
    simp only [← Finset.prod_inv_distrib]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [zpow_neg, ← prod_zpow_sum _ (h1 k), Finset.prod_inv_distrib]

theorem log_stepLine {N : ℕ} (T : Fin N → HermLine J) (i : Fin N) {z : (Σ k, J k) → ℂ}
    (hz : ∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) :
    Real.log ((stepLine T i).h z) = -∑ x ∈ Finset.Iic i, Real.log ((T x).h z) := by
  show Real.log (∏ x ∈ Finset.Iic i, ((T x).h z)⁻¹) = _
  rw [Real.log_prod fun x _ => inv_ne_zero ((T x).pos z hz).ne']
  simp only [Real.log_inv, Finset.sum_neg_distrib]

theorem isSmoothHerm_stepLine {N : ℕ} {T : Fin N → HermLine J} (hT : ∀ x, IsSmoothHerm (T x)) (i : Fin N) :
    IsSmoothHerm (stepLine T i) := by
  show ContDiffOn ℝ _ (fun z => ∏ x ∈ Finset.Iic i, ((T x).h z)⁻¹) _
  exact contDiffOn_prod fun x _ => (hT x).inv fun z hz => ((T x).pos z hz).ne'

def corr {Ψ : Type} {N : ℕ} (T : Ψ × Fin N → HermLine J) : Option (Ψ × Fin N) → HermLine J
  | none => Top.trivLine J
  | some r => stepLine (fun k => T (r.1, k)) r.2

theorem isSmoothHerm_trivLine : IsSmoothHerm (Top.trivLine J) := contDiffOn_const

theorem isSmoothHerm_corr {Ψ : Type} {N : ℕ} {T : Ψ × Fin N → HermLine J} (hT : ∀ r, IsSmoothHerm (T r))
    (a : Option (Ψ × Fin N)) : IsSmoothHerm (corr T a) := by
  cases a with
  | none => exact isSmoothHerm_trivLine
  | some r => exact isSmoothHerm_stepLine (fun k => hT (r.1, k)) r.2

def IsFlatOn {P Jd : Ideal (MRing J)} {e : ℕ} (R : AnLogRes P Jd e) (T : HermLine J) : Prop :=
  PB.SamePot R.A Set.univ (potOf R T) (ReciprocityTheory.AnForm.M.LocPot.ofFun 0)

def withTop {P Jd : Ideal (MRing J)} {e : ℕ} (R : AnLogRes P Jd e) (hP : ¬ (⊤ : Ideal (MRing J)) ≤ P)
    (hE : Cmp.IsEmbedded R.A P R.U R.lift) : AnLogRes P ⊤ e where
  homog := ⟨{1}, fun f hf => ⟨0, by
    rw [Set.mem_singleton_iff.1 hf]
    intro m hm k
    have hm0 : m = 0 := by
      rw [MvPolynomial.support_one] at hm
      simpa using hm
    simp [hm0]⟩, by simp⟩
  nondeg := hP
  X := R.X
  A := R.A
  U := R.U
  isOpen_U := R.isOpen_U
  mem_U := R.mem_U
  lift := R.lift
  holo := R.holo
  mem := R.mem
  compat := R.compat
  surj z hz _ := hE.surj z hz
  inj x x' _ h := hE.inj x x' h
  immersion x _ p hp j hj := hE.immersion x p hp j hj
  snc f a hf hh hz := R.snc f a hf hh fun z hz' h0 => by
    have h1 := (hz z hz' h0).2 1 trivial
    simp at h1
  null j := by
    have : {x | R.lift x x ∈ mcPts (⊤ : Ideal (MRing J))} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have h1 := h.2 1 trivial
      simp at h1
    rw [this]
    simp

end Lines

section Points

variable {X X₀ : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀]

def pushCpt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {h : X ⟶ X₀} {i : Ω₀ →+* Ω}
    (hd : Dominates ξ ξ₀ h i) (p : Cpt ξ) : Cpt ξ₀ := ⟨h p.1, hd.specializes p⟩

variable {K₀ : Type} [Fintype K₀] {J₀ : K₀ → Type} [∀ k, Fintype (J₀ k)]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

def IsRatio (ξ : Spec (CommRingCat.of Ω) ⟶ X) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (bk : K₀ → K)
    (bx : ∀ k, J₀ k ≃ J (bk k)) (i : Ω₀ →+* Ω) (a : K → ℤ) (a₀ : K₀ → ℤ) (e : Ω) (e₀ : Ω₀)
    (φ : ((Σ k, J k) → ℂ) → ℝ) : Prop :=
  ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w →
    ∀ (c : (k : K) → J k) (c₀ : (k : K₀) → J₀ k), (∀ k, w ⟨k, c k⟩ ≠ 0) → (∀ k, w (blkV bk bx ⟨k, c₀ k⟩) ≠ 0) →
      ∃ u : ℂ, u ≠ 0 ∧ ValAt ξ z (i ((∏ k, y₀ ⟨k, c₀ k⟩ ^ a₀ k) * e₀) / ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) u ∧
        φ w * ∏ k, ‖w (blkV bk bx ⟨k, c₀ k⟩)‖ ^ a₀ k = ‖u‖ * ∏ k, ‖w ⟨k, c k⟩‖ ^ a k

end Points

section Cover

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {S₀ S : Finset ℕ} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] {K₀ K : Type} [Fintype K₀] [Fintype K]
  {J₀ : K₀ → Type} {J : K → Type} {y₀ : (Σ k, J₀ k) → Ω₀} {y : (Σ k, J k) → Ω}

def IsCovOf (𝔐₀ : HodgeCpt Y S₀ y₀) (𝔐 : HodgeCpt Y S y) (i : Ω₀ →+* Ω) (h : 𝔐.X ⟶ 𝔐₀.X) : Prop :=
  GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i ∧ 𝔐.f = h ≫ 𝔐₀.f ∧ 𝔐.cst = i.comp 𝔐₀.cst

def FlagsOver {𝔐₀ : HodgeCpt Y S₀ y₀} {𝔐 : HodgeCpt Y S y} (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (i : Ω₀ →+* Ω) : Prop :=
  ∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt (Fl₀.b s a)).left ≫ 𝔐₀.m.φ

def GenPull {𝔐₀ : HodgeCpt Y S₀ y₀} {𝔐 : HodgeCpt Y S y} (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (i : Ω₀ →+* Ω) {h : 𝔐.X ⟶ 𝔐₀.X}
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ h i) : Prop :=
  ∀ q : Cpt 𝔐.ξ, (∀ r : ℕ, r.Prime → ¬ InFibre 𝔐.ξ r q) → ∀ s (a : Fin (labelRk D s)) (t₀ : Ω₀),
    ((𝔐₀.V s).gr (Fl₀.b s) a).IsGenAt (pushCpt hd q) t₀ → ((𝔐.V s).gr (Fl.b s) a).IsGenAt q (i t₀)

def NormPull {𝔐₀ : HodgeCpt Y S₀ y₀} {𝔐 : HodgeCpt Y S y} (Fl₀ : 𝔐₀.Flag) (Fl : 𝔐.Flag) (i : Ω₀ →+* Ω)
    (h : 𝔐.X ⟶ 𝔐₀.X) : Prop :=
  ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) s (a : Fin (labelRk D s)) (t₀ : Ω₀) (ν : ℝ),
    𝔐₀.M.IsGrNorm 𝔐₀.t.PP.L (𝔐₀.V s) (Fl₀.b s) a (z ≫ h) t₀ ν →
      𝔐.M.IsGrNorm 𝔐.t.PP.L (𝔐.V s) (Fl.b s) a z (i t₀) ν

end Cover

end GlobalTheory.CompanionTheory.Ar.Chg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelProjectiveGenericFibre
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

section Alg

variable {A K V T : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
  [AddCommGroup V] [Module A V] [AddCommGroup T] [Module K T] [Module A T] [IsScalarTower A K T]

theorem finrank_eq_of_isLocalized (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] [Module K T]
    [IsScalarTower A K T] (j : V →ₗ[A] T) [IsLocalizedModule (nonZeroDivisors A) j] :
    Module.finrank A V = Module.finrank K T := by
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors A) j le_rfl
  have h2 : Module.finrank K T = Module.finrank A T :=
    congrArg Cardinal.toNat (IsLocalization.rank_eq K (N := T) (nonZeroDivisors A) le_rfl)
  exact h1.symm.trans h2.symm

theorem injective_of_isLocalized [Module.IsTorsionFree A V] (j : V →ₗ[A] T)
    [IsLocalizedModule (nonZeroDivisors A) j] : Function.Injective j := by
  intro x y h
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_iff_exists (nonZeroDivisors A) j).1 h
  exact smul_right_injective V (nonZeroDivisors.ne_zero c.2) hc

def resMap (j : V →ₗ[A] T) (W : Submodule K T) : (W.restrictScalars A).comap j →ₗ[A] W where
  toFun x := ⟨j x, x.2⟩
  map_add' x y := Subtype.ext (map_add j _ _)
  map_smul' c x := Subtype.ext (map_smul j c _)

theorem isLocalized_resMap [Module.IsTorsionFree A V] (j : V →ₗ[A] T)
    [IsLocalizedModule (nonZeroDivisors A) j] (W : Submodule K T) :
    IsLocalizedModule (nonZeroDivisors A) (resMap j W) := by
  constructor
  · intro a
    have hk : algebraMap A K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2
    have key : ∀ w : W, algebraMap A (Module.End A W) a w = algebraMap A K a • w := fun w => by
      rw [Module.algebraMap_end_apply, algebraMap_smul]
    refine (Module.End.isUnit_iff _).2 ⟨fun w w' h => ?_, fun w => ⟨(algebraMap A K a)⁻¹ • w, ?_⟩⟩
    · rw [key, key] at h
      exact smul_right_injective W hk h
    · rw [key, smul_smul, mul_inv_cancel₀ hk, one_smul]
  · intro w
    obtain ⟨⟨y, a⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors A) j (w : T)
    have h' : (a : A) • (w : T) = j y := h
    have hy : j y ∈ W := by
      rw [← h', ← algebraMap_smul K (a : A) (w : T)]
      exact W.smul_mem _ w.2
    exact ⟨(⟨y, hy⟩, a), Subtype.ext h⟩
  · intro x y h
    refine ⟨1, ?_⟩
    rw [one_smul, one_smul]
    exact Subtype.ext (injective_of_isLocalized j (congrArg Subtype.val h))

theorem finrank_comap_eq [Module.IsTorsionFree A V] (j : V →ₗ[A] T)
    [IsLocalizedModule (nonZeroDivisors A) j] (W : Submodule K T) :
    Module.finrank A ((W.restrictScalars A).comap j) = Module.finrank K W := by
  haveI := isLocalized_resMap j W
  exact finrank_eq_of_isLocalized K (resMap j W)

theorem exists_smul_mem (j : V →ₗ[A] T) (S : Submodule A V) (B : Set T)
    (hB : ∀ w ∈ B, ∃ a : A, a ≠ 0 ∧ ∃ y ∈ S, a • w = j y) {w : T} (hw : w ∈ Submodule.span K B) :
    ∃ a : A, a ≠ 0 ∧ ∃ y ∈ S, a • w = j y := by
  induction hw using Submodule.span_induction with
  | mem w hw => exact hB w hw
  | zero => exact ⟨1, one_ne_zero, 0, S.zero_mem, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha, y, hy, e⟩ := hu
    obtain ⟨b, hb, y', hy', e'⟩ := hv
    refine ⟨a * b, mul_ne_zero ha hb, b • y + a • y', S.add_mem (S.smul_mem _ hy) (S.smul_mem _ hy'), ?_⟩
    rw [map_add (f := _), map_smul, map_smul, ← e, ← e', smul_add, smul_smul, smul_smul, mul_comm a b, mul_comm b a,
      mul_comm a b]
  | smul c u _ hu =>
    obtain ⟨a, ha, y, hy, e⟩ := hu
    obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := A) c
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hk : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
    refine ⟨d * a, mul_ne_zero hd0 ha, b • y, S.smul_mem _ hy, ?_⟩
    rw [map_smul, ← e, ← algebraMap_smul K (d * a), ← algebraMap_smul K b, ← algebraMap_smul K a, smul_smul,
      smul_smul, map_mul]
    congr 1
    field_simp

end Alg

section Num

variable {L V T : Type} [Field L] [NumberField L] [AddCommGroup V] [Module (𝓞 L) V] [AddCommGroup T]
  [Module (𝓞 L) T]

theorem exists_nat_smul (j : V →ₗ[𝓞 L] T) [IsLocalizedModule (nonZeroDivisors (𝓞 L)) j] (w : T) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ y : V, (n : 𝓞 L) • w = j y := by
  obtain ⟨⟨y, a⟩, h⟩ := IsLocalizedModule.surj (nonZeroDivisors (𝓞 L)) j w
  have ha : (a : 𝓞 L) ≠ 0 := nonZeroDivisors.ne_zero a.2
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {(a : 𝓞 L)}))
  refine ⟨Ideal.absNorm (Ideal.span {(a : 𝓞 L)}), ?_, b • y, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha
  · have h' : (a : 𝓞 L) • w = j y := h
    rw [← hb, mul_smul, map_smul, ← h']

end Num

section Geo

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {Li : Type} [AddCommGroup Li]
  [Module Ω Li] {L : Type} [Field L] [NumberField L] {z : Sp (𝓞 L) ⟶ X} {V : Type} [AddCommGroup V]
  [Module (𝓞 L) V] {T : Type} [AddCommGroup T] [Module L T] [Module (𝓞 L) T] [IsScalarTower (𝓞 L) L T]

theorem eq_pt_of_lifts {MB : LieModel G z V} {TL : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) T}
    {j : V →ₗ[𝓞 L] T} (hl : ∀ x, ((TL.pt (j x)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left)) {x : V}
    {v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G} (h : (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left)) :
    v = TL.pt (j x) := by
  have e : v.left ≫ 𝟙 G.left = (TL.pt (j x)).left ≫ 𝟙 G.left := h.trans (hl x).symm
  rw [Category.comp_id, Category.comp_id] at e
  exact Over.OverMorphism.ext e

theorem mem_subGens_of_nat {M : LieModel G ξ Li} {U : Submodule Ω Li} {MB : LieModel G z V}
    {TL : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) T} {j : V →ₗ[𝓞 L] T}
    (hl : ∀ x, ((TL.pt (j x)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left)) {e : Li} (he : e ∈ U) {w : T}
    (hv : M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)) (n : ℕ) {y : V} (hy : (n : 𝓞 L) • w = j y) :
    y ∈ subGens M U z MB := by
  obtain ⟨h1, -⟩ := id hv
  have key := hv.smul h1 (n : X.presheaf.stalk (centre (spMap (algebraMap (𝓞 L) L) ≫ z)))
  have e1 : (Scheme.stalkClosedPointTo (spMap (algebraMap (𝓞 L) L) ≫ z)).hom
      (n : X.presheaf.stalk (centre (spMap (algebraMap (𝓞 L) L) ≫ z))) = (n : L) := map_natCast _ n
  rw [map_natCast, e1, ← TL.pt_smul] at key
  have e2 : (n : L) • w = j y := by
    rw [← hy, ← algebraMap_smul L (n : 𝓞 L) w, map_natCast]
  rw [e2] at key
  exact ⟨_, U.smul_mem _ he, _, key, hl y⟩

end Geo

theorem finrank_subFib : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (V : Type) [AddCommGroup V] [Module (𝓞 L) V] [Module.Finite (𝓞 L) V] [Module.Projective (𝓞 L) V] (MB : LieModel G z V) (T : Type) [AddCommGroup T] [Module L T] [Module (𝓞 L) T] [IsScalarTower (𝓞 L) L T] (TL : LieModel G (spMap (algebraMap (𝓞 L) L) ≫ z) T) (j : V →ₗ[𝓞 L] T) (U : Submodule Ω Li), IsCptGen ξ → (∀ x, ((TL.pt (j x)).left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left)) → IsBaseChange L j → Module.finrank (𝓞 L) V = Module.finrank L T ∧ Module.finrank (𝓞 L) (FlagFib.subFib M U z MB) = Module.finrank L (Submodule.span L {w | ∃ e ∈ U, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)}) := by
  intro X G _ Ω _ ξ Li _ _ M L _ _ z V _ _ _ _ MB T _ _ _ _ TL j U _ hl hj
  haveI : IsLocalizedModule (nonZeroDivisors (𝓞 L)) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (𝓞 L)) L j).2 hj
  refine ⟨finrank_eq_of_isLocalized L j, ?_⟩
  set B : Set T := {w | ∃ e ∈ U, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w)} with hBdef
  have hinj : Function.Injective j := injective_of_isLocalized j
  have hS : ∀ y ∈ Submodule.span (𝓞 L) (subGens M U z MB), j y ∈ Submodule.span L B := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨e, he, v, hv, hlift⟩ := hy
      have hv' := eq_pt_of_lifts hl hlift
      exact Submodule.subset_span ⟨e, he, hv' ▸ hv⟩
    | zero => simp
    | add a b _ _ ha hb =>
      rw [map_add]
      exact add_mem ha hb
    | smul c a _ ha =>
      rw [map_smul, ← algebraMap_smul L c (j a)]
      exact Submodule.smul_mem _ _ ha
  have hB : ∀ w ∈ B, ∃ a : 𝓞 L, a ≠ 0 ∧ ∃ y ∈ Submodule.span (𝓞 L) (subGens M U z MB), a • w = j y := by
    rintro w ⟨e, he, hv⟩
    obtain ⟨n, hn, y, hy⟩ := exists_nat_smul j w
    exact ⟨n, Nat.cast_ne_zero.2 hn, y, Submodule.subset_span (mem_subGens_of_nat hl he hv n hy), hy⟩
  have e : subFib M U z MB = ((Submodule.span L B).restrictScalars (𝓞 L)).comap j := by
    ext x
    rw [mem_subFib]
    constructor
    · rintro ⟨a, ha, hx⟩
      have h1 := hS _ hx
      rw [map_smul, ← algebraMap_smul L a (j x)] at h1
      have hk : algebraMap (𝓞 L) L a ≠ 0 := fun h0 => ha (by simpa using h0)
      exact (Submodule.smul_mem_iff (Submodule.span L B) hk).1 h1
    · intro hx
      obtain ⟨a, ha, y, hy, h⟩ := exists_smul_mem j _ B hB (K := L) hx
      refine ⟨a, ha, ?_⟩
      rwa [hinj (by rw [map_smul]; exact h : j (a • x) = j y)]
  rw [e]
  exact finrank_comap_eq j _

end GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValAtEigen
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar


open LieTangent in
theorem valAt_eigen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (L : Type) [Field L] (zL : Sp L ⟶ 𝔐.X) (h : genPt 𝔐.ξ ⤳ centre zL) (g₀ : c.F →+* 𝔐.X.presheaf.stalk (centre zL)), (genMap 𝔐.ξ ⟨centre zL, h⟩).comp g₀ = 𝔐.cst → ∀ (s : CMType H ⊕ CMType H) (e : 𝔐.Li) (v : epsAt zL ⟶ 𝔐.t.G) (a : 𝓞 E), e ∈ 𝔐.Vgen s → 𝔐.M.ValAt zL e v → (v ≫ 𝔐.t.act.act a).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul ((Scheme.stalkClosedPointTo zL).hom (g₀ (labelEmb c s a))))) ≫ v.left := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 L _ zL h g₀ hg s e v a he hv
  obtain ⟨h', v₀, hext, rfl⟩ := (𝔐.M.valAt_iff zL e v).1 hv
  have hgen : genMap 𝔐.ξ ⟨centre zL, h⟩ (g₀ (labelEmb c s a)) = 𝔐.emb s a :=
    DFunLike.congr_fun hg (labelEmb c s a)
  have hρ : 𝔐.ρ a e = 𝔐.emb s a • e := by
    have h1 : e ∈ LinearMap.ker (𝔐.ρ a - 𝔐.emb s a • LinearMap.id) :=
      (Submodule.mem_iInf _).1 he a
    rw [LinearMap.mem_ker] at h1
    simpa [sub_eq_zero] using h1
  have hext' := (𝔐.M.extends_iff _ _ _).1 hext
  have h1 : 𝔐.M.Extends ⟨centre zL, h⟩ (𝔐.emb s a • e) (v₀ ≫ 𝔐.t.act.act a) := by
    rw [LieModel.extends_iff]
    refine ⟨?_, ?_⟩
    · rw [isTanAt_iff, ← Category.assoc, (isTanAt_iff _).1 hext'.1]
      haveI := 𝔐.t.act.hom a
      exact one_comp _
    · rw [← hρ, 𝔐.act a e, hext'.2, Category.assoc]
  have h2 := hext.smul (g₀ (labelEmb c s a))
  rw [hgen] at h2
  have key := h1.unique (𝔐.tie.gen.inj _) h2
  have e1 : epsBase _ (spec_centre zL) ≫ v₀ ≫ 𝔐.t.act.act a =
      epsScale zL ((Scheme.stalkClosedPointTo zL).hom (g₀ (labelEmb c s a))) ≫ epsBase _ (spec_centre zL) ≫ v₀ := by
    rw [key, ← Category.assoc, base_scale, Category.assoc]
    rfl
  exact congrArg (fun q => q.left) ((Category.assoc _ _ _).trans e1)

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

