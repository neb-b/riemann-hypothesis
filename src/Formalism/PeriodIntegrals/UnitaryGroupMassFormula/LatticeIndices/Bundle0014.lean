module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.Bundle0013
public import Mathlib

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImASubKpp
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

theorem imA_lift_mL (p : TypX X) (m : ℕ) {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ Ideal.span {((m : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} •
      latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    ∃ A ∈ mL X.B.I m, PI.FinKW.vecV X.B.I p.1 A = u ∧ ∀ v, v ≠ p.1 → PI.FinKW.vecV X.B.I v A = 0 := by
  refine Submodule.smul_induction_on hu ?_ ?_
  · intro r hr n hn
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    obtain ⟨A, hA, h1, h2⟩ := imA_lift_lat X p hn
    have hA' : scP X p a • A ∈ X.B.I.Lf :=
      Submodule.smul_mem _ (⟨_, scalarAt_mem_integralAdeles X p a⟩ : Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) hA
    refine ⟨(m : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • (scP X p a • A),
      Submodule.subset_span ⟨_, hA', rfl⟩, ?_, ?_⟩
    · rw [imA_vecV_smul', imA_vecV_smul', component_scalarAt_same, h1, smul_smul, imA_smul_alg, map_natCast]
      congr 1
      push_cast
      rw [mul_comm]
    · intro v hv
      rw [imA_vecV_smul', imA_vecV_smul', component_scalarAt_of_ne X p v hv, zero_smul, smul_zero]
  · rintro x y ⟨A, hA, h1, h2⟩ ⟨B, hB, h3, h4⟩
    exact ⟨A + B, add_mem hA hB, by rw [imA_vecV_add', h1, h3],
      fun v hv => by rw [imA_vecV_add', h2 v hv, h4 v hv, add_zero]⟩

theorem imA_inMod_glob (p : TypX X) (m : ℕ) (S : Set (Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F))
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)
    (hs : ∀ v, v ≠ p.1 → PI.FinKW.vecV X.B.I v w = 0)
    (h : InModP X p m (PI.FinKW.vecV X.B.I p.1 '' S) (PI.FinKW.vecV X.B.I p.1 w)) :
    InMod X.B.I m S w := by
  obtain ⟨a, ha, b, hb', hab⟩ := Submodule.mem_sup.mp h
  obtain ⟨A, hA, h1, h2⟩ := imA_lift_sp X p S ha
  obtain ⟨B, hB, h3, h4⟩ := imA_lift_mL X p m hb'
  have hw : w = A + B := by
    rw [← sub_eq_zero]
    apply imA_vec_ext X
    intro v
    rw [imA_vecV_sub, imA_vecV_add']
    by_cases hv : v = p.1
    · subst hv; rw [h1, h3, hab, sub_self]
    · rw [hs v hv, h2 v hv, h4 v hv, add_zero, sub_zero]
  rw [hw]
  exact Submodule.mem_sup.mpr ⟨A, hA, B, hB, rfl⟩

theorem imA_vecV_mulVec' (v : HeightOneSpectrum (𝓞 X.B.I.F)) (x : X.B.I.Gf)
    (w : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v ((X.B.I.fmat x - 1) *ᵥ w) =
      (((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (piV X.B.I v (tf X.B.I hb x)) :
        GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I v w := by
  rw [LocIdxLift_vecV_mulVec, Matrix.map_sub _ (map_sub _), LocIdxLift_psiV_fmat X.B.I hb,
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem imA_sub_kpp (p : TypX X) : {y | y ∈ KvX X p ∧ LocCong X p y} ⊆ KppX X hb p := by
  rintro y ⟨hy, h1, h2, h3⟩
  obtain ⟨x, hx⟩ := Bridge_tf_surjective X.B.I hb (liftHA X.B.I p.1 y)
  have hcomp : ∀ v, v ≠ p.1 → piV X.B.I v (tf X.B.I hb x) = 1 := fun v h => by
    rw [hx, LocIdxLift_piV_ne X.B.I p.1 v h]
  have hsame : piV X.B.I p.1 (tf X.B.I hb x) = y := by rw [hx, LocIdxLift_piV_same]
  have hsupp : ∀ w, ∀ v, v ≠ p.1 → PI.FinKW.vecV X.B.I v ((X.B.I.fmat x - 1) *ᵥ w) = 0 := by
    intro w v hv
    rw [imA_vecV_mulVec' X hb, hcomp v hv]
    have : ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (1 : HA (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J) :
        GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) = 1 := rfl
    rw [this, sub_self, Matrix.zero_mulVec]
  have hloc : ∀ w, PI.FinKW.vecV X.B.I p.1 ((X.B.I.fmat x - 1) *ᵥ w) =
      (((HA.mat (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J y :
        GL (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) :
        Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) - 1) *ᵥ
        PI.FinKW.vecV X.B.I p.1 w := by
    intro w; rw [imA_vecV_mulVec' X hb, hsame]
  have hxK : x ∈ X.B.I.Kset := by
    rw [← Bridge_mem_Kf_iff X.B.I hb, Kf, Subgroup.mem_iInf]
    intro v
    show HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (piV X.B.I v (tf X.B.I hb x)) ∈
      Kloc v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    by_cases h : v = p.1
    · subst h; rw [hsame]; exact hy
    · rw [hcomp v h]; exact (Kloc v _).one_mem
  have hc : K2cong X.B.I X.B.g X.e0 X.z0 X.bw x := by
    refine ⟨fun a => ?_, ?_, fun i => ?_⟩
    · apply imA_inMod_glob X p _ _ _ (hsupp _)
      rw [hloc, Set.image_image]; exact h1 a
    · apply imA_inMod_glob X p _ _ _ (hsupp _)
      rw [hloc, ← Set.range_comp]; exact h2
    · apply imA_inMod_glob X p _ _ _ (hsupp _)
      rw [hloc, Set.image_union, Set.image_image, ← Set.range_comp]; exact h3 i
  exact ⟨tf X.B.I hb x, ⟨x, ⟨hxK, hc⟩, rfl⟩, hsame⟩

theorem stImAloc_holds (p : TypX X) : StImAloc X hb p :=
  Set.Subset.antisymm (imA_kpp_sub X hb p) (imA_sub_kpp X hb p)

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.LatBasisAllOf
section
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct Matrix

section Gen

variable {K : Type} [Field K] (O : ValuationSubring K) {n : Type} [Fintype n] [DecidableEq n]

theorem dual_basis_iff (P : GL n K) (J : Matrix n n K) (z : n → K) :
    (∀ y : n → K, (∀ i, (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ y) i ∈ O) → z ⬝ᵥ (J *ᵥ y) ∈ O) ↔
      ∀ i, ((Matrix.transpose (P : Matrix n n K) * Matrix.transpose J) *ᵥ z) i ∈ O := by
  have key : ∀ c : n → K, z ⬝ᵥ (J *ᵥ ((P : Matrix n n K) *ᵥ c)) =
      ((Matrix.transpose (P : Matrix n n K) * Matrix.transpose J) *ᵥ z) ⬝ᵥ c := by
    intro c
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_mul]
  have hPP : ∀ c : n → K, ((P⁻¹ : GL n K) : Matrix n n K) *ᵥ ((P : Matrix n n K) *ᵥ c) = c := by
    intro c
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hPP' : ∀ y : n → K, (P : Matrix n n K) *ᵥ (((P⁻¹ : GL n K) : Matrix n n K) *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  constructor
  · intro h i
    have h1 := h ((P : Matrix n n K) *ᵥ Pi.single i 1) (by
      intro j
      rw [hPP]
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij])
    rw [key, dotProduct_single_one] at h1
    exact h1
  · intro h y hy
    rw [← hPP' y, key]
    exact sum_mem fun i _ => mul_mem (h i) (hy i)

end Gen

section Loc

variable {D : D7} (X : HidaSetting D) (p : TypX X) (θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p)

abbrev OpX : ValuationSubring (FpX X p) := p.1.adicCompletionIntegers X.B.I.F

def iota1 : X.B.I.E →+* FpX X p := (th1 X p θ).comp (inclR (FpX X p))

def iota2 : X.B.I.E →+* FpX X p := (th2 X p θ).comp (inclR (FpX X p))

def Mlat1 : Submodule (OpX X p) (Fin X.B.I.n → FpX X p) :=
  Submodule.span (OpX X p) ((fun l : Fin X.B.I.n → X.B.I.E => fun j => iota1 X p θ (l j)) ''
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))

def Mlat2 : Submodule (OpX X p) (Fin X.B.I.n → FpX X p) :=
  Submodule.span (OpX X p) ((fun l : Fin X.B.I.n → X.B.I.E => fun j => iota2 X p θ (l j)) ''
    (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)))

def LatSplitP : Prop :=
  ∀ x : Fin X.B.I.n → TpX X p, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
    (fun j => th1 X p θ (x j)) ∈ Mlat1 X p θ ∧ (fun j => th2 X p θ (x j)) ∈ Mlat2 X p θ

def LatFreeP : Prop :=
  ∃ P : GL (Fin X.B.I.n) (FpX X p), ∀ y, y ∈ Mlat1 X p θ ↔
    ∀ i, (((P⁻¹ : GL (Fin X.B.I.n) (FpX X p)) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (FpX X p)) *ᵥ y) i ∈ OpX X p

def LatDualP : Prop :=
  ∀ z, z ∈ Mlat2 X p θ ↔ ∀ y ∈ Mlat1 X p θ, z ⬝ᵥ (J1 X p θ *ᵥ y) ∈ OpX X p

theorem latBasis_of (hS : LatSplitP X p θ) (hF : LatFreeP X p θ) (hD : LatDualP X p θ) :
    ∃ P, LatBasis X p θ P := by
  obtain ⟨P, hP⟩ := hF
  refine ⟨P, fun x => ?_⟩
  rw [hS x, hD, hP]
  refine and_congr Iff.rfl ?_
  rw [← dual_basis_iff (OpX X p) P (J1 X p θ)]
  exact ⟨fun h y hy => h y ((hP y).2 hy), fun h y hy => h y ((hP y).1 hy)⟩

theorem latBasisAll_of
    (hS : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → LatSplitP X p θ)
    (hF : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → LatFreeP X p θ)
    (hD : ∀ θ : TpX X p ≃ₐ[FpX X p] FpX X p × FpX X p, IsSplitEquiv X p θ → LatDualP X p θ) :
    LatBasisAll X p := fun θ hθ => latBasis_of X p θ (hS θ hθ) (hF θ hθ) (hD θ hθ)

end Loc

end MassDataIdxSteps
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSsubIffSG
section
noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3 Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub MassDataIdxSpl
open scoped TensorProduct

variable {F E R : Type} [Field F] [Field E] [Algebra F E] [Field R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (θ : R ⊗[F] E ≃ₐ[R] R × R)

theorem reindex_mul' {ι : Type} [Fintype ι] [DecidableEq ι] (e : Fin n ≃ ι) (A B : Matrix (Fin n) (Fin n) R) :
    Matrix.reindex e e A * Matrix.reindex e e B = Matrix.reindex e e (A * B) := by
  simp only [Matrix.reindex_apply]
  exact Matrix.submatrix_mul_equiv A B e.symm e.symm e.symm

private theorem flagC_reindex_iff {K ι : Type} [Field K] [Fintype ι] [DecidableEq ι] {m : ℕ}
    (e : Fin n ≃ ι) (M : Matrix (Fin n) (Fin n) K) (v : Fin m → Fin n → K) :
    FlagC (Matrix.reindex e e M) (fun b => v b ∘ e.symm) ↔ FlagC M v := by
  let f : (Fin n → K) ≃ₗ[K] (ι → K) := LinearEquiv.funCongrLeft K K e.symm
  have hmv : ∀ w : Fin n → K, Matrix.reindex e e M *ᵥ (w ∘ e.symm) = (M *ᵥ w) ∘ e.symm := by
    intro w
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    congr 2
    ext i
    simp [Function.comp_def]
  have key : ∀ (x : Fin n → K) (S : Set (Fin n → K)),
      x ∘ e.symm ∈ Submodule.span K ((fun w : Fin n → K => w ∘ e.symm) '' S) ↔ x ∈ Submodule.span K S := by
    intro x S
    have h1 : (fun w : Fin n → K => w ∘ e.symm) = ⇑(f.toLinearMap) := rfl
    rw [h1, Submodule.span_image, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hyx : y = x := f.injective hxy
      exact hyx ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  unfold FlagC
  refine forall_congr' fun b => ?_
  show Matrix.reindex e e M *ᵥ (v b ∘ e.symm) - v b ∘ e.symm ∈
      Submodule.span K ((fun a => v a ∘ e.symm) '' {a | a < b}) ↔ _
  rw [hmv, show (fun a => v a ∘ e.symm) '' {a | a < b} =
      (fun w : Fin n → K => w ∘ e.symm) '' (v '' {a | a < b}) from
      (Set.image_image (fun w : Fin n → K => w ∘ e.symm) v {a | a < b}).symm]
  exact key (M *ᵥ v b - v b) _

theorem mem_Ssub_iff_sG (hθ : ∀ t, θ (sigR R σ t) = (θ t).swap) {r k : ℕ} (e : Fin n ≃ Idx r k)
    (hJ : IsUnit (jm1 J θ).det) (P : Frame E n r) (Q : GL (Idx r k) R) (l : Fin (r + 1) → R)
    (hl : ∀ b, l b ≠ 0)
    (hy1 : ∀ b, ((Q⁻¹ : GL (Idx r k) R) : Matrix (Idx r k) (Idx r k) R) *ᵥ
      (pr1 θ (ratV (F := F) R (F0 P b)) ∘ e.symm) = Pi.single (pe b) 1)
    (hy2 : ∀ b, (Q : Matrix (Idx r k) (Idx r k) R)ᵀ *ᵥ ((Matrix.reindex e e (jm1 J θ))ᵀ *ᵥ
      (pr2 θ (ratV (F := F) R (F0 P b)) ∘ e.symm)) = l b • Pi.single (pf b) 1)
    (g : HA R σ J) (g1 : GL (Idx r k) R)
    (hg1 : (g1 : Matrix (Idx r k) (Idx r k) R) = Matrix.reindex e e (cmp1 σ J θ g)) :
    g ∈ Ssub R σ J P ↔ Q⁻¹ * g1 * Q ∈ sG R r k := by
  rw [mem_Ssub_iff_flagC σ J θ P g]
  have hU : (Matrix.reindex e e (cmp2 σ J θ g))ᵀ * Matrix.reindex e e (jm1 J θ) *
      ((g1 : GL (Idx r k) R) : Matrix (Idx r k) (Idx r k) R) = Matrix.reindex e e (jm1 J θ) := by
    rw [hg1, Matrix.transpose_reindex, reindex_mul', reindex_mul', cmp_unit σ J θ hθ g]
  have hJ' : IsUnit (Matrix.reindex e e (jm1 J θ)).det := by
    rwa [Matrix.det_reindex_self]
  rw [← frame_mem_sG g1 Q _ _ hJ' hU (fun b => pr1 θ (ratV (F := F) R (F0 P b)) ∘ e.symm)
    (fun b => pr2 θ (ratV (F := F) R (F0 P b)) ∘ e.symm) l hl hy1 hy2, hg1]
  exact and_congr (flagC_reindex_iff e _ _).symm (flagC_reindex_iff e _ _).symm

end MassDataIdxStIm
end
end

