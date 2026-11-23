module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilRepresentationContinuous
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReAddIm
section
noncomputable section

open Formalism.BasicNotions.TH Matrix
open scoped InnerProductSpace

namespace GlobalTheory.RealPartAdjointAction

variable {r s : ℕ}

theorem J_ct : (Jm r s)ᴴ = Jm r s := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem J_sq : Jm r s * Jm r s = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem J_J (X : Mat r s) : Jm r s * (Jm r s * X) = X := by
  rw [← Matrix.mul_assoc, J_sq, Matrix.one_mul]

def reP (Z : Mat r s) : Mat r s := (1 / 2 : ℂ) • (Z - adjZ Z)

def imaginary (Z : Mat r s) : Mat r s := (-Complex.I / 2 : ℂ) • (Z + adjZ Z)

theorem adj_ct_J (Z : Mat r s) : (adjZ Z)ᴴ * Jm r s = Jm r s * Z := by
  simp only [adjZ, Matrix.conjTranspose_mul, J_ct, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, J_sq,
    Matrix.mul_one]

theorem J_adj (Z : Mat r s) : Jm r s * adjZ Z = Zᴴ * Jm r s := by
  simp only [adjZ, Matrix.mul_assoc, J_J]

theorem adj_adj (Z : Mat r s) : adjZ (adjZ Z) = Z := by
  have h : adjZ (adjZ Z) = Jm r s * ((adjZ Z)ᴴ * Jm r s) := Matrix.mul_assoc _ _ _
  rw [h, adj_ct_J, J_J]

theorem realPart_mem_unitaryLieAlgebra (Z : Mat r s) : reP Z ∈ upq r s := by
  have h : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [upq, reP, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, adj_ct_J, J_adj, h]
  module

theorem imaginaryPart_mem_unitaryLieAlgebra (Z : Mat r s) : imaginary Z ∈ upq r s := by
  have h : star (-Complex.I / 2 : ℂ) = Complex.I / 2 := by simp
  simp only [upq, imaginary, Set.mem_setOf_eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, adj_ct_J, J_adj, h]
  module

theorem re_add_im (Z : Mat r s) : reP Z + Complex.I • imaginary Z = Z := by
  have h : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I, neg_neg]
  rw [reP, imaginary, smul_smul, h]
  module

theorem realPart_adjoint (Z : Mat r s) : reP (adjZ Z) = (-1 : ℝ) • reP Z := by
  rw [reP, reP, adj_adj, neg_one_smul, ← smul_neg, neg_sub]

theorem imaginaryPart_adjoint (Z : Mat r s) : imaginary (adjZ Z) = imaginary Z := by
  rw [imaginary, imaginary, adj_adj, add_comm]

section Main

variable {W U I : Type} [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  (a : Mat r s →ₗ[ℂ] Module.End ℂ W) (b : Mat r s → Module.End ℂ U) (j : I → W →ₗ[ℂ] U)

def cx (Z : Mat r s) : Module.End ℂ U := b (reP Z) + Complex.I • b (imaginary Z)

def Sp : Submodule ℂ U := Submodule.span ℂ {y : U | ∃ (i : I) (P : W), y = j i P}

def jS (i : I) : W →ₗ[ℂ] Sp j := (j i).codRestrict (Sp j) fun P => Submodule.subset_span ⟨i, P, rfl⟩

theorem gen (K : Submodule ℂ (Sp j)) (h : ∀ i P, jS j i P ∈ K) (y : Sp j) : y ∈ K := by
  obtain ⟨y, hy⟩ := y
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, P, rfl⟩ := hx
    exact h i P
  | zero => exact K.zero_mem
  | add x y hx hy ihx ihy => exact K.add_mem ihx ihy
  | smul c x hx ih => exact K.smul_mem c ih

theorem ext_gen {N : Type} [AddCommGroup N] [Module ℂ N] (f g : Sp j →ₗ[ℂ] N)
    (h : ∀ i P, f (jS j i P) = g (jS j i P)) : f = g :=
  LinearMap.ext fun y => gen j (LinearMap.eqLocus f g) h y

def Eqv : Prop := ∀ i, ∀ Z ∈ upq r s, ∀ P, j i (a Z P) = b Z (j i P)

variable {a b j}

theorem cx_gen (h : Eqv a b j) (Z : Mat r s) (i : I) (P : W) : cx b Z (j i P) = j i (a Z P) := by
  conv_rhs => rw [← re_add_im Z]
  simp only [cx, map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, h i _ (realPart_mem_unitaryLieAlgebra Z), h i _ (imaginaryPart_mem_unitaryLieAlgebra Z)]

theorem stab (f : Module.End ℂ U) (Z : Mat r s) (hf : ∀ i P, f (j i P) = j i (a Z P)) :
    ∀ y ∈ Sp j, f y ∈ Sp j := by
  have : Sp j ≤ (Sp j).comap f := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, P, rfl⟩
    show f (j i P) ∈ Sp j
    rw [hf]
    exact Submodule.subset_span ⟨i, _, rfl⟩
  exact fun y hy => this hy

def op (h : Eqv a b j) (Z : Mat r s) : Module.End ℂ (Sp j) := (cx b Z).restrict (stab _ Z (cx_gen h Z))

theorem op_gen (h : Eqv a b j) (Z : Mat r s) (i : I) (P : W) : op h Z (jS j i P) = jS j i (a Z P) :=
  Subtype.ext (cx_gen h Z i P)

def act (h : Eqv a b j) : Mat r s →ₗ[ℂ] Module.End ℂ (Sp j) where
  toFun := op h
  map_add' X Y := ext_gen j _ _ fun i P => by
    simp only [LinearMap.add_apply, op_gen, map_add (f := _)]
  map_smul' c X := ext_gen j _ _ fun i P => by
    simp only [LinearMap.smul_apply, op_gen, map_smul, RingHom.id_apply]

theorem act_gen (h : Eqv a b j) (Z : Mat r s) (i : I) (P : W) : act h Z (jS j i P) = jS j i (a Z P) :=
  op_gen h Z i P

def finPart {V : Type} [AddCommGroup V] [Module ℂ V] (c : Mat r s →ₗ[ℂ] Module.End ℂ V) : Submodule ℂ V where
  carrier := {v | ∃ F : Submodule ℂ V, FiniteDimensional ℂ F ∧ v ∈ F ∧ KStable c F}
  zero_mem' := ⟨⊥, inferInstance, Submodule.zero_mem _, fun X _ w hw => by
    rw [(Submodule.mem_bot ℂ).1 hw, map_zero]; exact Submodule.zero_mem _⟩
  add_mem' := by
    rintro x y ⟨F, hF, hx, kF⟩ ⟨G, hG, hy, kG⟩
    refine ⟨F ⊔ G, inferInstance, Submodule.add_mem_sup hx hy, fun X hX w hw => ?_⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hw
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (kF X hX u hu) (kG X hX v hv)
  smul_mem' := by
    rintro t x ⟨F, hF, hx, kF⟩
    exact ⟨F, hF, F.smul_mem t hx, kF⟩

def spanMod (ha : GlobalTheory.ArchRec.IsGK a) (h : Eqv a b j) : GKMod r s where
  V := Sp j
  act := act h
  lie X Y := ext_gen j _ _ fun i P => by
    simp only [act_gen, ha.1 X Y, LinearMap.sub_apply, Module.End.mul_apply, map_sub (jS j i)]
  kfin := gen j (finPart (act h)) fun i P => by
    obtain ⟨F, hF, hP, kF⟩ := ha.2.1 P
    refine ⟨F.map (jS j i), inferInstance, Submodule.mem_map_of_mem hP, ?_⟩
    rintro X hX _ ⟨w, hw, rfl⟩
    rw [act_gen]
    exact Submodule.mem_map_of_mem (kF X hX w hw)
  wts := gen j _ fun i P => by
    have hle : (⨆ μ : Ix r s → ℚ, wtSub a μ) ≤ (⨆ μ : Ix r s → ℚ, wtSub (act h) μ).comap (jS j i) := by
      refine iSup_le fun μ w hw => Submodule.mem_iSup_of_mem μ ?_
      simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hw ⊢
      intro c
      rw [act_gen, ← map_smul, ← map_sub, hw c, map_zero]
    exact hle (ha.2.2 P)

theorem cx_adj (hb : GlobalTheory.ArchRec.IsUAct b) (Z : Mat r s) (x y : U) :
    ⟪cx b Z x, y⟫_ℂ = ⟪x, cx b (adjZ Z) y⟫_ℂ := by
  simp only [cx, realPart_adjoint, imaginaryPart_adjoint, hb.smul _ _ (realPart_mem_unitaryLieAlgebra Z), LinearMap.add_apply, LinearMap.smul_apply,
    inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hb.skew _ (realPart_mem_unitaryLieAlgebra Z),
    hb.skew _ (imaginaryPart_mem_unitaryLieAlgebra Z), Complex.conj_I]
  push_cast
  ring

def spanUMod (ha : GlobalTheory.ArchRec.IsGK a) (hb : GlobalTheory.ArchRec.IsUAct b) (h : Eqv a b j) : UGKMod r s where
  M := spanMod ha h
  ip := innerₛₗ ℂ (E := Sp j)
  herm x y := inner_conj_symm (𝕜 := ℂ) (E := Sp j) y x
  pos x hx := (re_inner_self_pos (𝕜 := ℂ) (E := Sp j)).2 hx
  adj Z x y := cx_adj hb Z (x : Sp j).1 (y : Sp j).1

theorem act_real (h : Eqv a b j) (Z : Mat r s) (hZ : Z ∈ upq r s) (y : Sp j) : (act h Z y : U) = b Z y := by
  have := ext_gen j ((Sp j).subtype ∘ₗ act h Z) (b Z ∘ₗ (Sp j).subtype) fun i P => by
    rw [LinearMap.comp_apply, act_gen]
    exact h i Z hZ P
  exact LinearMap.congr_fun this y

end Main

theorem main : ∀ (r s : ℕ) (W U I : Type) [inst : AddCommGroup W] [inst_1 : Module ℂ W] [inst_2 : NormedAddCommGroup U] [inst_3 : InnerProductSpace ℂ U] (a : Formalism.BasicNotions.TH.Mat r s →ₗ[ℂ] Module.End ℂ W) (b : Formalism.BasicNotions.TH.Mat r s → Module.End ℂ U) (j : I → W →ₗ[ℂ] U), GlobalTheory.ArchRec.IsGK a → GlobalTheory.ArchRec.IsUAct b → (∀ (i : I), ∀ Z ∈ Formalism.BasicNotions.TH.upq r s, ∀ (P : W), (j i : W → U) (((a : Formalism.BasicNotions.TH.Mat r s → Module.End ℂ W) Z : W → W) P) = (b Z : U → U) ((j i : W → U) P)) → ∃ (MM : Formalism.BasicNotions.TH.UGKMod r s) (inc : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) →ₗ[ℂ] U), Function.Injective (⇑inc : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) → U) ∧ LinearMap.range inc = Submodule.span ℂ {y : U | ∃ (i : I) (P : W), y = (j i : W → U) P} ∧ ∀ Z ∈ Formalism.BasicNotions.TH.upq r s, ∀ (y : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM)), (inc : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) → U) (((Formalism.BasicNotions.TH.GKMod.act (Formalism.BasicNotions.TH.UGKMod.M MM) : Formalism.BasicNotions.TH.Mat r s → Module.End ℂ (Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM))) Z : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) → Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM)) y) = (b Z : U → U) ((inc : Formalism.BasicNotions.TH.GKMod.V (Formalism.BasicNotions.TH.UGKMod.M MM) → U) y) := by
  intro r s W U I _ _ _ _ a b j ha hb h
  exact ⟨spanUMod ha hb h, (Sp j).subtype, (Sp j).injective_subtype, (Sp j).range_subtype,
    fun Z hZ y => act_real h Z hZ y⟩

end GlobalTheory.RealPartAdjointAction

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealIntertwinerContractionValuesKFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt GlobalTheory.Chain.RealLine
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.RealLineKFin

private theorem eq_of_inner_eq_on_dense {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {E : Submodule ℂ H} (hE : Dense (E : Set H)) {v w : H}
    (h : ∀ y : E, ⟪v, (y : H)⟫_ℂ = ⟪w, (y : H)⟫_ℂ) : v = w := by
  have hclosed : IsClosed {x : H | ⟪v - w, x⟫_ℂ = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hsub : (E : Set H) ⊆ {x : H | ⟪v - w, x⟫_ℂ = 0} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, inner_sub_left, h ⟨x, hx⟩, sub_self]
  have hall := closure_minimal hsub hclosed
  rw [hE.closure_eq] at hall
  have hz : ⟪v - w, v - w⟫_ℂ = 0 := hall (Set.mem_univ _)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

theorem exists_riesz {H P : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [AddCommGroup P] [Module ℂ P] {E : Submodule ℂ H} (hE : Dense (E : Set H)) (F : P →ₗ[ℂ] E →ₗ[ℂ] ℂ)
    (hF : ∀ φ, ∃ c : ℝ, ∀ y : E, ‖F φ y‖ ≤ c * ‖(y : H)‖) :
    ∃ b : P →ₛₗ[starRingEnd ℂ] H, ∀ φ (y : E), F φ y = ⟪b φ, (y : H)⟫_ℂ := by
  have hrep : ∀ φ, ∃ v : H, ∀ y : E, F φ y = ⟪v, (y : H)⟫_ℂ := by
    intro φ
    obtain ⟨c, hc⟩ := hF φ
    have hden : DenseRange (E.subtype : E →ₗ[ℂ] H) := by
      simpa using hE.denseRange_val
    let g : H →L[ℂ] ℂ := (F φ).extendOfNorm E.subtype
    refine ⟨(InnerProductSpace.toDual ℂ H).symm g, fun y => ?_⟩
    rw [InnerProductSpace.toDual_symm_apply]
    have := LinearMap.extendOfNorm_eq (f := F φ) hden ⟨c, fun y => by simpa using hc y⟩ y
    simpa [g] using this.symm
  choose v hv using hrep
  refine ⟨{ toFun := v, map_add' := ?_, map_smul' := ?_ }, hv⟩
  · intro φ ψ
    refine eq_of_inner_eq_on_dense hE fun y => ?_
    rw [← hv, inner_add_left, ← hv, ← hv, map_add (f := _), LinearMap.add_apply]
  · intro c φ
    refine eq_of_inner_eq_on_dense hE fun y => ?_
    rw [← hv, inner_smul_left, ← hv, map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp

theorem finite_map {H P : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup P] [Module ℂ P]
    (b : P →ₛₗ[starRingEnd ℂ] H) (T : Submodule ℂ P) [FiniteDimensional ℂ T] : FiniteDimensional ℂ (T.map b) := by
  have hT : (T : Submodule ℂ P).FG := Module.Finite.iff_fg.mp inferInstance
  exact Module.Finite.iff_fg.mpr (hT.map b)

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem sm_stable (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.MainNotions.S.UJset (M.ε τ)) {y : M.H τ} (hy : y ∈ M.sm τ) : M.σ τ g y ∈ M.sm τ := Submodule.subset_span (GlobalTheory.ConjExt.smooth_translate M τ ⟨y, hy⟩ hg)

theorem dense_sm (M : DSModel V S) (τ : D.what₂.Tau) : Dense (M.sm τ : Set (M.H τ)) := GlobalTheory.LowTypeDetermined.dense_of_irred (M.ds τ).2.2.2.1 (fun _ hg _ hy => sm_stable M τ hg hy) (GlobalTheory.GardingVec.sm_ne_bot D V S M τ)

theorem kset_star {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) :
    star k ∈ Formalism.REAL.Kset ε := by
  obtain ⟨hu, hc⟩ := hk
  refine ⟨Matrix.mem_unitaryGroup_iff.mpr (by rw [star_star]; exact Matrix.mem_unitaryGroup_iff'.mp hu), ?_⟩
  have hJ : star (Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε := by
    rw [Matrix.star_eq_conjTranspose]; exact Formalism.REAL.Jm_conjTranspose ε
  calc star k * Formalism.REAL.Jm ε = star (Formalism.REAL.Jm ε * k) := by rw [star_mul, hJ]
    _ = star (k * Formalism.REAL.Jm ε) := by rw [hc]
    _ = Formalism.REAL.Jm ε * star k := by rw [star_mul, hJ]

private theorem mem_UJset_of_mem_Kset_twisted_operators {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Formalism.REAL.Kset ε) : k ∈ Formalism.MainNotions.S.UJset ε := by
  obtain ⟨hu, hc⟩ := hk
  have hkk : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  simp only [Formalism.MainNotions.S.UJset, Set.mem_ofPred_eq, Formalism.REAL.inUJ]
  rw [← Matrix.star_eq_conjTranspose, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, hkk, Matrix.one_mul]

private theorem subst_subst_eq_of_subst_eq_X {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) (y : H) : σ k (σ (star k) y) = y := by
  have hks1 : k * star k = 1 := Matrix.mem_unitaryGroup_iff.mp hk.1
  rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 k (mem_UJset_of_mem_Kset_twisted_operators hk) (star k) (mem_UJset_of_mem_Kset_twisted_operators (kset_star hk)),
    hks1, hσ.1.1]
  rfl

private theorem inner_urep_apply_eq_inner_star_of_mem_Kset {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) (x y : H) :
    ⟪σ k x, y⟫_ℂ = ⟪x, σ (star k) y⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := ⟨(σ k).toLinearMap, hσ.2.1 k (mem_UJset_of_mem_Kset_twisted_operators hk)⟩
  conv_lhs => rw [← subst_subst_eq_of_subst_eq_X hσ hk y]
  exact L.inner_map_map x (σ (star k) y)

theorem kfin : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) (aS aT : ℚ) (A : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] M.H τ), SemiW M M' τ aS aT A → (∀ φ y, Formalism.MainNotions.S.IsKFin (M.ε τ) (M.σ τ) (A φ y)) ∧ ∀ φ u, ∃ b : M'.H τ, Formalism.MainNotions.S.IsKFin (M'.ε τ) (M'.σ τ) b ∧ ∀ y : M'.sm τ, ⟪u, A φ y⟫_ℂ = ⟪b, (y : M'.H τ)⟫_ℂ := by
  intro D V W S S' M M' τ aS aT A hA
  have : CompleteSpace (M'.H τ) := (M'.ds τ).1
  refine ⟨fun φ y => ?_, fun φ u => ?_⟩
  · refine ⟨(MvPolynomial.restrictTotalDegree _ ℂ φ.totalDegree).map (A.flip y), ?_, ⟨φ, ?_, rfl⟩, ?_⟩
    · exact Module.Finite.iff_fg.mpr ((Module.Finite.iff_fg.mp inferInstance).map _)
    · exact (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr le_rfl
    · intro g hg v hv
      obtain ⟨ψ, hψ, rfl⟩ := hv
      obtain ⟨ψ', hdeg, heq⟩ := hA.eqK g hg ψ
      refine ⟨ψ', (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
        (hdeg.trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hψ)), ?_⟩
      simp only [LinearMap.flip_apply, heq y]
  · let F : PolF D W.rank V.rank →ₗ[ℂ] M'.sm τ →ₗ[ℂ] ℂ := A.compr₂ (innerSL ℂ u).toLinearMap
    have hFapp : ∀ ψ y, F ψ y = ⟪u, A ψ y⟫_ℂ := fun ψ y => by simp [F]
    obtain ⟨b, hb⟩ := exists_riesz (dense_sm M' τ) F fun ψ => by
      obtain ⟨c, hc⟩ := hA.bdd ψ u
      exact ⟨c, fun y => by rw [hFapp]; exact hc y⟩
    have hσ := (M'.ds τ).2.2.1
    let T : Submodule ℂ (PolF D W.rank V.rank) := MvPolynomial.restrictTotalDegree _ ℂ φ.totalDegree
    refine ⟨b φ, ⟨T.map b, finite_map b T, ⟨φ, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr le_rfl, rfl⟩, ?_⟩,
      fun y => by rw [← hFapp, hb]⟩
    intro k hk v hv
    obtain ⟨ψ, hψ, rfl⟩ := hv
    obtain ⟨ψ', hdeg, heq⟩ := hA.invK k hk ψ
    have key : M'.σ τ k (b ψ) = b ψ' := by
      refine eq_of_inner_eq_on_dense (dense_sm M' τ) fun y => ?_
      have hmem : M'.σ τ (star k) y ∈ M'.sm τ := sm_stable M' τ (mem_UJset_of_mem_Kset_twisted_operators (kset_star hk)) y.2
      rw [inner_urep_apply_eq_inner_star_of_mem_Kset hσ hk]
      have e1 : F ψ ⟨_, hmem⟩ = ⟪b ψ, M'.σ τ (star k) y⟫_ℂ := hb ψ ⟨_, hmem⟩
      rw [← e1, ← hb ψ' y, hFapp, hFapp, heq ⟨_, hmem⟩ y (subst_subst_eq_of_subst_eq_X hσ hk y).symm]
    rw [key]
    exact ⟨ψ', (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
      (hdeg.trans ((MvPolynomial.mem_restrictTotalDegree _ _ _).mp hψ)), rfl⟩

end GlobalTheory.Chain.RealLineKFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceGroupsActUnitarilyWeaklyOnTheta
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section

namespace GlobalTheory.ThetaL2InnerProduct

open GlobalTheory.OrientedHeis GlobalTheory.Size Filter
open scoped Topology

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

def thetaSpace (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  add_mem' := GlobalTheory.OrientedHeis.theta_add
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  smul_mem' := fun a _ hf => GlobalTheory.OrientedHeis.theta_smul a hf

theorem ipTh_eq (f f' : WO S T → ℂ) : ipTh μ 𝓕 f f' = GlobalTheory.Ker.ipO μ 𝓕 f f' := rfl

theorem bound_near (hω : IsWeilDatumO ψ S T χS χT ω) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (p₀ : GA D S × GA D T) : ∃ C : ℝ, ∀ᶠ p in 𝓝 p₀, ∀ w, ‖ω p f w‖ ≤ C := by
  obtain ⟨K, hK, hKγ⟩ := (GlobalTheory.AdelicMatrixLattice.lattice D T S).2.2.2.2.2
  have hcont : Continuous fun q : (GA D S × GA D T) × WO S T => ω q.1 f q.2 :=
    GlobalTheory.ThetaJointCont.continuous_om_oriented hω hf
  have hc0 : ContinuousOn (fun w : WO S T => ω p₀ f w) K :=
    (hcont.comp (by fun_prop : Continuous fun w : WO S T => (p₀, w))).continuousOn
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc0
  refine ⟨M + 1, ?_⟩
  have hev : ∀ᶠ p in 𝓝 p₀, ∀ y ∈ K, ‖ω p f y‖ < M + 1 := by
    refine hK.eventually_forall_of_forall_eventually fun y hy => ?_
    have hlt : ‖ω p₀ f y‖ < M + 1 := lt_of_le_of_lt (hM y hy) (lt_add_one M)
    exact hcont.norm.continuousAt.eventually_lt continuousAt_const hlt
  filter_upwards [hev] with p hp w
  obtain ⟨γ, hγ, hγK⟩ := hKγ w
  rw [← theta_norm_periodic hω.std (hω.om_pres p f hf) γ hγ w]
  exact (hp _ hγK).le

theorem continuousOn_ip (hω : IsWeilDatumO ψ S T χS χT ω) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {X : Type} [TopologicalSpace X] [FirstCountableTopology X]
    {γ : X → GA D S × GA D T} {U : Set X} (hγ : ContinuousOn γ U) {F E : WO S T → ℂ}
    (hF : IsThetaFunO ψ S T F) (hE : IsThetaFunO ψ S T E) :
    ContinuousOn (fun x => ipTh μ 𝓕 (ω (γ x) F) E) U := by
  intro x₀ hx₀
  obtain ⟨C, hC⟩ := bound_near hω hF (γ x₀)
  obtain ⟨CE, hCE⟩ := theta_bounded hω.std hE
  have hfin : μ 𝓕 ≠ ⊤ := (measure_dom hμ h𝓕).2
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  unfold ipTh
  refine continuousWithinAt_of_dominated (bound := fun _ => C * CE) ?_ ?_ (integrable_const _) ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    exact (integrableOn_mul_conj hω.std hμ h𝓕 (hω.om_pres (γ x) F hF) hE).aestronglyMeasurable
  · have ht : Tendsto γ (𝓝[U] x₀) (𝓝 (γ x₀)) := hγ x₀ hx₀
    filter_upwards [ht.eventually hC] with x hx
    refine Filter.Eventually.of_forall fun w => ?_
    rw [norm_mul, norm_star]
    exact mul_le_mul (hx w) (hCE w) (norm_nonneg _) ((norm_nonneg _).trans (hx w))
  · refine Filter.Eventually.of_forall fun w => ?_
    exact ((hω.om_cont F hF w).continuousAt.comp_continuousWithinAt (hγ x₀ hx₀)).mul continuousWithinAt_const

theorem weaklyContinuous_unitaryAction_of_realUnitaryHom (hω : IsWeilDatumO ψ S T χS χT ω) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) {n : ℕ} {ι : Type} (G : Mn n) (γ : Mn n → GA D S × GA D T)
    (h1 : γ 1 = 1) (hmul : ∀ g ∈ Formalism.QuantumDeterminants.UH G, ∀ g' ∈ Formalism.QuantumDeterminants.UH G, γ (g * g') = γ g * γ g')
    (hc : ContinuousOn γ (Formalism.QuantumDeterminants.UH G)) (pt : MvPolynomial ι ℂ →ₗ[ℂ] (WO S T → ℂ))
    (hpt : ∀ P, IsThetaFunO ψ S T (pt P))
    (hd : ∀ X : Mn n, Xᴴ * G + G * X = 0 → ∀ P, ∃ F', DerAll ψ ω (fun t => γ (NormedSpace.exp (t • X))) (pt P) F') :
    L2UnitaryRepresentationData G (fun g F => ω (γ g) F) pt (ipTh μ 𝓕) (thetaSpace ψ S T) := {
  mem := hpt
  pt_lin := fun z P Q => by rw [map_add (f := _), map_smul]
  ip_lin := fun z F hF F' hF' E hE => by
    rw [ipTh_eq, ipTh_eq, ipTh_eq, ipO_add_left hω.std hμ h𝓕 ((thetaSpace ψ S T).smul_mem z hF) hF' hE,
      ipO_smul_left]
  ip_symm := fun F _ E _ => by rw [ipTh_eq, ipTh_eq, ipO_conj]
  ip_pos := fun F hF hne => by
    have htheta : IsThetaFunO ψ S T F := hF
    have hc : Continuous F := htheta.cont
    have h0 : GlobalTheory.Ker.ipO μ 𝓕 F F ≠ 0 := fun h => hne ((ipO_self_eq_zero_iff hω.std hμ h𝓕 hF).1 h)
    rw [ipO_self, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hc] at h0
    rw [ipTh_eq, ipO_self, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hc, Complex.ofReal_re]
    exact lt_of_le_of_ne (sq_nonneg _) (fun h => h0 (by rw [← h]; simp))
  stable := fun g _ F hF => hω.om_pres _ F hF
  lin := fun g _ z F _ F' _ => by simp only [map_add (f := _), map_smul]
  one := fun F _ => by
    show ω (γ 1) F = F
    rw [h1, map_one]
    rfl
  mul := fun g hg g' hg' F _ => by
    show ω (γ (g * g')) F = ω (γ g) (ω (γ g') F)
    rw [hmul g hg g' hg', map_mul]
    rfl
  unit := fun g _ F hF E hE => by
    show ipTh μ 𝓕 (ω (γ g) F) (ω (γ g) E) = ipTh μ 𝓕 F E
    rw [ipTh_eq, ipTh_eq, ipO_om hω hμ h𝓕 hF hE (γ g)]
  cont := fun F hF E hE => by
    have : FirstCountableTopology (Mn n) :=
      inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
    exact continuousOn_ip hω hμ h𝓕 hc hF hE
  der := fun X hX P P' hPP' E hE => by
    obtain ⟨F', hF'1, hF'2⟩ := hd X hX P
    have heq : F' = pt P' := by
      funext z
      have hz := hF'1 1 z
      simp only [one_mul, map_one, one_apply_eq_self] at hz
      exact hz.unique (hPP' z)
    have hder := hF'2 μ 𝓕 hμ h𝓕 E hE
    rw [heq] at hder
    exact hder }

theorem exists_l2_unitary_theta_of_fundamentalDomain : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ (frS : Mn S.rank) (εS : Fin S.rank → Bool) (frT : Mn T.rank) (εT : Fin T.rank → Bool) (aS aT : ℚ) (pt : LPol T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)), (∀ P, IsThetaFunO ψ S T (pt P)) → LieAt ψ θ τ ω εS frS εT frT aS aT pt → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∃ Θ, L2UnitaryRepresentationData (gramAt D S τ) (actSrc θ ω τ) pt (ipTh μ 𝓕) Θ ∧ L2UnitaryRepresentationData (gramAt D T τ) (actTgt θ ω τ) pt (ipTh μ 𝓕) Θ := by
  intro D ψ θ S T χS χT ω τ hθ hω frS εS frT εT aS aT pt hpt hL μ 𝓕 hμ h𝓕
  refine ⟨thetaSpace ψ S T, ?_, ?_⟩
  · have hcS := GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ S τ
    exact weaklyContinuous_unitaryAction_of_realUnitaryHom hω hμ h𝓕 (gramAt D S τ) (fun g => (atTau θ S τ g, (1 : GA D T)))
      (by rw [GlobalTheory.PointAtPlaceHom.atTau_one hθ S τ]; rfl)
      (fun g hg g' hg' => by
        rw [GlobalTheory.PointAtPlaceHom.atTau_mul hθ S τ hg hg', Prod.mk_mul_mk, one_mul])
      (by fun_prop) pt hpt (fun X hX P => ⟨_, hL.1 X hX P⟩)
  · have hcT := GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ T τ
    exact weaklyContinuous_unitaryAction_of_realUnitaryHom hω hμ h𝓕 (gramAt D T τ) (fun h => ((1 : GA D S), atTau θ T τ h))
      (by rw [GlobalTheory.PointAtPlaceHom.atTau_one hθ T τ]; rfl)
      (fun h hh h' hh' => by
        rw [GlobalTheory.PointAtPlaceHom.atTau_mul hθ T τ hh hh', Prod.mk_mul_mk, one_mul])
      (by fun_prop) pt hpt (fun Y hY P => ⟨_, hL.2 Y hY P⟩)

end GlobalTheory.ThetaL2InnerProduct

end
end

