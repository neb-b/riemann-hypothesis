module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsLocalizedModuleResBasicOpenOfQcqs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalRingCardinality.HostCls
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import GroundTheory.GlobalFields.LocalAtPlace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyTensorLineBundleGlobalSectionsEquiv
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

noncomputable section

namespace GlobalTheory.SecTensor

open TensorProduct

theorem isLocalizedModule_mulTensor {R M N B : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [CommRing B] [Algebra R B] (r : R) [IsLocalization.Away r B]
    (c : M →ₗ[R] B) (d : N →ₗ[R] B) [IsLocalizedModule.Away r c] [IsLocalizedModule.Away r d] :
    IsLocalizedModule.Away r (TensorProduct.lift ((LinearMap.mul R B).compl₁₂ c d)) := by
  have hc : IsBaseChange B c := (isLocalizedModule_iff_isBaseChange (.powers r) B c).1 inferInstance
  have hd : IsBaseChange B d := (isLocalizedModule_iff_isBaseChange (.powers r) B d).1 inferInstance
  show IsLocalizedModule (.powers r) _
  rw [isLocalizedModule_iff_isBaseChange (.powers r) B]
  have h1 := isBaseChange_tensorProduct_map (R := R) (P := N) B hc
  have h2 := h1.comp (IsBaseChange.ofEquiv hd.equiv)
  have heq : TensorProduct.lift ((LinearMap.mul R B).compl₁₂ c d) =
      (hd.equiv.toLinearMap.restrictScalars R) ∘ₗ
        (AlgebraTensorModule.map c (LinearMap.id (R := R) (M := N))).restrictScalars R := by
    ext m n
    simp [IsBaseChange.equiv_tmul]
  rw [heq]
  exact h2

theorem bijective_of_mulTensor {R M N P : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P] (μ : M ⊗[R] N →ₗ[R] P)
    (s : Set R) (hs : Ideal.span s = ⊤) (B : s → Type*) [∀ r, CommRing (B r)]
    [∀ r, Algebra R (B r)] [∀ r : s, IsLocalization.Away r.1 (B r)]
    (c : ∀ r, M →ₗ[R] B r) (d : ∀ r, N →ₗ[R] B r) (e : ∀ r, P →ₗ[R] B r)
    [∀ r : s, IsLocalizedModule.Away r.1 (c r)] [∀ r : s, IsLocalizedModule.Away r.1 (d r)]
    [∀ r : s, IsLocalizedModule.Away r.1 (e r)]
    (h : ∀ r m n, e r (μ (m ⊗ₜ n)) = c r m * d r n) : Function.Bijective μ := by
  have (r : s) := isLocalizedModule_mulTensor r.1 (c r) (d r)
  refine bijective_of_isLocalized_span s hs (fun r => B r)
    (fun r => TensorProduct.lift ((LinearMap.mul R (B r)).compl₁₂ (c r) (d r))) (fun r => B r) e μ
    fun r => ?_
  have : IsLocalizedModule.map (.powers r.1)
      (TensorProduct.lift ((LinearMap.mul R (B r)).compl₁₂ (c r) (d r))) (e r) μ = LinearMap.id := by
    apply IsLocalizedModule.linearMap_ext (.powers r.1)
      (TensorProduct.lift ((LinearMap.mul R (B r)).compl₁₂ (c r) (d r))) (e r)
    rw [IsLocalizedModule.map_comp]
    ext m n
    simp [h]
  rw [this]
  exact Function.bijective_id

end GlobalTheory.SecTensor

namespace GlobalTheory.SecTensor

open TensorProduct GlobalTheory.LB

variable {T : Scheme.{0}}

def mulFun (A B : LB T) (s : LB.Sec A) (t : LB.Sec B) (p : A.ι × B.ι) :
    Γ(T, A.U p.1 ⊓ B.U p.2) :=
  resG T (inf_le_left : A.U p.1 ⊓ B.U p.2 ≤ A.U p.1) (s.f p.1) *
    resG T (inf_le_right : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2) (t.f p.2)

def mulSec (A B : LB T) (s : LB.Sec A) (t : LB.Sec B) : LB.Sec (CechPic.tens A B) where
  f := mulFun A B s t
  compat := fun (p q : A.ι × B.ι) => by
    unfold CechPic.tens
    change resG T _ (_ * _) = _ * resG T _ (_ * _)
    simp only [map_mul, resG_resG]
    rw [sec_rel s p.1 q.1 (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
        (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)),
      sec_rel t p.2 q.2 (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))]
    simp only [Units.val_mul, val_res, resG_resG]
    ring

def mulBil (A B : LB T) :
    LB.Sec A →ₗ[Γ(T, ⊤)] LB.Sec B →ₗ[Γ(T, ⊤)] LB.Sec (CechPic.tens A B) :=
  LinearMap.mk₂ Γ(T, ⊤) (mulSec A B)
    (fun s s' t => f_injective (show mulFun A B (s + s') t = mulFun A B s t + mulFun A B s' t from
      funext fun p => by simp only [mulFun, add_f, map_add (f := _), add_mul, Pi.add_apply]))
    (fun a s t => f_injective (show mulFun A B (a • s) t =
      fun (p : A.ι × B.ι) => resG T (le_top : A.U p.1 ⊓ B.U p.2 ≤ ⊤) a * mulFun A B s t p
      from funext fun p => by simp only [mulFun, smul_f, map_mul, resG_resG]; ring))
    (fun s t t' => f_injective (show mulFun A B s (t + t') = mulFun A B s t + mulFun A B s t' from
      funext fun p => by simp only [mulFun, add_f, map_add (f := _), mul_add, Pi.add_apply]))
    (fun a s t => f_injective (show mulFun A B s (a • t) =
      fun (p : A.ι × B.ι) => resG T (le_top : A.U p.1 ⊓ B.U p.2 ≤ ⊤) a * mulFun A B s t p
      from funext fun p => by simp only [mulFun, smul_f, map_mul, resG_resG]; ring))

def chartLoc (L : LB T) (r : Γ(T, ⊤)) (i : L.ι) (h : T.basicOpen r ≤ L.U i) :
    LB.Sec L →ₗ[Γ(T, ⊤)] Γ(T, T.basicOpen r) where
  toFun s := resG T h (s.f i)
  map_add' s t := by simp only [add_f, map_add (f := _)]
  map_smul' a s := by
    simp only [smul_f, map_mul, resG_resG, RingHom.id_apply, Algebra.smul_def]
    rfl

end GlobalTheory.SecTensor

namespace GlobalTheory.SecTensor

open TensorProduct GlobalTheory.LB

variable {T : Scheme.{0}}

def chartEquivTop (L : LB T) (hL : L.IsLB) (r : Γ(T, ⊤)) (i : L.ι) (h : T.basicOpen r ≤ L.U i) :
    AbLaw.SecOn L (T.basicOpen r) ≃ₗ[Γ(T, ⊤)] Γ(T, T.basicOpen r) where
  toFun s := resG T (le_inf le_rfl h) (coord s i)
  invFun a := a • (toMod L).presheaf.map (homOfLE h).op (chartSec hL i)
  map_add' s t := by simp only [coord_add, map_add (f := _)]
  map_smul' a s := by
    rw [AbLaw.SecOn.smul_basicOpen_def, Algebra.smul_def]
    simp only [coord_smul, map_mul, resG_resG, RingHom.id_apply]
    rfl
  left_inv s := Subtype.ext (funext fun j => by
    change coord (_ • _) j = coord s j
    simp only [coord_smul, coord_map, coord_chartSec, resG_resG]
    rw [mul_comm, ← coord_rel s j i le_rfl, resG_self])
  right_inv a := by
    simp only [coord_smul, coord_map, coord_chartSec, resG_resG, resG_self,
      resG_g_self hL, map_one, mul_one]

theorem isLocalizedModule_chartLoc [IsAffine T] (L : LB T) (hL : L.IsLB) (r : Γ(T, ⊤)) (i : L.ι)
    (h : T.basicOpen r ≤ L.U i) : IsLocalizedModule.Away r (chartLoc L r i h) := by
  haveI := AbLaw.SecOn.isLocalizedModule_resBasicOpen hL (isAffineOpen_top T) r
  haveI := IsLocalizedModule.of_linearEquiv (S := .powers r) (f := AbLaw.SecOn.resBasicOpen L r)
    (chartEquivTop L hL r i h)
  let toTop : LB.Sec L →ₗ[Γ(T, ⊤)] AbLaw.SecOn L ⊤ :=
    { toFun := fun s => ofSec s ⊤
      map_add' := fun s t => Subtype.ext (funext fun i => by
        change coord (ofSec (s + t) ⊤) i = coord (ofSec s ⊤ + ofSec t ⊤) i
        simp only [coord_ofSec, coord_add, add_f, map_add (f := _)])
      map_smul' := fun a s => Subtype.ext (funext fun i => by
        change coord (ofSec (a • s) ⊤) i = coord (a • ofSec s ⊤) i
        simp only [coord_ofSec, coord_smul, smul_f, map_mul, resG_resG]) }
  let topEquiv := LinearEquiv.ofBijective toTop (AbLaw.SecOn.ofSec_bijective (M := L) rfl)
  haveI := IsLocalizedModule.of_linearEquiv_right (S := .powers r)
    (f := (chartEquivTop L hL r i h).toLinearMap ∘ₗ AbLaw.SecOn.resBasicOpen L r)
    topEquiv
  have e : chartLoc L r i h = ((chartEquivTop L hL r i h).toLinearMap ∘ₗ
      AbLaw.SecOn.resBasicOpen L r) ∘ₗ topEquiv.toLinearMap := by
    ext s
    change resG T h (s.f i) = resG T (le_inf le_rfl h)
      (coord ((toMod L).presheaf.map (homOfLE (T.basicOpen_le r)).op (ofSec s ⊤)) i)
    rw [map_ofSec, coord_ofSec, resG_resG]
  rw [e]
  infer_instance

end GlobalTheory.SecTensor

namespace GlobalTheory.SecTensor

open TensorProduct GlobalTheory.LB

theorem tensorSecEquiv : ∀ (T : Scheme.{0}) [IsAffine T] (A B : LB T), A.IsLB → B.IsLB →
    Nonempty (TensorProduct Γ(T, ⊤) (LB.Sec A) (LB.Sec B) ≃ₗ[Γ(T, ⊤)]
      LB.Sec (GlobalTheory.CechPic.tens A B)) := by
  intro T _ A B hA hB
  let s : Set Γ(T, ⊤) := {f | ∃ i j, T.basicOpen f ≤ A.U i ⊓ B.U j}
  have hs : Ideal.span s = ⊤ := by
    rw [← (isAffineOpen_top T).self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hA.cover.ge (TopologicalSpace.Opens.mem_top x))
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (hB.cover.ge (TopologicalSpace.Opens.mem_top x))
    obtain ⟨f, hf, hxf⟩ := (isAffineOpen_top T).exists_basicOpen_le (V := A.U i ⊓ B.U j) ⟨x, hi, hj⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, i, j, hf⟩, hxf⟩
  have (r : s) := (isAffineOpen_top T).isLocalization_basicOpen r.1
  let i (r : s) : A.ι := r.2.choose
  let j (r : s) : B.ι := r.2.choose_spec.choose
  have hij (r : s) : T.basicOpen r.1 ≤ A.U (i r) ⊓ B.U (j r) := r.2.choose_spec.choose_spec
  have (r : s) := isLocalizedModule_chartLoc A hA r.1 (i r) ((hij r).trans inf_le_left)
  have (r : s) := isLocalizedModule_chartLoc B hB r.1 (j r) ((hij r).trans inf_le_right)
  have (r : s) := isLocalizedModule_chartLoc (CechPic.tens A B) (CechPic.isLB_tens hA hB) r.1
    ((i r, j r) : A.ι × B.ι) (hij r)
  refine ⟨LinearEquiv.ofBijective (TensorProduct.lift (mulBil A B))
    (bijective_of_mulTensor _ s hs (fun r => Γ(T, T.basicOpen r.1))
      (fun r => chartLoc A r.1 (i r) ((hij r).trans inf_le_left))
      (fun r => chartLoc B r.1 (j r) ((hij r).trans inf_le_right))
      (fun r => chartLoc (CechPic.tens A B) r.1 ((i r, j r) : A.ι × B.ι) (hij r))
      fun r m n => ?_)⟩
  rw [TensorProduct.lift.tmul]
  change resG T (hij r) (mulFun A B m n (i r, j r)) = _ * _
  simp only [mulFun, map_mul, resG_resG]
  rfl

end GlobalTheory.SecTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneCharacterModulusOneAllEmbeddings
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.CharModOne

open scoped nonZeroDivisors

section General

variable {E : Type} [Field E] [NumberField E]

def intMap (σ : E ≃ₐ[ℚ] E) (r : 𝓞 E) : 𝓞 E :=
  ⟨σ r, (RingOfIntegers.isIntegral_coe r).map (σ.toAlgHom.restrictScalars ℤ)⟩

def cj (σ : E ≃ₐ[ℚ] E) (M : Submodule (𝓞 E) E) : Submodule (𝓞 E) E where
  carrier := {x | σ x ∈ M}
  add_mem' {x y} hx hy := by
    show σ (x + y) ∈ M
    rw [map_add (f := _)]; exact M.add_mem hx hy
  zero_mem' := by
    show σ 0 ∈ M
    rw [map_zero]; exact M.zero_mem
  smul_mem' r x hx := by
    show σ (r • x) ∈ M
    rw [Algebra.smul_def, map_mul]
    have : σ (algebraMap (𝓞 E) E r) * σ x = intMap σ r • σ x := by
      rw [Algebra.smul_def]; rfl
    rw [this]; exact M.smul_mem _ hx

theorem mem_cj (σ : E ≃ₐ[ℚ] E) (M : Submodule (𝓞 E) E) (x : E) : x ∈ cj σ M ↔ σ x ∈ M := Iff.rfl

theorem cj_mono (σ : E ≃ₐ[ℚ] E) {M N : Submodule (𝓞 E) E} (h : M ≤ N) : cj σ M ≤ cj σ N :=
  fun _ hx => h hx

theorem cj_cj (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) (M : Submodule (𝓞 E) E) : cj σ (cj σ M) = M := by
  ext x; rw [mem_cj, mem_cj, hσ]

theorem cj_mul_le (σ : E ≃ₐ[ℚ] E) (M N : Submodule (𝓞 E) E) : cj σ M * cj σ N ≤ cj σ (M * N) := by
  refine Submodule.mul_le.2 fun x hx y hy => ?_
  rw [mem_cj, map_mul]
  exact Submodule.mul_mem_mul hx hy

theorem cj_mul (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) (M N : Submodule (𝓞 E) E) :
    cj σ (M * N) = cj σ M * cj σ N := by
  refine le_antisymm ?_ (cj_mul_le σ M N)
  have h := cj_mono σ (cj_mul_le σ (cj σ M) (cj σ N))
  rwa [cj_cj σ hσ, cj_cj σ hσ, cj_cj σ hσ] at h

theorem one_le_cj_one (σ : E ≃ₐ[ℚ] E) : (1 : Submodule (𝓞 E) E) ≤ cj σ 1 := by
  intro x hx
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨intMap σ y, rfl⟩

theorem cj_one (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) : cj σ (1 : Submodule (𝓞 E) E) = 1 := by
  refine le_antisymm ?_ (one_le_cj_one σ)
  have h := cj_mono σ (one_le_cj_one σ)
  rwa [cj_cj σ hσ] at h

theorem cj_pow (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) (M : Submodule (𝓞 E) E) (n : ℕ) :
    cj σ (M ^ n) = cj σ M ^ n := by
  induction n with
  | zero => simp [cj_one σ hσ]
  | succ n ih => rw [pow_succ, pow_succ, cj_mul σ hσ, ih]

theorem span_le_cj_span (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) (a : E) :
    Submodule.span (𝓞 E) {σ a} ≤ cj σ (Submodule.span (𝓞 E) {a}) := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  exact (mem_cj σ _ _).2 (by rw [hσ]; exact Submodule.mem_span_singleton_self a)

theorem cj_span (σ : E ≃ₐ[ℚ] E) (hσ : ∀ x, σ (σ x) = x) (a : E) :
    cj σ (Submodule.span (𝓞 E) {a}) = Submodule.span (𝓞 E) {σ a} := by
  refine le_antisymm ?_ (span_le_cj_span σ hσ a)
  have h := cj_mono σ (span_le_cj_span σ hσ (σ a))
  rwa [cj_cj σ hσ, hσ] at h

theorem span_mul_span_singleton (a b : E) :
    Submodule.span (𝓞 E) {a} * Submodule.span (𝓞 E) {b} = Submodule.span (𝓞 E) {a * b} := by
  rw [Submodule.span_mul_span, Set.singleton_mul_singleton]

theorem exists_pow_card_eq_span (𝔞 𝔟 : Submodule (𝓞 E) E) (h : 𝔞 * 𝔟 = 1) :
    ∃ a : E, 𝔞 ^ Fintype.card (ClassGroup (𝓞 E)) = Submodule.span (𝓞 E) {a} := by
  have hfa : IsFractional (𝓞 E)⁰ 𝔞 :=
    FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit (Units.mkOfMulEqOne 𝔞 𝔟 h).isUnit)
  have hfb : IsFractional (𝓞 E)⁰ 𝔟 :=
    FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit (Units.mkOfMulEqOne 𝔟 𝔞 (by rw [mul_comm]; exact h)).isUnit)
  let I : FractionalIdeal (𝓞 E)⁰ E := ⟨𝔞, hfa⟩
  let J : FractionalIdeal (𝓞 E)⁰ E := ⟨𝔟, hfb⟩
  have hIJ : I * J = 1 := by
    apply FractionalIdeal.coeToSubmodule_injective
    show ((I * J : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) = ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)
    rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_one]
    exact h
  let U : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mkOfMulEqOne I J hIJ
  have h1 := pow_card_eq_one (x := ClassGroup.mk E U)
  rw [← map_pow, ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨a, ha⟩ := h1.principal
  refine ⟨a, ?_⟩
  rw [← ha, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
  rfl

end General

end GlobalTheory.CharModOne

namespace GlobalTheory.CharModOne

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  letI := D.host.isCMField_hostE
  show D.host.φ₀ (IsCMField.complexConj D.host.E x) = _
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem emb_conj (D : D7) (ρ : D.host.E →+* ℂ) (x : D.host.E) :
    ρ (D.host.conj x) = starRingEnd ℂ (ρ x) :=
  D.host.conjE_apply ρ x

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [emb_conj, emb_conj, Complex.conj_conj]

theorem mod1All_of_isChi : ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 →
    StandardLatticesGL3.Mod1All (χ 𝔞) := by
  intro D χ hχ 𝔞 h𝔞
  set σ := D.host.conj with hσdef
  have hinv : ∀ x, σ (σ x) = x := conj_conj D
  obtain ⟨𝔟, h𝔟, hab⟩ := h𝔞
  have hb : 𝔟 = cj σ 𝔞 := Submodule.ext h𝔟
  have hN1 : ∀ n : ℕ, TaylorLogMetric.N1 D (𝔞 ^ n) := fun n =>
    ⟨𝔟 ^ n, fun x => by rw [hb, ← cj_pow σ hinv]; exact mem_cj σ _ x, by rw [← mul_pow, hab, one_pow]⟩
  have hχpow : ∀ n : ℕ, χ (𝔞 ^ (n + 1)) = χ 𝔞 ^ (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ 𝔞 (n + 1), hχ.1 _ _ (hN1 _) ⟨𝔟, h𝔟, hab⟩, ih]; ring
  obtain ⟨a, ha⟩ := exists_pow_card_eq_span 𝔞 𝔟 hab
  set h := Fintype.card (ClassGroup (𝓞 D.host.E)) with hhdef
  have hpos : 0 < h := Fintype.card_pos
  have hb' : 𝔟 ^ h = Submodule.span (𝓞 D.host.E) {σ a} := by rw [hb, ← cj_pow σ hinv, ha, cj_span σ hinv]
  have h1 : Submodule.span (𝓞 D.host.E) {a} * Submodule.span (𝓞 D.host.E) {σ a} = 1 := by
    rw [← ha, ← hb', ← mul_pow, hab, one_pow]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Submodule.span_singleton_eq_bot.2 rfl, Submodule.bot_mul] at h1
    have : (1 : D.host.E) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := Submodule.mem_one.2 ⟨1, map_one _⟩
    rw [← h1, Submodule.mem_bot] at this
    exact one_ne_zero this
  have hσa0 : σ a ≠ 0 := (map_ne_zero σ).2 ha0
  set z : D.host.E := a / σ a with hzdef
  have hσz : σ z = σ a / a := by rw [hzdef, map_div₀, hinv]
  have hz1 : z * σ z = 1 := by rw [hσz, hzdef]; field_simp
  have hz : z ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, star_eq_conj]
    exact ⟨by rw [mul_comm]; exact hz1, hz1⟩
  have hspan : Submodule.span (𝓞 D.host.E) {z} = 𝔞 ^ (2 * h) := by
    have e1 : z * σ a = a := by rw [hzdef]; field_simp
    calc Submodule.span (𝓞 D.host.E) {z}
        = Submodule.span (𝓞 D.host.E) {z} * (Submodule.span (𝓞 D.host.E) {σ a} * Submodule.span (𝓞 D.host.E) {a}) := by
          rw [mul_comm (Submodule.span (𝓞 D.host.E) {σ a}), h1, mul_one]
      _ = Submodule.span (𝓞 D.host.E) {a} * Submodule.span (𝓞 D.host.E) {a} := by
          rw [← mul_assoc, span_mul_span_singleton, e1]
      _ = 𝔞 ^ (2 * h) := by rw [← ha, two_mul, pow_add]
  have key : χ 𝔞 ^ (2 * h) = ∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ z)⁻¹ := by
    have e := hχ.2 ⟨z, hz⟩
    simp only at e
    rw [hspan] at e
    obtain ⟨k, hk⟩ : ∃ k, 2 * h = k + 1 := ⟨2 * h - 1, by omega⟩
    rw [← e, hk, hχpow]

  have hemb : ∀ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z ∈ TaylorLogMetric.Qbar := fun τ =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).algHom (TaylorLogMetric.embT D τ).toRatAlgHom)
  have hc : (∏ τ : D.what₂.Tau, (TaylorLogMetric.embT D τ z)⁻¹) ∈ TaylorLogMetric.Qbar :=
    prod_mem fun τ _ => inv_mem (hemb τ)
  have hx : χ 𝔞 ∈ TaylorLogMetric.Qbar := by
    rw [mem_algebraicClosure_iff]
    refine IsAlgebraic.of_pow (n := 2 * h) (by omega) ?_
    rw [key]
    exact mem_algebraicClosure_iff.1 hc
  refine ⟨hx, fun ρ => ?_⟩
  have hw : (⟨χ 𝔞, hx⟩ : TaylorLogMetric.Qbar) ^ (2 * h) = ∏ τ : D.what₂.Tau, (⟨TaylorLogMetric.embT D τ z, hemb τ⟩ : TaylorLogMetric.Qbar)⁻¹ := by
    apply Subtype.ext
    push_cast
    exact key
  have hone : ∀ τ : D.what₂.Tau, ‖ρ ⟨TaylorLogMetric.embT D τ z, hemb τ⟩‖ = 1 := by
    intro τ
    let ρ' : D.host.E →+* ℂ := ρ.comp ((TaylorLogMetric.embT D τ).codRestrict TaylorLogMetric.Qbar fun x =>
      mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (TaylorLogMetric.embT D τ).toRatAlgHom))
    have hρ' : ρ' z = ρ ⟨TaylorLogMetric.embT D τ z, hemb τ⟩ := rfl
    have h2 : ρ' z * starRingEnd ℂ (ρ' z) = 1 := by rw [← emb_conj, ← map_mul, hz1, map_one]
    have h3 : ‖ρ' z‖ ^ 2 = 1 := by
      calc ‖ρ' z‖ ^ 2 = ‖ρ' z * starRingEnd ℂ (ρ' z)‖ := by rw [norm_mul, Complex.norm_conj, sq]
        _ = 1 := by rw [h2, norm_one]
    rw [← hρ']
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h3
  have h4 : ‖ρ ⟨χ 𝔞, hx⟩‖ ^ (2 * h) = 1 := by
    rw [← norm_pow, ← map_pow, hw, map_prod, norm_prod]
    simp [map_inv₀, norm_inv, hone]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 h4

end GlobalTheory.CharModOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumDatumNumbersEqHostOfCompatible
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNorms

theorem logDerivLOne_eq_of_prime_eq (D : D7) (N : NumDatum) (hd : N.d = D.host.d) : N.logDerivativeAtOne = TaylorLogMetric.logDerivativeAtOne D := by
  have key : ∀ (a b : ℕ) (ha : a.Prime) (hb : b.Prime), a = b →
      (haveI : Fact a.Prime := ⟨ha⟩
       (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod a)).ringHomComp (Int.castRingHom ℂ))) 1 /
        DirichletCharacter.LFunction ((quadraticChar (ZMod a)).ringHomComp (Int.castRingHom ℂ)) 1).re) =
      (haveI : Fact b.Prime := ⟨hb⟩
       (deriv (DirichletCharacter.LFunction ((quadraticChar (ZMod b)).ringHomComp (Int.castRingHom ℂ))) 1 /
        DirichletCharacter.LFunction ((quadraticChar (ZMod b)).ringHomComp (Int.castRingHom ℂ)) 1).re) := by
    rintro a b ha hb rfl
    rfl
  exact key _ _ N.hyp.2.1 D.host.hyp.2.1 hd

theorem numbers_of_hostTie : ∀ (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X), HostTie N s Pr → N.rd = D.host.rdE ∧ N.v = D.host.v ∧ N.logDerivativeAtOne = TaylorLogMetric.logDerivativeAtOne D ∧ N.logOm = TaylorLogMetric.logOmVal D ∧ TaylorLogMetric.fF D = N.R.f ∧ X.f = N.R.f ∧ Module.finrank ℚ X.E = 2 * N.R.f ∧ |(discr X.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ X.E : ℝ)) = N.rd ∧ TaylorLogMetric.IsCurveIdeal D D.host.ccK := by
  intro D N X s Pr h
  have hrd : N.rd = D.host.rdE := h.rd_eq
  obtain ⟨hR, hq, hd, hcc, -, -, hX, -⟩ := h
  have hv : N.v = D.host.v := by
    rw [NumDatum.v, Host.v, hrd]
  have hL := logDerivLOne_eq_of_prime_eq D N hd
  have hfr : Module.finrank ℚ X.E = Module.finrank ℚ D.host.E :=
    (AlgEquiv.ofRingEquiv (f := s.iE) (fun x => by simp) : X.E ≃ₐ[ℚ] D.host.E).toLinearEquiv.finrank_eq
  have hE : Module.finrank ℚ X.E = 2 * N.R.f := by
    rw [hfr, D.host.finrank_E', hR]
  have htower : Module.finrank ℚ X.F * Module.finrank X.F X.E = Module.finrank ℚ X.E :=
    Module.finrank_mul_finrank ℚ X.F X.E
  refine ⟨hrd, hv, hL, ?_, ?_, ?_, hE, ?_, ?_⟩
  · rw [NumDatum.logOm, TaylorLogMetric.logOmVal, hv, hL]
  · rw [TaylorLogMetric.fF, hR]
  · rw [hX.ok.rankE, hE] at htower
    rw [Fields.f, hX.ok.card_Tau]
    omega
  · rw [hrd, Host.rdE, hfr, discr_eq_discr_of_ringEquiv X.E s.iE]
  · rw [hcc]
    refine ⟨top_ne_bot, ?_⟩
    simp

end GlobalTheory.ColNorms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntegersHenselianFiniteResidue
section
open IsDedekindDomain IsLocalRing

namespace GlobalTheory.IntAdicHensel

theorem henselianLocalRing_and_finite_residueField :
    ∀ (v : HeightOneSpectrum ℤ), HenselianLocalRing (v.adicCompletionIntegers ℚ) ∧
      Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := by
  intro v
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers ℚ)
  haveI : IsPrecomplete (maximalIdeal (v.adicCompletionIntegers ℚ)) (v.adicCompletionIntegers ℚ) :=
    Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.completion_integers_precomplete v hϖ
  haveI : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers ℚ)) (v.adicCompletionIntegers ℚ) := {}
  haveI := IsAdicComplete.henselianRing (v.adicCompletionIntegers ℚ)
    (maximalIdeal (v.adicCompletionIntegers ℚ))
  refine ⟨GlobalTheory.henselianLocalRing_of_henselianRing _, ?_⟩
  haveI : Finite (ℤ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  exact Finite.of_equiv _ (GroundTheory.Global.residueFieldEquiv (K := ℚ) v).toEquiv

end GlobalTheory.IntAdicHensel
end

