module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0767
public import GroundTheory.GlobalFields.TateThesis.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualGOfGQ
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DualSwap

section Alg

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def invT : GL n A →* GL n A where
  toFun g := ⟨((g⁻¹ : GL n A) : Matrix n n A)ᵀ, (g : Matrix n n A)ᵀ,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := Units.ext (by simp)
  map_mul' a b := Units.ext (by simp [Matrix.transpose_mul])

theorem invT_invT (g : GL n A) : invT (invT g) = g := Units.ext rfl

theorem bc_invT {B : Type} [CommRing B] (φ : A →+* B) (g : GL n A) :
    Formalism.UG.bc φ (invT g) = invT (Formalism.UG.bc φ g) := Units.ext rfl

theorem continuous_invT [TopologicalSpace A] : Continuous (invT : GL n A → GL n A) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

theorem invT_mem (σ : A →+* A) {J J' : Matrix n n A} (h : J'ᵀ * J = 1) {g : GL n A}
    (hg : g ∈ Formalism.UG.UJ σ J') : invT g ∈ Formalism.UG.UJ σ J := by
  have h' : J * J'ᵀ = 1 := mul_eq_one_comm.1 h
  have hg' : (g : Matrix n n A)ᵀ * J'ᵀ * (g : Matrix n n A).map σ = J'ᵀ := by
    have := congrArg Matrix.transpose (show Formalism.UG.cT σ (g : Matrix n n A) * J' * (g : Matrix n n A) = J' from hg)
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Formalism.UG.cT, Matrix.transpose_transpose, ← Matrix.mul_assoc] at this
    exact this
  show ((g⁻¹ : GL n A) : Matrix n n A).map σ * J * ((g⁻¹ : GL n A) : Matrix n n A)ᵀ = J
  have e1 : ((g⁻¹ : GL n A) : Matrix n n A)ᵀ * (g : Matrix n n A)ᵀ = 1 := (invT g).val_inv
  have e2 : ((g⁻¹ : GL n A) : Matrix n n A).map σ * (g : Matrix n n A).map σ = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one σ (map_zero σ) (map_one σ)]
  have e3 : ((g⁻¹ : GL n A) : Matrix n n A).map σ * J * ((g⁻¹ : GL n A) : Matrix n n A)ᵀ * J'ᵀ = 1 := by
    rw [← hg']
    calc _ = ((g⁻¹ : GL n A) : Matrix n n A).map σ * (J * (((g⁻¹ : GL n A) : Matrix n n A)ᵀ * (g : Matrix n n A)ᵀ) * J'ᵀ) *
          (g : Matrix n n A).map σ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, Matrix.mul_one, h', Matrix.mul_one, e2]
  calc _ = ((g⁻¹ : GL n A) : Matrix n n A).map σ * J * ((g⁻¹ : GL n A) : Matrix n n A)ᵀ * J'ᵀ * J := by
        rw [Matrix.mul_assoc _ J'ᵀ, h, Matrix.mul_one]
    _ = J := by rw [e3, Matrix.one_mul]

end Alg

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

def formLat (G : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {y | ∃ x ∈ Λ, y = star x ᵥ* G}
  zero_mem' := ⟨0, Λ.zero_mem, by simp⟩
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, Λ.add_mem hx hy, by rw [star_add, Matrix.add_vecMul]⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    refine ⟨(⟨star (c : E), Formalism.BasicNotions.Examples₂.star_isIntegral _ c.2⟩ : 𝓞 E) • x, Λ.smul_mem _ hx, ?_⟩
    change (c : E) • (star x ᵥ* G) = star (star (c : E) • x) ᵥ* G
    rw [star_smul, star_star, Matrix.smul_vecMul]

theorem formLat_isLattice {G : Matrix (Fin n) (Fin n) E} (hG : IsUnit G.det) {Λ : Submodule (𝓞 E) (Fin n → E)}
    (h : Submodule.IsLattice E Λ) : Submodule.IsLattice E (formLat G Λ) :=
  Submodule.IsLattice.of_fg E (by
    obtain ⟨s, hs⟩ := h.fg
    classical
    refine ⟨s.image fun x => star x ᵥ* G, le_antisymm (Submodule.span_le.2 ?_) ?_⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact ⟨x, hs ▸ Submodule.subset_span hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hs] at hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hx))
      | zero => simp
      | add x y _ _ hx hy => rw [star_add, Matrix.add_vecMul]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx =>
        have := Submodule.smul_mem _ (⟨star (c : E), Formalism.BasicNotions.Examples₂.star_isIntegral _ c.2⟩ : 𝓞 E) hx
        change star ((c : E) • x) ᵥ* G ∈ _
        rw [star_smul, Matrix.smul_vecMul]
        exact this)

theorem form_dual {G : Matrix (Fin n) (Fin n) E} (hG : IsUnit G.det) (hh : Gᴴ = G) (x y : Fin n → E) :
    ∑ i, ∑ j, star ((star x ᵥ* G) i) * G⁻¹ᵀ i j * (star y ᵥ* G) j = star (∑ i, ∑ j, star (x i) * G i j * y j) := by
  have h1 : ∀ (M : Matrix (Fin n) (Fin n) E) (a b : Fin n → E), ∑ i, ∑ j, star (a i) * M i j * b j = star a ⬝ᵥ (M *ᵥ b) := by
    intro M a b
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  rw [h1, h1, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hG, Matrix.vecMul_one,
    Matrix.star_vecMul, star_star, hh, ← star_dotProduct_star, star_star, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.star_mulVec, hh]

theorem formLat_selfDual {G : Matrix (Fin n) (Fin n) E} (hG : IsUnit G.det) (hh : Gᴴ = G) {Λ : Submodule (𝓞 E) (Fin n → E)}
    (h : ∀ y, y ∈ Λ ↔ ∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G i j * y j) (y : Fin n → E) :
    y ∈ formLat G Λ ↔ ∀ x ∈ formLat G Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G⁻¹ᵀ i j * y j := by
  have hy : y = star (star (y ᵥ* G⁻¹)) ᵥ* G := by
    rw [star_star, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hG, Matrix.vecMul_one]
  constructor
  · rintro ⟨z, hz, rfl⟩ _ ⟨x, hx, rfl⟩
    obtain ⟨b, hb⟩ := (h z).1 hz x hx
    exact ⟨⟨star (b : E), Formalism.BasicNotions.Examples₂.star_isIntegral _ b.2⟩, by rw [form_dual hG hh, ← hb]; rfl⟩
  · intro H
    refine ⟨_, (h _).2 fun x hx => ?_, hy⟩
    obtain ⟨b, hb⟩ := H _ ⟨x, hx, rfl⟩
    rw [hy, form_dual hG hh] at hb
    exact ⟨⟨star (b : E), Formalism.BasicNotions.Examples₂.star_isIntegral _ b.2⟩, by
      change star (b : E) = _
      rw [hb, star_star]⟩

theorem toLin_apply (M : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Matrix.toLinearMapₛₗ₂' E (starRingEnd E) (RingHom.id E) M x y = ∑ i, ∑ j, star (x i) * M i j * y j := by
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp [starRingEnd_apply, mul_comm, mul_left_comm, mul_assoc]

end Lat

variable {D : D7}

theorem gram_herm (S : HSp D) : S.gramᴴ = S.gram :=
  Matrix.ext fun i j => GlobalTheory.LatVac.gram_star S j i

theorem gramInvT_star (S : HSp D) (i j : Fin S.rank) : star (S.gram⁻¹ᵀ i j) = S.gram⁻¹ᵀ j i := by
  have : (S.gram⁻¹)ᴴ = S.gram⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, gram_herm]
  exact congrFun (congrFun this i) j

@[reducible] def dualSp (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (hΛ : IsSelfDualC S Λ) : HSp D where
  V := Fin S.rank → D.host.E
  hT := Matrix.toLinearMapₛₗ₂' D.host.E (starRingEnd D.host.E) (RingHom.id D.host.E) S.gram⁻¹ᵀ
  herm := ⟨fun x y => by
    rw [toLin_apply, toLin_apply, starRingEnd_apply, star_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_mul', star_mul', star_star, gramInvT_star]; ring⟩
  nondeg := by
    have hd := GlobalTheory.LatVac.gram_det_isUnit S
    constructor
    · intro x hx
      have h1 : star x ᵥ* S.gram⁻¹ᵀ = 0 := by
        funext j
        have := hx (Pi.single j 1)
        rw [toLin_apply] at this
        simpa [Pi.single_apply, Matrix.vecMul, dotProduct] using this
      have h2 := congrArg (· ᵥ* S.gramᵀ) h1
      simp only [Matrix.vecMul_vecMul, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.transpose_one,
        Matrix.vecMul_one, Matrix.zero_vecMul] at h2
      exact star_eq_zero.1 h2
    · intro y hy
      have h1 : S.gram⁻¹ᵀ *ᵥ y = 0 := by
        funext j
        have := hy (Pi.single j 1)
        rw [toLin_apply] at this
        simpa [Pi.single_apply, Matrix.mulVec, dotProduct, apply_ite] using this
      have h2 := congrArg (S.gramᵀ *ᵥ ·) h1
      simp only [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hd, Matrix.transpose_one,
        Matrix.one_mulVec, Matrix.mulVec_zero] at h2
      exact h2
  rank := S.rank
  rank_eq := Module.finrank_fin_fun _
  frame := Pi.basisFun _ _
  sig := S.sig
  L0 := formLat S.gram Λ
  standardTuple_isLattice := formLat_isLattice (GlobalTheory.LatVac.gram_det_isUnit S) hΛ.1
  baseLattice_isUnimodular := by
    ext y
    rw [formLat_selfDual (GlobalTheory.LatVac.gram_det_isUnit S) (gram_herm S) hΛ.2]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one,
      LinearMap.restrictScalars_apply, toLin_apply]

variable (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (hΛ : IsSelfDualC S Λ)

theorem dualSp_gram : (dualSp S Λ hΛ).gram = S.gram⁻¹ᵀ := by
  refine Matrix.ext fun i j => ?_
  change Matrix.toLinearMapₛₗ₂' D.host.E (starRingEnd D.host.E) (RingHom.id D.host.E) S.gram⁻¹ᵀ
    (Pi.basisFun _ _ i) (Pi.basisFun _ _ j) = _
  rw [toLin_apply]
  simp [Pi.single_apply, apply_ite]

theorem dualSp_selfDual : IsSelfDualC (dualSp S Λ hΛ) (formLat S.gram Λ) := by
  refine ⟨formLat_isLattice (GlobalTheory.LatVac.gram_det_isUnit S) hΛ.1, fun y => ?_⟩
  rw [dualSp_gram]
  exact formLat_selfDual (GlobalTheory.LatVac.gram_det_isUnit S) (gram_herm S) hΛ.2 y

theorem gram_dual_mul : (dualSp S Λ hΛ).gramᵀ * S.gram = 1 := by
  rw [dualSp_gram, Matrix.transpose_transpose, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S)]

theorem gram_mul_dual : S.gramᵀ * (dualSp S Λ hΛ).gram = 1 := by
  rw [dualSp_gram, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S), Matrix.transpose_one]

theorem dualSp_gram_inv : (dualSp S Λ hΛ).gram⁻¹ = S.gramᵀ := Matrix.inv_eq_left_inv (gram_mul_dual S Λ hΛ)

def dualG : GA D (dualSp S Λ hΛ) →* GA D S :=
  (invT.comp (matHom (dualSp S Λ hΛ))).codRestrict (HR (AF D.host.F) D.sp.cm.sig S.gram) fun g =>
    invT_mem _ (J' := JR (AF D.host.F) (dualSp S Λ hΛ).gram) (by
      rw [JR, JR, ← Matrix.transpose_map, ← Matrix.map_mul, gram_dual_mul,
        Matrix.map_one _ (map_zero _) (map_one _)]) g.2

theorem matHom_dualG (g : GA D (dualSp S Λ hΛ)) : matHom S (dualG S Λ hΛ g) = invT (matHom (dualSp S Λ hΛ) g) := rfl

theorem mt_dualG (g : GA D (dualSp S Λ hΛ)) :
    Formalism.L2.Theta.mt S (dualG S Λ hΛ g) = (Formalism.L2.Theta.mt (dualSp S Λ hΛ) g⁻¹)ᵀ := rfl

theorem mt_dualG_inv (g : GA D (dualSp S Λ hΛ)) :
    Formalism.L2.Theta.mt S (dualG S Λ hΛ g)⁻¹ = (Formalism.L2.Theta.mt (dualSp S Λ hΛ) g)ᵀ := rfl

theorem continuous_dualG : Continuous (dualG S Λ hΛ) :=
  (continuous_invT.comp continuous_subtype_val).subtype_mk _

theorem dualG_mem_GfC {g : GA D (dualSp S Λ hΛ)} (hg : g ∈ GfC (dualSp S Λ hΛ)) : dualG S Λ hΛ g ∈ GfC S := by
  have h : infHom S (dualG S Λ hΛ g) = invT (infHom (dualSp S Λ hΛ) g) := Units.ext rfl
  rw [GfC, MonoidHom.mem_ker] at hg ⊢
  rw [h, hg, map_one]

theorem dualG_mem_GinfC {g : GA D (dualSp S Λ hΛ)} (hg : g ∈ GinfC (dualSp S Λ hΛ)) : dualG S Λ hΛ g ∈ GinfC S := by
  have h : finHom S (dualG S Λ hΛ g) = invT (finHom (dualSp S Λ hΛ) g) := Units.ext rfl
  rw [GinfC, MonoidHom.mem_ker] at hg ⊢
  rw [h, hg, map_one]

theorem exists_dualG_of_GQ {γ : GA D S} (hγ : γ ∈ GQ S) : ∃ γ' ∈ GQ (dualSp S Λ hΛ), dualG S Λ hΛ γ' = γ := by
  have hγ' : matHom S γ ∈ HFin (AF D.host.F) D.sp.cm.sig S.gram := hγ
  obtain ⟨g, hg, hgγ⟩ := hγ'
  have h1 : invT (matHom S γ) ∈ HR (AF D.host.F) D.sp.cm.sig (dualSp S Λ hΛ).gram :=
    invT_mem _ (J' := JR (AF D.host.F) S.gram) (by
      rw [JR, JR, ← Matrix.transpose_map, ← Matrix.map_mul, gram_mul_dual,
        Matrix.map_one _ (map_zero _) (map_one _)]) γ.2
  have h2 : invT (matHom S γ) ∈ HFin (AF D.host.F) D.sp.cm.sig (dualSp S Λ hΛ).gram :=
    ⟨invT g, invT_mem _ (gram_mul_dual S Λ hΛ) hg, by rw [bc_invT, hgγ]⟩
  refine ⟨⟨invT (matHom S γ), h1⟩, h2, Subtype.ext ?_⟩
  exact invT_invT (matHom S γ)

end GlobalTheory.DualSwap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrAlgClosureOverFiniteDvrExtension
section
open IsLocalRing

namespace GlobalTheory

theorem exists_dvr_over_finite_ext : ∀ (V W : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr V → GlobalTheory.LN.CDvr W → ∀ io : V →+* W, io.Finite → Function.Injective io → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] [Algebra (FractionRing W) F], (∀ v, algebraMap (FractionRing W) F (algebraMap W _ (io v)) = algebraMap (FractionRing V) F (algebraMap V _ v)) → ∃ N : ℕ, ∀ (T' : Subring F) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v, (f v : F) = algebraMap (FractionRing V) F (algebraMap V _ v)) → (∀ π, Irreducible π → Irreducible (f π)) → ∃ (T'' : Subring F) (_ : IsDiscreteValuationRing T'') (g : W →+* T'') (e : ℕ), T' ≤ T'' ∧ (∀ w, (g w : F) = algebraMap (FractionRing W) F (algebraMap W _ w)) ∧ 1 ≤ e ∧ e ≤ N ∧ ∀ π, Irreducible π → ∃ ϖ : T'', Irreducible ϖ ∧ Associated (g π) (ϖ ^ e) := by
  classical
  intro V W _ _ _ _ _ _ hV hW io hio hinj F _ _ _ _ hcomp
  obtain ⟨hVd, -, hV0⟩ := (GlobalTheory.LN.cDvr_iff V).1 hV
  obtain ⟨hWd, -, -⟩ := (GlobalTheory.LN.cDvr_iff W).1 hW
  set φV : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V _) with hφV
  set φW : W →+* F := (algebraMap (FractionRing W) F).comp (algebraMap W _) with hφW
  have hφWinj : Function.Injective φW :=
    (algebraMap (FractionRing W) F).injective.comp (IsFractionRing.injective W _)
  have hφVinj : Function.Injective φV :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _)
  haveI : CharZero F := (RingHom.charZero_iff hφVinj).1 hV0
  have hc : ∀ v, φW (io v) = φV v := hcomp
  letI := io.toAlgebra
  haveI : Module.Finite V W := hio
  obtain ⟨n, gens, hspan⟩ := Module.Finite.exists_fin (R := V) (M := W)
  refine ⟨n, ?_⟩
  intro T' hT' f hf hirr
  set s : Finset F := Finset.univ.image (fun i => φW (gens i)) with hs
  have hcard : s.card ≤ n := by
    calc s.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
      _ = n := by simp
  have K1 : ∀ w : W, φW w ∈ Submodule.span T' (s : Set F) := by
    intro w
    have hw : w ∈ Submodule.span V (Set.range gens) := by rw [hspan]; trivial
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact Submodule.subset_span (by simp [hs])
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul v x _ hx =>
      have : φW (v • x) = (f v) • φW x := by
        rw [Algebra.smul_def, map_mul, Subring.smul_def, smul_eq_mul, hf]
        exact congrArg (· * φW x) (hc v)
      rw [this]; exact Submodule.smul_mem _ _ hx
  have h1 : (1 : F) ∈ Submodule.span T' (s : Set F) := by simpa using K1 1
  have hmul : ∀ x ∈ s, ∀ y ∈ s, x * y ∈ Submodule.span T' (s : Set F) := by
    intro x hx y hy
    simp only [hs, Finset.mem_image, Finset.mem_univ, true_and] at hx hy
    obtain ⟨i, rfl⟩ := hx; obtain ⟨j, rfl⟩ := hy
    rw [← map_mul]; exact K1 _
  obtain ⟨T'', hT'', hle, hsT, hdom, hden⟩ := _root_.GlobalTheory.DomDVR.exists_dominating_dvr F T' hT' s h1 hmul
  have K2 : ∀ x ∈ Submodule.span T' (s : Set F), x ∈ T'' := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hsT x hx
    | zero => exact T''.zero_mem
    | add x y _ _ hx hy => exact T''.add_mem hx hy
    | smul t x _ hx => rw [Subring.smul_def, smul_eq_mul]; exact T''.mul_mem (hle t.2) hx
  let g : W →+* T'' := φW.codRestrict T'' (fun w => K2 _ (K1 w))
  have hg : ∀ w, (g w : F) = φW w := fun w => rfl
  have hginj : Function.Injective g := fun a b h => hφWinj (by simpa [hg] using congrArg Subtype.val h)
  haveI := hT''
  obtain ⟨πV, hπV⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hfπ := hirr πV hπV
  obtain ⟨ϖ, hϖ, e', he1, he2, hassoc⟩ := _root_.GlobalTheory.ramification_le_card_of_span F T' T'' hT' hT'' hle hdom s hden (f πV) hfπ
  obtain ⟨πW, hπW⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hioπ : io πV ≠ 0 := fun h => hπV.ne_zero (hinj (by rw [h, map_zero]))
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.associated_pow_irreducible hioπ hπW
  have hgπ : g πW ≠ 0 := fun h => hπW.ne_zero (hginj (by rw [h, map_zero]))
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hgπ hϖ
  have hgio : g (io πV) = Subring.inclusion hle (f πV) := by
    apply Subtype.ext
    rw [hg, hc]
    exact (hf πV).symm
  have hA : Associated (ϖ ^ e') (ϖ ^ (k * a)) := by
    have h2 : Associated (g (io πV)) ((g πW) ^ a) := by
      rw [← map_pow]; exact ha.map g
    rw [hgio] at h2
    rw [pow_mul]
    exact hassoc.symm.trans (h2.trans hk.pow_pow)
  have hka : e' = k * a := by
    apply le_antisymm
    · exact (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 hA.dvd
    · exact (pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 hA.symm.dvd
  have hk0 : k ≠ 0 := by rintro rfl; simp at hka; omega
  have ha0 : a ≠ 0 := by rintro rfl; simp at hka; omega
  refine ⟨T'', hT'', g, k, hle, fun w => rfl, Nat.one_le_iff_ne_zero.2 hk0, ?_, ?_⟩
  · calc k ≤ k * a := Nat.le_mul_of_pos_right k (Nat.pos_of_ne_zero ha0)
      _ = e' := hka.symm
      _ ≤ s.card := he2
      _ ≤ n := hcard
  · intro π hπ
    exact ⟨ϖ, hϖ, ((IsDiscreteValuationRing.associated_of_irreducible W hπ hπW).map g).trans hk⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCharacterSumEqLocallyConstantOnCompa
section
open Matrix Topology

noncomputable section

namespace GlobalTheory.JSW.KirFin

theorem exists_charSum_eq_on_compact : ∀ {F : Type} [NormedField F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 →
    ∀ {ι : Type} [Fintype ι] (K : Set (ι → F)), IsCompact K → ∀ Φ : (ι → F) → ℂ, IsLocallyConstant Φ →
    ∃ T : (ι → F) →₀ ℂ, ∀ r ∈ K, (T.sum fun v c => c * ψ (r ⬝ᵥ v)) = Φ r := by
  intro F _ ψ hψ hψ1 ι _ K hK Φ hΦ
  classical
  obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
    by_contra h
    push_neg at h
    exact hψ1 (AddChar.ext _ _ h)
  let χ : (ι → F) → (ι → F) → ℂ := fun v r => ψ (r ⬝ᵥ v)
  let S : Set ((ι → F) → ℂ) := Set.range χ
  have hχmul : ∀ v w, χ v * χ w = χ (v + w) := by
    intro v w; funext r; simp [χ, dotProduct_add, AddChar.map_add_eq_mul]
  have hχ0 : χ 0 = 1 := by funext r; simp [χ]
  have hlc : ∀ v, IsLocallyConstant (χ v) := fun v =>
    hψ.comp_continuous (continuous_id.dotProduct continuous_const)
  let L : Subalgebra ℂ ((ι → F) → ℂ) :=
    { carrier := {a | IsLocallyConstant a}
      mul_mem' := fun ha hb => IsLocallyConstant.mul ha hb
      add_mem' := fun ha hb => IsLocallyConstant.add ha hb
      algebraMap_mem' := fun c => IsLocallyConstant.const _ }
  let A := Algebra.adjoin ℂ S
  have hAL : A ≤ L := Algebra.adjoin_le (by rintro _ ⟨v, rfl⟩; exact hlc v)
  have hAspan : ∀ a ∈ A, a ∈ Submodule.span ℂ S := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Submodule.subset_span hx
    | algebraMap c =>
      have : algebraMap ℂ ((ι → F) → ℂ) c = c • χ 0 := by
        rw [hχ0, Algebra.algebraMap_eq_smul_one]
      rw [this]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | mul x y _ _ hx hy =>
      have := Submodule.mul_mem_mul hx hy
      rw [Submodule.span_mul_span] at this
      refine Submodule.span_mono ?_ this
      rintro _ ⟨_, ⟨v, rfl⟩, _, ⟨w, rfl⟩, rfl⟩
      exact ⟨v + w, (hχmul v w).symm⟩
  let ρ : ((ι → F) → ℂ) →ₐ[ℂ] (K → ℂ) :=
    { toFun := fun a x => a x.1
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  obtain ⟨a, ha, e⟩ := mem_of_separates (A.map ρ)
    (by rintro _ ⟨a, ha, rfl⟩; exact (hAL ha).comp_continuous continuous_subtype_val)
    (by
      intro x y hxy
      obtain ⟨i, hi⟩ := Function.ne_iff.1 (Subtype.coe_ne_coe.2 hxy)
      refine ⟨ρ (χ (Pi.single i (t / (x.1 i - y.1 i)))), ⟨_, Algebra.subset_adjoin ⟨_, rfl⟩, rfl⟩,
        fun h => ht ?_⟩
      change ψ (x.1 ⬝ᵥ _) = ψ (y.1 ⬝ᵥ _) at h
      rw [dotProduct_single, dotProduct_single] at h
      have h2 : x.1 i * (t / (x.1 i - y.1 i)) = t + y.1 i * (t / (x.1 i - y.1 i)) := by
        have := sub_ne_zero.2 hi
        field_simp
        ring
      rw [h2, AddChar.map_add_eq_mul] at h
      exact (mul_eq_right₀ (ψ.val_isUnit _).ne_zero).1 h)
    (hΦ.comp_continuous continuous_subtype_val)
  obtain ⟨T, hT⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hAspan a ha)
  refine ⟨T, fun r hr => ?_⟩
  have h1 := congrFun e ⟨r, hr⟩
  change a r = Φ r at h1
  rw [← h1, ← hT]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, χ]

end GlobalTheory.JSW.KirFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKerOpRowFreqColGL
section
open MeasureTheory GlobalTheory.JSW
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW

theorem colGL_val_apply {a : ℕ} (r : ℕ) (x : Fin a → ℂ) (i j : Fin a) :
    ((colGL r x : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j =
      (1 : Matrix (Fin a) (Fin a) ℂ) i j + (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) := rfl

theorem colGL_inv_val_apply {a : ℕ} (r : ℕ) (x : Fin a → ℂ) (i j : Fin a) :
    (((colGL r x)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j =
      (1 : Matrix (Fin a) (Fin a) ℂ) i j - (if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) := rfl

theorem norm_one_apply_le' {a : ℕ} (i j : Fin a) : ‖(1 : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem norm_ite_apply_le {a : ℕ} (p : Prop) [Decidable p] (x : Fin a → ℂ) (i : Fin a) :
    ‖(if p then x i else 0)‖ ≤ ‖x‖ := by
  split_ifs
  · exact norm_le_pi_norm x i
  · simp

theorem htGL_colGL_le {a : ℕ} (r : ℕ) (x : Fin a → ℂ) :
    htGL (colGL r x) ≤ 1 + 2 * (a : ℝ) ^ 2 * (1 + ‖x‖) := by
  unfold htGL
  have h1 : ∀ i j : Fin a, ‖((colGL r x : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ 1 + ‖x‖ := by
    intro i j
    rw [colGL_val_apply]
    exact (norm_add_le _ _).trans (add_le_add (norm_one_apply_le' i j) (norm_ite_apply_le _ x i))
  have h2 : ∀ i j : Fin a, ‖(((colGL r x)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ 1 + ‖x‖ := by
    intro i j
    rw [colGL_inv_val_apply]
    exact (norm_sub_le _ _).trans (add_le_add (norm_one_apply_le' i j) (norm_ite_apply_le _ x i))
  have s1 : ∑ i, ∑ j, ‖((colGL r x : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ (a : ℝ) ^ 2 * (1 + ‖x‖) := by
    calc _ ≤ ∑ _i : Fin a, ∑ _j : Fin a, (1 + ‖x‖) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have s2 : ∑ i, ∑ j, ‖(((colGL r x)⁻¹ : GL (Fin a) ℂ) : Matrix (Fin a) (Fin a) ℂ) i j‖ ≤ (a : ℝ) ^ 2 * (1 + ‖x‖) := by
    calc _ ≤ ∑ _i : Fin a, ∑ _j : Fin a, (1 + ‖x‖) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h2 i j
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  linarith

theorem norm_inr_le_one' (Z V : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ‖ContinuousLinearMap.inr ℝ Z V‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [Prod.norm_def]

theorem norm_inl_le_one' (Z V : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ‖ContinuousLinearMap.inl ℝ Z V‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by simp [Prod.norm_def]

end GlobalTheory.JSW
end
end

