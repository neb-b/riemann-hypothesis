module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasComplementOfBasis
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1245
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1303
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOpArchimedeanVectorActsBySchrodingerTr
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchRhoPure


variable (F : Type) [Field F] [NumberField F] in
def evHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evHom_apply {F : Type} [Field F] [NumberField F] (a : AF F) : evHom F a = evI F a := rfl

theorem rho_pureA_schrF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ), IsStd ψ → ∀ u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (h : (κ → Af F) → ℂ),
      d.rho ψ u (pureA F f h) = pureA F (GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F κ)
        (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) f) h := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d hψ u hu f h
  have hw : At (evI F) (d.e u) := fun r hr => by rw [← map_smul, hu r hr, map_zero]
  show schr ψ (d.e u) (pureA F f h) = _
  generalize d.e u = w at hw ⊢
  obtain ⟨p, q⟩ := w
  funext x
  have hfin : (fun i => ((x + p) i).2) = fun i => (x i).2 := by
    funext i
    have h0 : evI F ((0, 1) : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    have h1 : (1 : Af F) * (p i).2 = 0 := congrArg (fun z : (κ → AF F) × (κ → AF F) => (z.1 i).2) (hw _ h0)
    change (x i).2 + (p i).2 = _
    rw [one_mul] at h1
    rw [h1, add_zero]
  have hAt : At (evI F) (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q)) := by
    intro v hv
    have hq : v • q = 0 := congrArg Prod.snd (hw v hv)
    rw [smul_add, ← dotProduct_smul, smul_eq_mul, mul_left_comm, ← smul_eq_mul v, ← dotProduct_smul, hq]
    simp
  have harch : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + p) i).1) =
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) + ArchUniq.locV p :=
    funext fun i => map_add (evHom F) (x i) (p i)
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q))) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * evI F (q i)) +
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, evI F (p i) * evI F (q i)) / 2 := by
    set z : mixedEmbedding.mixedSpace F := ∑ i, evI F (p i) * evI F (q i) with hz
    have hpq : evHom F (p ⬝ᵥ q) = z := by
      rw [RingHom.map_dotProduct]; rfl
    have hxq : evHom F (x ⬝ᵥ q) = ∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * evI F (q i) := by
      rw [RingHom.map_dotProduct]; rfl
    have key : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evHom F ⅟(2 : AF F) * z) +
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evHom F ⅟(2 : AF F) * z) =
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z := by
      rw [← map_add (f := _), ← add_mul, ← map_add (f := _), invOf_two_add_invOf_two, map_one, one_mul]
    rw [← evHom_apply, map_add (f := _), map_mul, hpq, hxq, map_add (f := _)]
    linarith
  simp only [schr, pureA, GlobalTheory.ArchUniq.schrF, GlobalTheory.ArchUniq.trP, GlobalTheory.ArchUniq.locV] at harch ⊢
  rw [hψ.2.2 _ hAt, hfin, htr, harch, ← mul_assoc]

end GlobalTheory.ArchRhoPure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeLocalUnitaryTwist
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertSign

open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

variable {K : UQ}

theorem model_pow {B : InvAlg K} {n : ℕ} {γ : Matrix (Fin n) (Fin n) K.E} {x : B.Aˣ}
    {ψ : B.A ≃ₗ[K.E] (Fin n → K.E)} (h : IsModel B γ x ψ) (k : ℕ) (y : B.A) :
    ψ (B.g ^ k * y) = (γ ^ k) *ᵥ ψ y := by
  induction k generalizing y with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, h.2.1, ih, pow_succ', ← mulVec_mulVec]

theorem model_aeval {B : InvAlg K} {n : ℕ} {γ : Matrix (Fin n) (Fin n) K.E} {x : B.Aˣ}
    {ψ : B.A ≃ₗ[K.E] (Fin n → K.E)} (h : IsModel B γ x ψ) (p : K.E[X]) (y : B.A) :
    ψ (aeval B.g p * y) = aeval γ p *ᵥ ψ y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), add_mul, map_add (f := _), hp, hq, add_mulVec]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, mul_assoc, ← Algebra.smul_def, map_smul, model_pow h,
      ← Algebra.smul_def, Matrix.smul_mulVec]

theorem aeval_g_P (B : InvAlg K) : aeval B.g B.P = 0 := by
  have h : Algebra.lmul K.E B.A (aeval B.g B.P) = 0 := by
    rw [← aeval_algHom_apply]; exact LinearMap.aeval_self_charpoly _
  simpa using LinearMap.congr_fun h 1

theorem aeval_prod (B₁ B₂ : InvAlg K) (p : K.E[X]) :
    aeval (B₁.prod B₂).g p = ((aeval B₁.g p, aeval B₂.g p) : B₁.A × B₂.A) := by
  change aeval ((B₁.g, B₂.g) : B₁.A × B₂.A) p = _
  ext
  · exact (aeval_algHom_apply (AlgHom.fst K.E B₁.A B₂.A) ((B₁.g, B₂.g) : B₁.A × B₂.A) p).symm
  · exact (aeval_algHom_apply (AlgHom.snd K.E B₁.A B₂.A) ((B₁.g, B₂.g) : B₁.A × B₂.A) p).symm

theorem ker_model (B₁ B₂ : InvAlg K) (hs : (B₁.P * B₂.P).Separable) {n : ℕ}
    {γ : Matrix (Fin n) (Fin n) K.E} {x : (B₁.prod B₂).Aˣ} {ψ : (B₁.prod B₂).A ≃ₗ[K.E] (Fin n → K.E)}
    (h : IsModel (B₁.prod B₂) γ x ψ) (y : Fin n → K.E) :
    aeval γ B₁.P *ᵥ y = 0 ↔ ∃ a : B₁.A, y = ψ ((a, 0) : B₁.A × B₂.A) := by
  obtain ⟨z, rfl⟩ := ψ.surjective y
  rw [← model_aeval h, LinearEquiv.map_eq_zero_iff, aeval_prod, aeval_g_P]
  obtain ⟨a, c, hac⟩ := Polynomial.Separable.isCoprime hs
  have hu : IsUnit (aeval B₂.g B₁.P) := by
    have := congrArg (aeval B₂.g) hac
    rw [map_add (f := _), map_mul, map_mul, aeval_g_P B₂, mul_zero, add_zero, map_one] at this
    exact isUnit_iff_exists_inv'.2 ⟨_, this⟩
  constructor
  · intro hz
    have h2 : aeval B₂.g B₁.P * z.2 = 0 := congrArg Prod.snd hz
    refine ⟨z.1, ?_⟩
    congr 1
    exact Prod.ext rfl (hu.mul_right_eq_zero.1 h2)
  · rintro ⟨a0, ha⟩
    rw [ψ.injective ha]
    exact Prod.ext (zero_mul _) (mul_zero _)

theorem herm_fst (B₁ B₂ : InvAlg K) (x : (B₁.prod B₂).A) (a b : B₁.A) :
    (B₁.prod B₂).herm x ((a, 0) : B₁.A × B₂.A) ((b, 0) : B₁.A × B₂.A) = B₁.herm x.1 a b := by
  unfold InvAlg.herm
  change Algebra.trace K.E (B₁.A × B₂.A) ((x.1 * a * B₁.σ b, x.2 * 0 * B₂.σ 0)) = _
  rw [Algebra.trace_prod_apply]
  simp

theorem aeval_map_matrix {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) (p : R[X]) : aeval (M.map f) (p.map f) = (aeval M p).map f := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.map_add (f := _), map_add (f := _), map_add (f := _), hp, hq, Matrix.map_add _ (map_add f)]
  | monomial k a =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial]
    change _ = f.mapMatrix _
    rw [map_mul, map_pow]
    congr 1
    rw [Matrix.algebraMap_eq_diagonal, Matrix.algebraMap_eq_diagonal]
    ext i j
    simp [Matrix.diagonal_apply]
    split_ifs <;> simp

theorem ker_transport {F L : Type} [Field F] [Field L] (e : F ≃+* L) {n : ℕ} (A : Matrix (Fin n) (Fin n) L)
    (y : Fin n → F) : (A.map e.symm) *ᵥ y = 0 ↔ A *ᵥ (fun k => e (y k)) = 0 := by
  have key : ∀ i, e ((A.map e.symm *ᵥ y) i) = (A *ᵥ fun k => e (y k)) i := by
    intro i
    have := RingHom.map_mulVec e.toRingHom (A.map e.symm) y i
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, Matrix.map_map] at this
    rw [this]
    congr 2
    ext a b
    simp
  constructor
  · intro h
    funext i
    rw [← key, h]
    simp
  · intro h
    funext i
    apply e.injective
    rw [key, h]
    simp

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → ∀ (n : ℕ) (Q₁ : (w.adicCompletion E)[X]) (B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K), (B₁.P * B₂.P).Separable → B₁.P = Q₁.map e.symm.toRingHom → ∀ (γ : GLw n w) (x : (B₁.prod B₂).Aˣ) (ψ : (B₁.prod B₂).A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel (B₁.prod B₂) (γ.val.map e.symm) x ψ → kapSign n w Q₁ γ = ((K.eta (B₁.gramDet (x : (B₁.prod B₂).A).1) : ℚ) : ℂ) := by
  intro E _ _ _ _ w hw K e he hval n Q₁ B₁ B₂ hs hP γ x ψ hm
  simp only [kapSign, if_neg hw]
  have hA : aeval (γ.val.map e.symm) B₁.P = (aeval γ.val Q₁).map e.symm := by
    rw [hP]; exact aeval_map_matrix e.symm.toRingHom _ _
  have hmemW : ∀ y : Fin n → K.E, y ∈ LinearMap.ker (Matrix.toLin' (aeval (γ.val.map e.symm) B₁.P)) ↔
      aeval γ.val Q₁ *ᵥ (fun k => e (y k)) = 0 := by
    intro y
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, hA]
    exact ker_transport e _ y
  set V₁ := LinearMap.ker (Matrix.toLin' (aeval γ.val Q₁)) with hV₁
  set b := Module.finBasis (w.adicCompletion E) V₁ with hb
  set W := LinearMap.ker (Matrix.toLin' (aeval (γ.val.map e.symm) B₁.P)) with hW
  let v : Fin (Module.finrank (w.adicCompletion E) V₁) → Fin n → K.E := fun i k => e.symm ((b i : Fin n → _) k)
  have hv_li : LinearIndependent K.E v := by
    refine Fintype.linearIndependent_iff.2 (fun g hg i => ?_)
    have h1 : ∑ j, e (g j) • (b j : Fin n → w.adicCompletion E) = 0 := by
      funext k
      have := congrArg e (congrFun hg k)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [v, Finset.sum_apply, map_sum, map_mul] using this
    have := Fintype.linearIndependent_iff.1 (GlobalTheory.KapSignMul.li_coe b) _ h1 i
    simpa using this
  have hv_span : Submodule.span K.E (Set.range v) = W := by
    refine le_antisymm (Submodule.span_le.2 ?_) (fun y hy => ?_)
    · rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, hmemW]
      have := LinearMap.mem_ker.1 (b i).2
      rw [Matrix.toLin'_apply] at this
      have h2 : (fun k => e (v i k)) = (b i : Fin n → w.adicCompletion E) := by funext k; simp [v]
      rw [h2]; exact this
    · rw [hmemW] at hy
      have hyV : (fun k => e (y k)) ∈ V₁ := by rw [hV₁, LinearMap.mem_ker, Matrix.toLin'_apply]; exact hy
      have hsr := congrArg (fun z : V₁ => (z : Fin n → w.adicCompletion E)) (b.sum_repr ⟨_, hyV⟩)
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => e.symm (b.repr ⟨_, hyV⟩ i), ?_⟩
      funext k
      have h3 : ∑ i, b.repr ⟨_, hyV⟩ i * (b i : Fin n → w.adicCompletion E) k = e (y k) := by
        have := congrFun hsr k
        simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
        exact this
      apply e.injective
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [v, Finset.sum_apply, map_sum, map_mul] using h3
  let f := Module.finBasis K.E B₁.A
  let φ : B₁.A →ₗ[K.E] (Fin n → K.E) := ψ.toLinearMap ∘ₗ LinearMap.inl K.E B₁.A B₂.A
  have hφi : Function.Injective φ := fun a a' h => congrArg Prod.fst (ψ.injective h)
  let u : Fin (Module.finrank K.E B₁.A) → Fin n → K.E := fun i => φ (f i)
  have hu_li : LinearIndependent K.E u := f.linearIndependent.map' φ (LinearMap.ker_eq_bot.2 hφi)
  have hu_span : Submodule.span K.E (Set.range u) = W := by
    have hr : Set.range u = φ '' Set.range f := by rw [← Set.range_comp]; rfl
    rw [hr, Submodule.span_image, f.span_eq, Submodule.map_top]
    ext y
    rw [LinearMap.mem_range, hW, LinearMap.mem_ker, Matrix.toLin'_apply, ker_model B₁ B₂ hs hm]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨a, rfl⟩
  obtain ⟨d, hd, hdet⟩ := GlobalTheory.KapSignMul.gram_change (K.c : K.E →+* K.E) W u v hu_li hu_span hv_li hv_span
  have hM : (Matrix.of fun i j => ∑ k, cj w ((b i : Fin n → w.adicCompletion E) k) * (b j : Fin n → w.adicCompletion E) k) =
      (Matrix.of fun i j => ∑ k, (K.c : K.E →+* K.E) (v i k) * v j k).map e := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [v, map_sum, he]
  have hG : (Matrix.of fun i j => ∑ k, (K.c : K.E →+* K.E) (u i k) * u j k) =
      (Matrix.of fun i j => B₁.herm (x : (B₁.prod B₂).A).1 (f i) (f j))ᵀ := by
    ext i j
    simp only [Matrix.of_apply, Matrix.transpose_apply]
    rw [← herm_fst]
    refine Eq.trans ?_ (hm.2.2 _ _)
    unfold GlobalTheory.InertUnitOrb.stdH
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [RingEquiv.coe_toRingHom]
    exact mul_comm _ _
  rw [hM, show ((Matrix.of fun i j => ∑ k, (K.c : K.E →+* K.E) (v i k) * v j k).map e).det =
    e (Matrix.of fun i j => ∑ k, (K.c : K.E →+* K.E) (v i k) * v j k).det from
    (RingHom.map_det e.toRingHom _).symm, ← hval, hdet, hG, Matrix.det_transpose]
  have heta : K.eta ((K.c : K.E →+* K.E) d * d * (Matrix.of fun i j => B₁.herm (x : (B₁.prod B₂).A).1 (f i) (f j)).det) =
      K.eta (B₁.gramDet (x : (B₁.prod B₂).A).1) := by
    rw [show (K.c : K.E →+* K.E) d * d * (Matrix.of fun i j => B₁.herm (x : (B₁.prod B₂).A).1 (f i) (f j)).det =
      d * (Matrix.of fun i j => B₁.herm (x : (B₁.prod B₂).A).1 (f i) (f j)).det * K.c d by
      simp only [RingEquiv.coe_toRingHom]; ring]
    rw [GlobalTheory.UnitLemma.Orbit.eta_norm_mul _ _ hd]
    rfl
  rw [← heta]
  unfold UQ.eta
  push_cast
  rfl

end GlobalTheory.InertSign
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSpaceAddSignatureExists
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.SignatureAddition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem coords_gram (B : HSpace E) (x y : B.V) :
    ∑ l, (∑ k, star (B.frame.repr x k) * B.gram k l) * B.frame.repr y l = B.hT x y := by
  conv_rhs => rw [← B.frame.sum_repr x, ← B.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    Finset.sum_mul, HSpace.gram, RingHom.id_apply, starRingEnd_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring

def middleSymmetricBasisVector (E : Type) [Field E] (c : ℕ) (p : Fin c) : Fin c → E :=
  Pi.single p (if 2 * p.1 + 1 ≤ c then 1 else -1 / 2) +
    Pi.single p.rev (if 2 * p.1 + 1 < c then 1 else if 2 * p.1 + 1 = c then 0 else 1 / 2)

theorem middleSymmetricBasisVectors_gram_antiDiagonal (c : ℕ) (neg : Bool) (p q : Fin c) :
    Examples₂.diagForm c (GlobalTheory.UnitPerp.negFrom c (if neg then c / 2 else (c + 1) / 2)) (middleSymmetricBasisVector E c p) (middleSymmetricBasisVector E c q) =
      antiDiagonalSignGramMatrix c (if neg then -1 else 1) p q := by
  have hp := p.2
  have hq := q.2
  obtain ⟨P, hP⟩ : ∃ P, P = if neg then c / 2 else (c + 1) / 2 := ⟨_, rfl⟩
  have hP1 : c / 2 ≤ P ∧ P ≤ (c + 1) / 2 := by rw [hP]; split_ifs <;> omega
  have hm : 2 * p.1 + 1 = c → (P ≤ p.1 ↔ neg = true) := by
    intro h; rw [hP]; cases neg <;> simp <;> omega
  rw [← hP]
  simp only [middleSymmetricBasisVector, map_add (f := _), LinearMap.add_apply, Examples₂.diagForm_single_left, Pi.single_apply, Pi.add_apply,
    GlobalTheory.UnitPerp.negFrom, Examples₂.sgn, antiDiagonalSignGramMatrix, Fin.ext_iff, Fin.val_rev, decide_eq_true_eq]
  generalize p.1 = a at *
  generalize q.1 = b at *
  clear hP
  have e1 : (c - (a + 1) = c - (b + 1)) = (a = b) := propext (by omega)
  have e2 : (a = c - (b + 1)) = (a + b + 1 = c) := propext (by omega)
  have e3 : (c - (a + 1) = b) = (a + b + 1 = c) := propext (by omega)
  simp only [e1, e2, e3]
  by_cases h1 : a = b <;> by_cases h2 : a + b + 1 = c
  · subst h1
    have h : 2 * a + 1 = c := by omega
    simp only [if_pos h.le, if_pos h, if_neg (show ¬ 2 * a + 1 < c by omega), hm h, if_pos h2]
    cases neg <;> simp
  · subst h1
    rcases (show 2 * a + 1 < c ∨ c < 2 * a + 1 by omega) with h | h
    · simp only [if_pos h.le, if_pos h, if_neg (show ¬ P ≤ a by omega), if_pos (show P ≤ c - (a + 1) by omega), if_neg h2]
      simp
    · simp only [if_neg h.not_ge, if_neg h.not_gt, if_neg h.ne', if_pos (show P ≤ a by omega),
        if_neg (show ¬ P ≤ c - (a + 1) by omega), if_neg h2]
      norm_num
  · rcases (show (2 * a + 1 < c ∧ c < 2 * b + 1) ∨ (2 * b + 1 < c ∧ c < 2 * a + 1) by omega) with ⟨h, h'⟩ | ⟨h', h⟩
    · simp only [if_pos h.le, if_pos h, if_neg (show ¬ P ≤ a by omega), if_pos (show P ≤ c - (a + 1) by omega),
        if_neg h'.not_ge, if_neg h'.not_gt, if_neg h'.ne', if_neg h1, if_pos h2]
      norm_num
    · simp only [if_neg h.not_ge, if_neg h.not_gt, if_neg h.ne', if_pos (show P ≤ a by omega),
        if_neg (show ¬ P ≤ c - (a + 1) by omega), if_pos h'.le, if_pos h', if_neg h1, if_pos h2]
      norm_num
  · simp only [if_neg h1, if_neg h2, add_zero, mul_zero]

end Generic

theorem exists_hermitian_space_add_signature (D : D7) (A : HSp D) (p q c : ℕ) (neg : Bool) (hA : A.SigOK) (hs : ∀ τ, A.sig τ = (p, q)) :
    ∃ B : HSp D, Nonempty (HermitianOrthogonalExtensionData A B c (if neg then -1 else 1)) ∧ B.SigOK ∧
      ∀ τ, B.sig τ = (p + (if neg then c / 2 else (c + 1) / 2), q + (if neg then (c + 1) / 2 else c / 2)) := by
  have hc : c = (if neg then c / 2 else (c + 1) / 2) + (if neg then (c + 1) / 2 else c / 2) := by
    split_ifs <;> omega
  have hW := GlobalTheory.UnitPerp.ofKind_stdSpace (E := D.host.E) hc
  set W : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral c (GlobalTheory.UnitPerp.negFrom c (if neg then c / 2 else (c + 1) / 2))
    (if neg then c / 2 else (c + 1) / 2) (if neg then (c + 1) / 2 else c / 2) with hWd
  refine ⟨GlobalTheory.Doubling.hsum A W, ⟨?_⟩, GlobalTheory.Doubling.sigOK_hsum hA hW.2.1, fun τ => ?_⟩
  · refine
      { ι := LinearMap.inl _ _ _
        isom := GlobalTheory.Doubling.isIsomEmb_inl A W
        a := fun k j => (GlobalTheory.Doubling.hsum A W).frame.repr ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V) k
        gram := Matrix.ext fun i j => ?_
        perp := Matrix.ext fun i j => ?_
        rank := rfl }
    · refine Eq.trans (coords_gram (GlobalTheory.Doubling.hsum A W) ((0, middleSymmetricBasisVector D.host.E c i) : A.V × W.V)
        ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V)) ?_
      refine (GlobalTheory.Doubling.orthSum_apply A W _ _).trans ?_
      rw [map_zero, zero_add]
      exact middleSymmetricBasisVectors_gram_antiDiagonal c neg i j
    · refine Eq.trans ?_ ((coords_gram (GlobalTheory.Doubling.hsum A W) ((A.frame i, 0) : A.V × W.V)
        ((0, middleSymmetricBasisVector D.host.E c j) : A.V × W.V)).trans ?_)
      · have e : frameMat (GlobalTheory.Doubling.hsum A W) A (LinearMap.inl _ _ _) =
            fun k i => (GlobalTheory.Doubling.hsum A W).frame.repr ((A.frame i, 0) : A.V × W.V) k :=
          Matrix.ext fun k i => LinearMap.toMatrix_apply A.frame (GlobalTheory.Doubling.hsum A W).frame _ k i
        rw [e]
        rfl
      · refine (GlobalTheory.Doubling.orthSum_apply A W _ _).trans ?_
        rw [map_zero, map_zero, zero_add]
        rfl
  · show A.sig τ + W.sig τ = _
    rw [hs τ]
    rfl

end GlobalTheory.SignatureAddition

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelFiltrationSymbolMonomialProduct
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open GlobalTheory.HSShort GlobalTheory.HSChoice MvPolynomial

set_option autoImplicit false

namespace GlobalTheory.HSShort

theorem exists_filV_mulPow {K : Type} [Field K] [NumberField K] (X : Data K) {s : Fin X.D → Fin X.N → K} {hs : X.IsGood s}
    {δ : ℕ} (Co : Coord X.toGeo hs δ) {a : ℕ} (haT : a ≤ X.T) (α : MonoDeg (Fin X.D) a)
    (m : X.Sec (X.T - a)) (hg : m ∈ X.global (X.T - a)) :
    ∃ f : filV X s a, (f.1 : X.Sec X.T) = mulPow X.toGeo s (Nat.sub_add_cancel haT) α m ∧
      ∀ α' p, symV Co a f (α', p) = if α'.1 = α.1 then Co.ev (X.T - a) (hs.res (X.T - a) m) p else 0 := by
  have hh : X.T - a + a = X.T := Nat.sub_add_cancel haT
  have hgl := GlobalTheory.HSCore.IntLift.mulPow_mem_global X.toGeo s hh α hg
  obtain ⟨f, hfeq⟩ : ∃ f : X.V X.T, (f : X.Sec X.T) = mulPow X.toGeo s hh α m := ⟨⟨_, X.global_le _ le_rfl hgl⟩, rfl⟩
  have hfF : (f : X.Sec X.T) ∈ Fil (X.ideal s) a (spaceV X s) := by
    refine (mem_Fil).2 ⟨Submodule.mem_sup_left ?_, ?_⟩
    · rw [hfeq]; exact hgl
    · rw [hfeq]; exact vanishesTo_mulMono _ _ _ _ _ _
  refine ⟨⟨f, hfF⟩, hfeq, fun α' p => ?_⟩
  have key : hs.sym hh (spaceV X s) ((X.V X.T).subtype.restrict (p := filV X s a) (q := Fil (X.ideal s) a (spaceV X s))
      (fun _ hx => hx) ⟨f, hfF⟩) = Pi.single α (hs.res (X.T - a) m) :=
    Vanishing.sym_mulMono _ _ _ _ _ _ _ _ _ _ α (m : X.Sec (X.T - a)) _ hfeq
  unfold symV
  rw [dite_eq_left haT]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.pi_apply, LinearEquiv.coe_coe, LinearMap.coe_proj,
    Function.eval]
  rw [key]
  by_cases hα : α' = α
  · subst hα; simp
  · rw [if_neg (fun h => hα (Subtype.ext h)), Pi.single_eq_of_ne hα, map_zero]; rfl

theorem totSym_incl {K : Type} [Field K] [NumberField K] {X : Data K} {s : Fin X.D → Fin X.N → K} {hs : X.IsGood s}
    {δ : ℕ} (Co : Coord X.toGeo hs δ) (a : ℕ) (f : filV X s a) (y : totFil X s a) (h : y.1 = incl X X.T f.1) :
    totSym Co a y = symV Co a f := by
  have : y = Submodule.equivMapOfInjective _ (incl_injective X X.T) (filV X s a) f := Subtype.ext h
  rw [this]
  exact congrArg (symV Co a) (LinearEquiv.symm_apply_apply _ f)

theorem totSym_mono : ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), X.MulStable → ∀ a < X.T - X.D, ∀ (α : MonoDeg (Fin X.D) a) (l : Fin (X.T - a) → Fin X.N → K), ∀ m ∈ LinearMap.range (incl X 0), ∃ h : pw (shift X.toGeo) s α.1 (word (shift X.toGeo) l m) ∈ totFil X s a, ∀ α' p, totSym Co a ⟨_, h⟩ (α', p) = if α'.1 = α.1 then (∏ q, ∑ k, l q k * Co.y p k) * totRes Co m p else 0 := by
  intro K _ _ X s hs δ Co _ a ha α l m hm
  obtain ⟨m₀, rfl⟩ := hm
  have haT : a ≤ X.T := by omega
  have hm₀ : (m₀ : X.Sec 0) ∈ X.global 0 := (SetLike.ext_iff.1 X.V_zero _).1 m₀.2
  have H : ∀ (t k : ℕ) (_ : 0 + t = k) (u : Fin t → Fin X.N → K), ∃ x' ∈ X.global k,
      word (shift X.toGeo) u (Pi.single 0 (m₀ : X.Sec 0)) = Pi.single k x' ∧ ∀ p,
        Co.ev k (hs.res k x') p = (∏ q, ∑ j, u q j * Co.y p j) * Co.ev 0 (hs.res 0 m₀) p := by
    intro t k h u
    subst h
    obtain ⟨x', h1, h2, h3⟩ := _root_.GlobalTheory.HSShort.GlobWord.word_global K X.toGeo t 0 u _ hm₀
    exact ⟨x', h1, h2, h3 s hs δ Co⟩
  obtain ⟨x', h1, h2, h3⟩ := H _ _ (Nat.zero_add _) l
  obtain ⟨f, hf, hsym⟩ := exists_filV_mulPow X Co haT α x' h1
  have e : pw (shift X.toGeo) s α.1 (word (shift X.toGeo) l (incl X 0 m₀)) = incl X X.T f.1 := by
    change pw (shift X.toGeo) s α.1 (word (shift X.toGeo) l (Pi.single 0 (m₀ : X.Sec 0))) =
      Pi.single X.T (f.1 : X.Sec X.T)
    rw [h2, hf]
    exact (_root_.GlobalTheory.HSShort.shift_comm_single_mono K X.toGeo).2.2 s a _ _ _ α x'
  refine ⟨⟨f.1, f.2, e.symm⟩, fun α' p => ?_⟩
  rw [totSym_incl Co a f _ e, hsym, h3]
  have : totRes Co (incl X 0 m₀) = Co.ev 0 (hs.res 0 m₀) := by simp [totRes, incl]
  rw [this]

end GlobalTheory.HSShort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairLatticeLocalSplitStatement
section
open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperbolic_pair_lattice_local_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (x y : Matrix (Fin n) (Fin 1) E), cT (σ : E →+* E) x * J * x = 0 → cT (σ : E →+* E) y * J * y = 0 → cT (σ : E →+* E) x * J * y = 1 → cT (σ : E →+* E) y * J * x = 1 → ∀ (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E L → ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → IsSelfDualAt σ J L v → ∀ g : GLoc σ J v, ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ g = q * k ∧ ∃ β : GL (Fin 1) (Fv F v ⊗[F] E), (matHom _ σ J q).1 * x.map (inclR (F := F) (Fv F v)) = x.map (inclR (F := F) (Fv F v)) * β.1 := by
  intro F E _ _ _ _ _ σ h n J hJ x y hxx hyy hxy hyx L hLat v hv hL g
  first
  | exact GlobalTheory.IwSplitLine.iwasawa_line_split F E σ h n J hJ x y hxx hyy hxy hyx L hLat v hv hL g
  | exact GlobalTheory.IwSplitLine.iwasawa_line_split F E σ h n J hJ x y hxx hyy hxy hyx L hLat.toIsLattice v hv hL g
end

