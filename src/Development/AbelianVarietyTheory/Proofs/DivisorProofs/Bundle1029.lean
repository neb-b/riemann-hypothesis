module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0994
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1006
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeEqZeroOfTorusLawAtOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicIndefiniteSkewHermitianCm
section
open scoped TensorProduct Matrix nonZeroDivisors
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.PlaneSkew

noncomputable section
namespace GlobalTheory.PlaneSkew

theorem exists_re_pos_of_congr_diagonal {n : ℕ} (H Q : Matrix (Fin n) (Fin n) ℂ) (δ : Fin n → ℂ)
    (hQ : Q.det ≠ 0) (hd : Qᵀ * H * Q.map star = Matrix.diagonal δ)
    (u : Fin n → ℂ) (hu : 0 < (u ⬝ᵥ H *ᵥ star u).re) : ∃ i, 0 < (δ i).re := by
  by_contra hneg
  push_neg at hneg
  obtain ⟨v, rfl⟩ : ∃ v, Q *ᵥ v = u :=
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det Q).mpr (isUnit_iff_ne_zero.mpr hQ)) u
  have hs : star (Q *ᵥ v) = Q.map star *ᵥ star v := by
    ext i
    simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
  have key : (Q *ᵥ v) ⬝ᵥ H *ᵥ star (Q *ᵥ v) = v ⬝ᵥ (Qᵀ * H * Q.map star) *ᵥ star v := by
    rw [hs, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec v Qᵀ,
      Matrix.vecMul_transpose]
  rw [key, hd] at hu
  have h2 : v ⬝ᵥ Matrix.diagonal δ *ᵥ star v = ∑ i, δ i * (Complex.normSq (v i) : ℂ) := by
    simp only [dotProduct, Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    simp [Pi.star_apply]
    ring
  rw [h2, Complex.re_sum] at hu
  refine hu.not_ge (Finset.sum_nonpos fun i _ => ?_)
  rw [Complex.re_mul_ofReal]
  exact mul_nonpos_of_nonpos_of_nonneg (hneg i) (Complex.normSq_nonneg _)

theorem exists_algebraMap_eq_of_fixed {F E : Type} [Field F] [Field E] [CharZero E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (σ : E →ₐ[F] E) {ξ : E} (hξ0 : ξ ≠ 0) (hξ : σ ξ = -ξ) {e : E}
    (he : σ e = e) : ∃ a : F, algebraMap F E a = e := by
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  set V : Submodule F E := LinearMap.ker (σ.toLinearMap - LinearMap.id) with hV
  have mem : ∀ x, x ∈ V ↔ σ x = x := fun x => by
    simp [hV, sub_eq_zero]
  have hle : Submodule.span F {(1 : E)} ≤ V := by
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem, map_one]
  have hne : V ≠ ⊤ := by
    intro htop
    have : ξ ∈ V := htop ▸ Submodule.mem_top
    rw [mem, hξ] at this
    have h2' : (2 : E) * ξ = 0 := by linear_combination -this
    rcases mul_eq_zero.mp h2' with h | h
    · exact two_ne_zero h
    · exact hξ0 h
  have hlt := Submodule.finrank_lt hne
  have h1 : Module.finrank F (Submodule.span F {(1 : E)}) = 1 := finrank_span_singleton one_ne_zero
  have heq := Submodule.eq_of_le_of_finrank_le hle (by omega)
  have : e ∈ Submodule.span F {(1 : E)} := heq ▸ (mem e).mpr he
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp this
  exact ⟨a, by rw [Algebra.algebraMap_eq_smul_one, ha]⟩

theorem re_embedding_algebraMap {F E : Type} [Field F] [Field E] [Algebra F E]
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w) (τ : E →+* ℂ) (a : F) :
    (τ (algebraMap F E a)).re =
      ((emb (InfinitePlace.mk (τ.comp (algebraMap F E)))).1 (algebraMap F E a)).re := by
  have h1 := congrArg (fun f : F →+* ℂ => f a) (emb (InfinitePlace.mk (τ.comp (algebraMap F E)))).2
  simp only [RingHom.comp_apply] at h1
  rw [h1]
  rcases InfinitePlace.embedding_mk_eq (τ.comp (algebraMap F E)) with h | h
  · rw [h, RingHom.comp_apply]
  · rw [h, ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, Complex.conj_re]

theorem exists_isotropic_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r s : ℕ), (∀ i j, σ (J j i) = -J i j) →
    (∀ w, HasSig (Complex.I • J.map (B.emb w).1) r s) → 1 ≤ r → 1 ≤ s → 3 ≤ n →
    ∃ x : Fin n → E, x ≠ 0 ∧ form σ J x x = 0 := by
  intro F E _ _ _ _ _ σ B hcm n J r s hJ hsig hr hs hn
  obtain ⟨hTR, hTC, h2, hconj⟩ := hcm
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσσ : ∀ x, σ (σ x) = x := fun x => τ₀.injective (by rw [hconj, hconj, star_star])
  by_cases hd : J.det = 0
  · obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    refine ⟨fun i => σ (v i), fun h => hv0 (funext fun i => ?_), ?_⟩
    · have := congrArg σ (congrFun h i)
      simpa [hσσ] using this
    · have : (fun i => σ ((fun i => σ (v i)) i)) = v := funext fun i => hσσ _
      simp only [form]
      rw [this, hv, dotProduct_zero]
  haveI := hTR
  haveI := hTC
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  haveI : IsCMField E := IsCMField.ofCMExtension F E
  have hcc : ∀ a, σ a = IsCMField.complexConj E a := fun a =>
    τ₀.injective (by rw [hconj, IsCMField.complexEmbedding_complexConj]; rfl)
  obtain ⟨x₀, hx₀⟩ : ∃ x, σ x ≠ x := by
    by_contra hno
    push_neg at hno
    apply IsCMField.complexConj_ne_one E
    ext x
    rw [← hcc, hno]
    rfl
  set ξ := x₀ - σ x₀ with hξdef
  have hξ : σ ξ = -ξ := by rw [hξdef, map_sub, hσσ]; ring
  have hξ0 : ξ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx₀)
  set G : Matrix (Fin n) (Fin n) E := ξ • J with hG
  have hform : ∀ x, GlobalTheory.UTrans.hf (σ : E →+* E) G x x = ξ * form σ J x x := fun x => by
    simp only [GlobalTheory.UTrans.hf, form, dotProduct, Matrix.mulVec, hG, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [AlgHom.coe_toRingHom]
    ring
  have hherm : GlobalTheory.UTrans.IsHerm (σ : E →+* E) G :=
    { invol := hσσ
      ne_id := ⟨x₀, hx₀⟩
      herm := fun a b => by
        simp only [AlgHom.coe_toRingHom, hG, Matrix.smul_apply, smul_eq_mul, map_mul, hξ, hJ]
        ring
      det_ne := by
        rw [hG, Matrix.det_smul]
        exact mul_ne_zero (pow_ne_zero _ hξ0) hd }
  have hh : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (G a b) = G b a := fun a b => by
    rw [← hherm.herm a b]
    simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, AlgHom.coe_toRingHom, hcc]
  obtain ⟨P, d, hP, hPg, hdfix, -⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hh
  have hPg' : Pᵀ * G * P.map σ = Matrix.diagonal d := by
    rw [← hPg]; congr 2; ext a b; simp [ReciprocityTheory.ChartRestriction.G.FD.cc, hcc]
  have hdσ : ∀ i, σ (d i) = d i := fun i => by
    rw [hcc]; exact hdfix i
  have hdiag : ∀ i, GlobalTheory.UTrans.hf (σ : E →+* E) G (fun a => P a i) (fun a => P a i) = d i := fun i => by
    have := congrFun (congrFun hPg' i) i
    rw [Matrix.diagonal_apply_eq] at this
    rw [← this]
    simp only [GlobalTheory.UTrans.hf, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Finset.sum_mul, AlgHom.coe_toRingHom]
    exact Finset.sum_comm

  have hsignE : ∀ w : InfinitePlace F,
      (∃ i, 0 < ((B.emb w).1 (d i)).re) ∧ ∃ j, ((B.emb w).1 (d j)).re < 0 := by
    intro w
    set φ : E →+* ℂ := (B.emb w).1 with hφ
    obtain ⟨hrs, A, hA⟩ := hsig w
    have hφσ : ∀ x, φ (σ x) = star (φ x) := hconj φ
    have hQ : (P.map φ).det ≠ 0 := by
      have h := RingHom.map_det φ P
      rw [RingHom.mapMatrix_apply] at h
      rw [← h]
      exact (map_ne_zero φ).mpr hP
    have hdQ : (P.map φ)ᵀ * G.map φ * (P.map φ).map star = Matrix.diagonal (fun i => φ (d i)) := by
      have e1 : (P.map φ).map star = (P.map σ).map φ := by
        ext a b
        simp [hφσ]
      rw [e1, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hPg',
        Matrix.diagonal_map (map_zero φ)]
    set c : ℂ := -Complex.I * φ ξ with hc
    have hGM : G.map φ = c • (Complex.I • J.map φ) := by
      ext a b
      simp only [hG, hc, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
      linear_combination (φ ξ * φ (J a b)) * Complex.I_sq
    have hcol : ∀ k, (fun a => A a k) ⬝ᵥ G.map φ *ᵥ star (fun a => A a k) =
        c * (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ) k k := by
      intro k
      rw [← hA, hGM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      congr 1
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, dotProduct,
        Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, Pi.star_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    have hφξ : (φ ξ).re = 0 := by
      have h1 := congrArg Complex.re (hφσ ξ)
      rw [hξ, map_neg, Complex.neg_re, Complex.star_def, Complex.conj_re] at h1
      linarith
    have hφξ0 : (φ ξ).im ≠ 0 := by
      intro him
      apply hξ0
      apply φ.injective
      rw [map_zero]
      exact Complex.ext hφξ him
    have hcre : c.re = (φ ξ).im := by simp [hc, hφξ]
    have pos : ∀ u, 0 < (u ⬝ᵥ G.map φ *ᵥ star u).re → ∃ i, 0 < (φ (d i)).re :=
      fun u hu => exists_re_pos_of_congr_diagonal _ _ _ hQ hdQ u hu
    have neg : ∀ u, (u ⬝ᵥ G.map φ *ᵥ star u).re < 0 → ∃ i, (φ (d i)).re < 0 := fun u hu => by
      obtain ⟨i, hi⟩ := exists_re_pos_of_congr_diagonal (-(G.map φ)) _ (fun i => -φ (d i)) hQ
        (by rw [Matrix.mul_neg, Matrix.neg_mul, hdQ, Matrix.diagonal_neg]) u
        (by rw [Matrix.neg_mulVec, dotProduct_neg, Complex.neg_re]; linarith)
      exact ⟨i, by simpa using hi⟩
    have v1 := hcol (Sum.inl ⟨0, by omega⟩)
    have v2 := hcol (Sum.inr ⟨0, by omega⟩)
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq,
      Matrix.neg_apply, mul_one, mul_neg] at v1 v2
    rcases lt_or_gt_of_ne hφξ0 with h | h
    · exact ⟨pos _ (by rw [v2, Complex.neg_re, hcre]; linarith),
        neg _ (by rw [v1, hcre]; exact h)⟩
    · exact ⟨pos _ (by rw [v1, hcre]; exact h),
        neg _ (by rw [v2, Complex.neg_re, hcre]; linarith)⟩
  have hre : ∀ (τ : E →+* ℂ) i, (τ (d i)).re =
      ((B.emb (InfinitePlace.mk (τ.comp (algebraMap F E)))).1 (d i)).re := fun τ i => by
    obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_fixed h2 σ hξ0 hξ (hdσ i)
    rw [← ha]
    exact re_embedding_algebraMap B.emb τ a
  obtain ⟨z, hz0, hz⟩ := GlobalTheory.UTrans.exists_isotropic_of_indefinite E n (σ : E →+* E) G
    (fun a => hcc a) hherm hn (fun τ => by
      obtain ⟨⟨i, hi⟩, j, hj⟩ := hsignE (InfinitePlace.mk (τ.comp (algebraMap F E)))
      exact ⟨⟨_, by rw [hdiag, hre]; exact hi⟩, _, by rw [hdiag, hre]; exact hj⟩)
  refine ⟨z, hz0, ?_⟩
  rw [hform] at hz
  exact (mul_eq_zero.mp hz).resolve_left hξ0

end GlobalTheory.PlaneSkew
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeModel
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR.LatSheaf

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]

def secGrp (M : X → AddSubgroup V) (U : X.Opens) : AddSubgroup V where
  carrier := {v | (∀ y ∈ U, v ∈ M y) ∧ (genericPoint X ∉ U → v = 0)}
  add_mem' := fun {a b} ha hb =>
    ⟨fun y hy => add_mem (ha.1 y hy) (hb.1 y hy), fun h => by rw [ha.2 h, hb.2 h, add_zero]⟩
  zero_mem' := ⟨fun y _ => zero_mem _, fun _ => rfl⟩
  neg_mem' := fun {a} ha => ⟨fun y hy => neg_mem (ha.1 y hy), fun h => by rw [ha.2 h, neg_zero]⟩

variable (M : X → AddSubgroup V)

theorem val_eq_zero {U : X.Opens} (h : genericPoint X ∉ U) (s : secGrp M U) : (s : V) = 0 := s.2.2 h


open Classical in
def resHom {U W : X.Opens} (e : W ≤ U) : secGrp M U →+ secGrp M W where
  toFun s := if h : genericPoint X ∈ W then ⟨(s : V), fun y hy => s.2.1 y (e hy), fun h' => (h' h).elim⟩
    else 0
  map_zero' := by split_ifs <;> rfl
  map_add' s t := by split_ifs <;> first | rfl | simp

open Classical in
theorem val_resHom {U W : X.Opens} (e : W ≤ U) (s : secGrp M U) :
    ((resHom M e s : secGrp M W) : V) = if genericPoint X ∈ W then (s : V) else 0 := by
  unfold resHom; simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]; split_ifs <;> rfl

theorem val_resHom_of_mem {U W : X.Opens} (e : W ≤ U) (h : genericPoint X ∈ W) (s : secGrp M U) :
    ((resHom M e s : secGrp M W) : V) = s := by rw [val_resHom, if_pos h]

def pre : TopCat.Presheaf Ab.{0} X where
  obj U := AddCommGrpCat.of (secGrp M U.unop)
  map f := AddCommGrpCat.ofHom (resHom M (leOfHom f.unop))
  map_id U := by
    ext s
    change ((resHom M le_rfl s : secGrp M U.unop) : V) = s
    rw [val_resHom]; split_ifs with h
    · rfl
    · exact (val_eq_zero M h s).symm
  map_comp f g := by
    ext s
    change ((resHom M (leOfHom (f ≫ g).unop) s : secGrp M _) : V) =
      ((resHom M (leOfHom g.unop) (resHom M (leOfHom f.unop) s) : secGrp M _) : V)
    rw [val_resHom, val_resHom, val_resHom]
    split_ifs with h1 h2 <;> first | rfl | exact (h2 (leOfHom g.unop h1)).elim

theorem sec_ext {U : X.Opens} {s t : secGrp M U} (h : genericPoint X ∈ U → (s : V) = t) : s = t := by
  by_cases hU : genericPoint X ∈ U
  · exact Subtype.ext (h hU)
  · exact Subtype.ext ((val_eq_zero M hU s).trans (val_eq_zero M hU t).symm)

def sv (U : (X.Opens)ᵒᵖ) (s : (pre M).obj U) : V := @Subtype.val V (· ∈ secGrp M U.unop) s

theorem sv_mem (U : (X.Opens)ᵒᵖ) (s : (pre M).obj U) : sv M U s ∈ secGrp M U.unop :=
  @Subtype.property V (· ∈ secGrp M U.unop) s

theorem sv_ext {U : (X.Opens)ᵒᵖ} {s t : (pre M).obj U} (h : genericPoint X ∈ U.unop → sv M U s = sv M U t) :
    s = t :=
  sec_ext M (U := U.unop) (s := s) (t := t) h

def mk (U : (X.Opens)ᵒᵖ) (v : V) (h : v ∈ secGrp M U.unop) : (pre M).obj U :=
  (⟨v, h⟩ : secGrp M U.unop)

@[simp] theorem sv_mk (U : (X.Opens)ᵒᵖ) (v : V) (h : v ∈ secGrp M U.unop) : sv M U (mk M U v h) = v := rfl

open Classical in
theorem sv_map {U W : (X.Opens)ᵒᵖ} (f : U ⟶ W) (s : (pre M).obj U) :
    sv M W ((pre M).map f s) = if genericPoint X ∈ W.unop then sv M U s else 0 :=
  val_resHom M (leOfHom f.unop) s

theorem isSheaf_pre : (pre M).IsSheaf := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  have key : ∀ k l, genericPoint X ∈ W k → genericPoint X ∈ W l →
      sv M _ (sf k) = sv M _ (sf l) := fun k l hk hl => by
    have := congrArg (sv M _) (hsf k l)
    rw [sv_map, sv_map, if_pos (show genericPoint X ∈ W k ⊓ W l from ⟨hk, hl⟩),
      if_pos (show genericPoint X ∈ W k ⊓ W l from ⟨hk, hl⟩)] at this
    exact this
  by_cases hg : genericPoint X ∈ iSup W
  · obtain ⟨k₀, hk₀⟩ := Opens.mem_iSup.1 hg
    have mem : sv M _ (sf k₀) ∈ secGrp M (iSup W) := by
      refine ⟨fun y hy => ?_, fun h => (h hg).elim⟩
      obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hy
      rw [key k₀ k hk₀ (gen_mem hk)]
      exact (sv_mem M _ (sf k)).1 y hk
    refine ⟨mk M (Opposite.op (iSup W)) _ mem, fun k => ?_, fun t ht => ?_⟩
    · refine sv_ext M fun hk => ?_
      rw [sv_map, if_pos hk, sv_mk]
      exact key k₀ k hk₀ hk
    · refine sv_ext M fun _ => ?_
      have := congrArg (sv M _) (ht k₀)
      rw [sv_map, if_pos hk₀] at this
      rw [sv_mk]
      exact this
  · refine ⟨mk M (Opposite.op (iSup W)) 0 (zero_mem _), fun k => ?_, fun t _ => ?_⟩
    · exact sv_ext M fun hk => (hg (Opens.mem_iSup.2 ⟨k, hk⟩)).elim
    · exact sv_ext M fun h => (hg h).elim

variable {M}
variable (hM : ∀ y (f : X.functionField) (v : V), RegAt y f → v ∈ M y → f • v ∈ M y)


open Classical in
def smulSec (U : X.Opens) (r : Γ(X, U)) (s : secGrp M U) : secGrp M U :=
  if h : genericPoint X ∈ U then
    ⟨fnOf U h r • (s : V), fun y hy => hM y _ _ (regAt_fnOf hy h r) (s.2.1 y hy), fun h' => (h' h).elim⟩
  else 0

theorem val_smulSec {U : X.Opens} (h : genericPoint X ∈ U) (r : Γ(X, U)) (s : secGrp M U) :
    (smulSec hM U r s : V) = fnOf U h r • (s : V) := by
  rw [smulSec, dite_eq_left h]

def secModule (U : X.Opens) : Module Γ(X, U) (secGrp M U) where
  smul := smulSec hM U
  one_smul s := sec_ext M fun h => by
    change (smulSec hM U 1 s : V) = s
    rw [val_smulSec hM h, map_one, one_smul]
  mul_smul a b s := sec_ext M fun h => by
    change (smulSec hM U (a * b) s : V) = smulSec hM U a (smulSec hM U b s)
    rw [val_smulSec hM h, val_smulSec hM h, val_smulSec hM h, map_mul, mul_smul]
  smul_zero a := sec_ext M fun h => by
    change (smulSec hM U a 0 : V) = ((0 : secGrp M U) : V)
    rw [val_smulSec hM h, ZeroMemClass.coe_zero, smul_zero]
  smul_add a s t := sec_ext M fun h => by
    change (smulSec hM U a (s + t) : V) = ((smulSec hM U a s + smulSec hM U a t : secGrp M U) : V)
    rw [AddSubgroup.coe_add, val_smulSec hM h, val_smulSec hM h, val_smulSec hM h, AddSubgroup.coe_add,
      smul_add]
  add_smul a b s := sec_ext M fun h => by
    change (smulSec hM U (a + b) s : V) = ((smulSec hM U a s + smulSec hM U b s : secGrp M U) : V)
    rw [AddSubgroup.coe_add, val_smulSec hM h, val_smulSec hM h, val_smulSec hM h, map_add (f := _), add_smul]
  zero_smul s := sec_ext M fun h => by
    change (smulSec hM U 0 s : V) = ((0 : secGrp M U) : V)
    rw [val_smulSec hM h, map_zero, zero_smul, ZeroMemClass.coe_zero]

theorem resHom_smulSec {U W : X.Opens} (e : W ≤ U) (r : Γ(X, U)) (s : secGrp M U) :
    resHom M e (smulSec hM U r s) = smulSec hM W (resG X e r) (resHom M e s) :=
  sec_ext M fun h => by
    rw [val_resHom_of_mem M e h, val_smulSec hM h, val_smulSec hM (e h), fnOf_resG,
      val_resHom_of_mem M e h]

def toMod : X.Modules :=
  letI : ∀ U, Module (X.ringCatSheaf.obj.obj U) ((pre M).obj U) := fun U => secModule hM U.unop
  { val := PresheafOfModules.ofPresheaf (pre M) fun _ _ f r m => resHom_smulSec hM (leOfHom f.unop) r m
    isSheaf := isSheaf_pre M }

def latModel : LatModel M (toMod hM) where
  val U _ := { toFun := fun s => sv M (Opposite.op U) s, map_zero' := rfl, map_add' := fun _ _ => rfl }
  inj U _ s t e := sv_ext M fun _ => e
  range U h := by
    ext v
    simp only [AddMonoidHom.mem_range, AddMonoidHom.coe_mk, ZeroHom.coe_mk, latSec,
      AddSubgroup.mem_iInf]
    constructor
    · rintro ⟨s, rfl⟩ y hy
      exact (sv_mem M _ s).1 y hy
    · intro hv
      exact ⟨mk M (Opposite.op U) v ⟨hv, fun h' => (h' h).elim⟩, rfl⟩
  res U W e h s := by
    exact (sv_map M (homOfLE e).op s).trans (if_pos h)
  smul U h r s := val_smulSec hM h r s

end GlobalTheory.LogDR.LatSheaf

theorem GlobalTheory.LogDR.exists_latModel : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V]
    [Module X.functionField V] (M : X → AddSubgroup V),
    (∀ y (f : X.functionField) (v : V), RegAt y f → v ∈ M y → f • v ∈ M y) →
      ∃ F : X.Modules, Nonempty (LatModel M F) :=
  fun _ _ _ _ _ _ hM => ⟨LatSheaf.toMod hM, ⟨LatSheaf.latModel hM⟩⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationBigCellRelationFourierStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weilRepresentation_bigCell_relation_fourier : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure], ∃ κ : ℂ, κ ≠ 0 ∧ ∀ p ∈ sieg c ν, InCell c (weyl c ν * p * weyl c ν) → ∃ p₁ ∈ sieg c ν, ∃ p₂ ∈ sieg c ν, weyl c ν * p * weyl c ν = p₁ * weyl c ν * p₂ ∧ ∀ φ ∈ SB (Matrix α ν E), κ • fou c ψ Q μ (parFun c ψ χ Q (mat c p) (κ • fou c ψ Q μ φ)) = parFun c ψ χ Q (mat c p₁) (κ • fou c ψ Q μ (parFun c ψ χ Q (mat c p₂) φ)) := by
  first | exact @GlobalTheory.KSp.weyl_cell_relation | exact GlobalTheory.KSp.weyl_cell_relation | (intros; apply GlobalTheory.KSp.weyl_cell_relation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFrameCoeffRingQuotientPrime
section
open GlobalTheory.ExpFrame Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.FrameQuot

theorem finite_quot_prime (l : ℕ) [Fact l.Prime] (ι : Type) (N : ℕ) (F : Frame l ι N) (hF : F.Ok) :
    Finite (F.O ⧸ Ideal.span {((l : ℕ) : F.O)}) := by
  obtain ⟨hinj, L, hL, hrange⟩ := hF.ring
  haveI := hL
  have hmem : ∀ x : F.O, F.emb x ∈ L ∧ ‖F.emb x‖ ≤ 1 := fun x => by
    have hx : F.emb x ∈ Set.range F.emb := ⟨x, rfl⟩
    rw [hrange] at hx
    exact hx
  let f : F.O →+* integralClosure ℤ_[l] L :=
    { toFun := fun x => ⟨⟨F.emb x, (hmem x).1⟩,
        (GlobalTheory.mem_integralClosure_padicInt_iff L ⟨F.emb x, (hmem x).1⟩).2 (hmem x).2⟩
      map_one' := Subtype.ext (Subtype.ext (map_one F.emb))
      map_mul' := fun x y => Subtype.ext (Subtype.ext (map_mul F.emb x y))
      map_zero' := Subtype.ext (Subtype.ext (map_zero F.emb))
      map_add' := fun x y => Subtype.ext (Subtype.ext (map_add F.emb x y)) }
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨y, hyL⟩, hy⟩
    have hn := (GlobalTheory.mem_integralClosure_padicInt_iff L ⟨y, hyL⟩).1 hy
    have hy' : y ∈ Set.range F.emb := by
      rw [hrange]
      exact ⟨hyL, hn⟩
    obtain ⟨x, rfl⟩ := hy'
    exact ⟨x, rfl⟩
  have hbij : Function.Bijective f :=
    ⟨fun x y h => hinj (congrArg (fun z : integralClosure ℤ_[l] L => ((z : L) : PadicAlgCl l)) h), hsurj⟩
  let e := RingEquiv.ofBijective f hbij
  have hfin : Finite (integralClosure ℤ_[l] L ⧸
      Ideal.span {((l : ℕ) : integralClosure ℤ_[l] L) ^ 1}) :=
    GlobalTheory.LocalIntegers.finite_quotient_pow l (integralClosure ℤ_[l] L) 1
  have hIJ : Ideal.span {((l : ℕ) : integralClosure ℤ_[l] L) ^ 1} =
      (Ideal.span {((l : ℕ) : F.O)}).map (e : F.O →+* integralClosure ℤ_[l] L) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast, pow_one]
  exact Finite.of_equiv _ (Ideal.quotientEquiv _ _ e hIJ).symm.toEquiv

end GlobalTheory.FrameQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedVectorSquaredBound
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_vector_squared_bound : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ (z : Fin G.n → ℂ), 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → ∃ K : ℝ, ∀ y : grp G β, FixL G v β y z → ∀ (w : InfinitePlace G.F) (i j : Fin G.n), ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i j‖ ^ 2 ≤ K * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
  first | (exact @GlobalTheory.LKCx.entries_sq_le_of_fixL) | (exact GlobalTheory.LKCx.entries_sq_le_of_fixL) | (intros; apply GlobalTheory.LKCx.entries_sq_le_of_fixL  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeEqZeroOfTorusLawAtOneStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicType_eq_zero_of_torus_law_at_one : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ f, HolFn Hm q x₀ w f → (∀ u ∈ UG Hm, ∀ s, f (torEl x₀ s * u) = torCh w s * f u) → f 1 = 0 → ∀ u ∈ UG Hm, f u = 0 := by
  first | exact @GlobalTheory.HolDict.Uniq.eq_zero_of_torus_law | exact GlobalTheory.HolDict.Uniq.eq_zero_of_torus_law | (intros; apply GlobalTheory.HolDict.Uniq.eq_zero_of_torus_law <;> assumption)
end

