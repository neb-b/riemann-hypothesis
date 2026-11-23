module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphism
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0941
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnitaryDiagonalLeOfEigenvalueBound
section
noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem re_inner_apply_le_of_eigen {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (R : ℝ)
    (hR : ∀ (x : ℝ) (v : E), v ≠ 0 → T v = (x : ℂ) • v → x ≤ R) (y : E) :
    (inner ℂ y (T y)).re ≤ R * (inner ℂ y y).re := by
  have hn : Module.finrank ℂ E = Module.finrank ℂ E := rfl
  set b := hT.eigenvectorBasis hn
  set ev := hT.eigenvalues hn
  have hb : ∀ i, T (b i) = ((ev i : ℝ) : ℂ) • b i := fun i => hT.apply_eigenvectorBasis hn i
  have hle : ∀ i, ev i ≤ R := fun i => hR _ _ (b.orthonormal.ne_zero i) (hb i)
  have h3 : ∀ i, inner ℂ y (b i) * inner ℂ (b i) y = ((‖inner ℂ (b i) y‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    rw [← inner_conj_symm (b i) y, Complex.norm_conj]
    first
      | (rw [Complex.mul_conj']; push_cast; rfl)
      | (rw [mul_comm, Complex.conj_mul']; push_cast; rfl)
  have h1 : inner ℂ y (T y) = ∑ i, ((ev i * ‖inner ℂ (b i) y‖ ^ 2 : ℝ) : ℂ) := by
    rw [← b.sum_inner_mul_inner y (T y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hT (b i) y, hb i, inner_smul_left, Complex.conj_ofReal, mul_left_comm, h3 i]
    push_cast; ring
  have h2 : inner ℂ y y = ∑ i, ((‖inner ℂ (b i) y‖ ^ 2 : ℝ) : ℂ) := by
    rw [← b.sum_inner_mul_inner y y]
    exact Finset.sum_congr rfl fun i _ => h3 i
  rw [h1, h2, Complex.re_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right (hle i) (by positivity)

section Block

variable {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

def blockSub (s : ι → Bool) (U : Submodule ℂ M) : Submodule ℂ (ι → M) where
  carrier := {y | ∀ c, y c ∈ U ∧ (s c = false → y c = 0)}
  add_mem' {x y} hx hy c := ⟨U.add_mem (hx c).1 (hy c).1, fun h => by simp [(hx c).2 h, (hy c).2 h]⟩
  zero_mem' c := ⟨U.zero_mem, fun _ => rfl⟩
  smul_mem' r x hx c := ⟨U.smul_mem r (hx c).1, fun h => by simp [(hx c).2 h]⟩

def blockOp (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M)
    (hst : ∀ a b, s a = s b → ∀ u ∈ U, F a b u ∈ U) : blockSub s U →ₗ[ℂ] blockSub s U where
  toFun y := ⟨fun a => if s a = true then ∑ b, F a b (y.1 b) else 0, fun c => by
    refine ⟨?_, fun h => by simp [h]⟩
    show (if s c = true then ∑ b, F c b (y.1 b) else 0) ∈ U
    split_ifs with hc
    · refine U.sum_mem fun b _ => ?_
      by_cases hb : s b = true
      · exact hst c b (hc.trans hb.symm) _ (y.2 b).1
      · rw [(y.2 b).2 (by simpa using hb), map_zero]; exact U.zero_mem
    · exact U.zero_mem⟩
  map_add' y z := by
    ext a
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]
    split_ifs <;> simp
  map_smul' r y := by
    ext a
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, RingHom.id_apply]
    split_ifs <;> simp [Finset.smul_sum]

theorem blockOp_apply (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M)
    (hst : ∀ a b, s a = s b → ∀ u ∈ U, F a b u ∈ U) (y : blockSub s U) (a : ι) :
    (blockOp s F U hst y : ι → M) a = if s a = true then ∑ b, F a b (y.1 b) else 0 := rfl

def blockCore (s : ι → Bool) (U : Submodule ℂ M) (ip : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (hsym : ∀ x ∈ U, ∀ y ∈ U, star (ip x y) = ip y x) (hpos : ∀ x ∈ U, x ≠ 0 → 0 < (ip x x).re) :
    InnerProductSpace.Core ℂ (blockSub s U) where
  inner y z := ∑ c, ip (y.1 c) (z.1 c)
  conj_inner_symm y z := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, starRingEnd_apply]
    exact Finset.sum_congr rfl fun c _ => hsym _ (z.2 c).1 _ (y.2 c).1
  re_inner_nonneg y := by
    simp only [RCLike.re_to_complex, Complex.re_sum]
    refine Finset.sum_nonneg fun c _ => ?_
    by_cases h : y.1 c = 0
    · simp [h]
    · exact (hpos _ (y.2 c).1 h).le
  add_left y z w := by simp [Finset.sum_add_distrib]
  smul_left y z r := by simp [Finset.mul_sum]
  definite y h := by
    have h' : ∑ c, (ip (y.1 c) (y.1 c)).re = 0 := by rw [← Complex.re_sum, h]; rfl
    have hnn : ∀ c ∈ Finset.univ, 0 ≤ (ip (y.1 c) (y.1 c)).re := fun c _ => by
      by_cases h : y.1 c = 0
      · simp [h]
      · exact (hpos _ (y.2 c).1 h).le
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h'
    ext c
    by_contra hc
    exact (hpos _ (y.2 c).1 hc).ne' (hz c (Finset.mem_univ c))

end Block

theorem re_diag_le_of_eigen_bound : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (U : Submodule ℂ M) (R : ℝ), UnitOn s F U → (∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, y a ∈ U) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → x ≤ R) → ∀ a, s a = true → ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, F a a u = m • u → m.re ≤ R := by
  intro ι M _ _ _ _ s F U R hU hR a ha u hu hu0 m hm
  obtain ⟨hfd, hst, ip, hsym, hpos, hadj⟩ := hU
  let cd := blockCore s U ip hsym hpos
  letI : NormedAddCommGroup (blockSub s U) := cd.toNormedAddCommGroup
  letI : InnerProductSpace ℂ (blockSub s U) := InnerProductSpace.ofCore cd.toCore
  haveI : FiniteDimensional ℂ U := hfd
  haveI : FiniteDimensional ℂ (blockSub s U) := by
    let e : blockSub s U →ₗ[ℂ] (ι → U) :=
      { toFun := fun y c => ⟨y.1 c, (y.2 c).1⟩
        map_add' := fun y z => rfl
        map_smul' := fun r y => rfl }
    exact Module.Finite.of_injective e
      (fun y z h => Subtype.ext (funext fun c => congrArg Subtype.val (congrFun h c)))
  have hinner : ∀ y z : blockSub s U, inner ℂ y z = ∑ c, ip (y.1 c) (z.1 c) := fun _ _ => rfl
  have key : ∀ (y z : blockSub s U) (c b : ι),
      ip (if s c = true then F c b (y.1 b) else 0) (z.1 c) =
        ip (y.1 b) (if s b = true then F b c (z.1 c) else 0) := by
    intro y z c b
    by_cases hc : s c = true
    · by_cases hb : s b = true
      · rw [if_pos hc, if_pos hb]
        exact hadj c b (hc.trans hb.symm) _ (y.2 b).1 _ (z.2 c).1
      · rw [if_pos hc, if_neg hb, (y.2 b).2 (by simpa using hb)]
        simp
    · rw [if_neg hc, (z.2 c).2 (by simpa using hc)]
      simp
  have hT : (blockOp s F U hst).IsSymmetric := by
    intro y z
    rw [hinner, hinner]
    simp only [blockOp_apply]
    have e1 : ∀ c, ip (if s c = true then ∑ b, F c b (y.1 b) else 0) (z.1 c) =
        ∑ b, ip (if s c = true then F c b (y.1 b) else 0) (z.1 c) := by
      intro c; split_ifs <;> simp [map_sum]
    have e2 : ∀ b, ip (y.1 b) (if s b = true then ∑ c, F b c (z.1 c) else 0) =
        ∑ c, ip (y.1 b) (if s b = true then F b c (z.1 c) else 0) := by
      intro b; split_ifs <;> simp [map_sum]
    simp only [e1, e2, key]
    exact Finset.sum_comm
  have hR' : ∀ (x : ℝ) (v : blockSub s U), v ≠ 0 → blockOp s F U hst v = (x : ℂ) • v → x ≤ R := by
    intro x v hv hTv
    refine hR x v.1 (fun h => hv (Subtype.ext h)) (fun c => (v.2 c).1) (fun c => (v.2 c).2) fun c hc => ?_
    have := congrFun (congrArg Subtype.val hTv) c
    rw [blockOp_apply, if_pos hc] at this
    exact this
  have hmem : Pi.single a u ∈ blockSub s U := by
    intro c
    by_cases hc : c = a
    · subst hc; simp only [Pi.single_eq_same]; exact ⟨hu, fun h => by simp [ha] at h⟩
    · rw [Pi.single_eq_of_ne hc]; exact ⟨U.zero_mem, fun _ => rfl⟩
  set y0 : blockSub s U := ⟨Pi.single a u, hmem⟩
  have hy0 : (y0 : ι → M) = Pi.single a u := rfl
  have hTa : (blockOp s F U hst y0 : ι → M) a = m • u := by
    rw [blockOp_apply, if_pos ha, hy0, Finset.sum_eq_single a, Pi.single_eq_same, hm]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  have i1 : inner ℂ y0 (blockOp s F U hst y0) = m * ip u u := by
    rw [hinner, Finset.sum_eq_single a, hTa, hy0, Pi.single_eq_same, map_smul, smul_eq_mul]
    · intro b _ hb; rw [hy0, Pi.single_eq_of_ne hb]; simp
    · intro h; exact absurd (Finset.mem_univ a) h
  have i2 : inner ℂ y0 y0 = ip u u := by
    rw [hinner, Finset.sum_eq_single a, hy0, Pi.single_eq_same]
    · intro b _ hb; rw [hy0, Pi.single_eq_of_ne hb]; simp
    · intro h; exact absurd (Finset.mem_univ a) h
  have hle := re_inner_apply_le_of_eigen hT R hR' y0
  rw [i1, i2] at hle
  have him : (ip u u).im = 0 := by
    have h := hsym u hu u hu
    have h2 := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at h2
    linarith
  have hp := hpos u hu hu0
  rw [Complex.mul_re, him, mul_zero, sub_zero] at hle
  exact le_of_mul_le_mul_right hle hp

end GlobalTheory.HoweR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmQuadraticCharacterEqProdRealSigns
section
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.EtaSignReal

open GlobalTheory.QuadSymbol GlobalTheory.IdeleNormChar GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem eq_signToCircle [Algebra.IsQuadraticExtension F E] (η : (AF F)ˣ →* Circle) (hη : IsEtaF E η) :
    η = signToCircle.comp (normSign E) := by
  obtain ⟨-, h1, h3, h4⟩ := hη
  refine eq_signToCircle_comp _ η (fun a ha => ?_) h4
  obtain ⟨t, x, hx⟩ := (normSign_eq_one_iff E a).1 ha
  rw [← div_mul_cancel a (toUnits F (AdeleRing (𝓞 F) F) t), map_mul, ← hx, h3 x, one_mul]
  exact h1 t

theorem finComp_eq_one {a : (AF F)ˣ} (ha : At (evI F) ((a : AF F) - 1)) : finComp a = 1 := by
  have h := ha ((0 : Ainf F), (1 : Af F)) (by
    show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
    exact map_zero _)
  have h2 : ((a : AF F) - 1).2 = 0 := by
    have := congrArg Prod.snd h
    change (1 : Af F) * ((a : AF F) - 1).2 = 0 at this
    rwa [one_mul] at this
  have h3 : (a : AF F).2 = 1 := sub_eq_zero.1 (h2 : (a : AF F).2 - 1 = 0)
  funext v
  apply Units.ext
  change (a : AF F).2 v = 1
  rw [h3]
  rfl

theorem normSign_eq_prod [Algebra.IsQuadraticExtension F E] {a : (AF F)ˣ} (ha : finComp a = 1) :
    normSign E a = ∏ w : InfinitePlace F, eta F E w.Completion (infComp a w) := by
  change etaProd F E (finComp a) (infComp a) = _
  rw [etaProd, ha]
  have : ∀ v : HeightOneSpectrum (𝓞 F), eta F E (v.adicCompletion F) ((1 : FinFam F) v) = 1 :=
    fun v => eta_eq_one_iff.2 (one_mem _)
  simp only [this, finprod_one, one_mul]

theorem ringEquivReal_neg {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (hw : w.IsReal)
    (τ : EmbOver E w) {δ : F} (hδ : δ ≠ 0) {θ : E} (hθ : σ θ = -θ) (h1 : θ * θ = algebraMap F E δ) :
    InfinitePlace.Completion.ringEquivRealOfIsReal hw (algebraMap F w.Completion δ) < 0 := by
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  set z := τ.1 θ
  have hz : star z = -z := by rw [← hcm.2.2.2 τ.1 θ, hθ, map_neg]
  have hre : z.re = 0 := by
    have := congrArg Complex.re hz
    simp at this
    linarith
  have hc : ((e (algebraMap F w.Completion δ) : ℝ) : ℂ) = z * z := by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
    have h5 : InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion δ) = w.embedding δ := by
      rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
        Algebra.algebraMap_self_apply, InfinitePlace.Completion.extensionEmbedding_coe]
      rfl
    rw [h5, ← τ.2, RingHom.comp_apply, ← h1, map_mul]
  have hr := congrArg Complex.re hc
  simp only [Complex.ofReal_re, Complex.mul_re, hre, zero_mul, zero_sub] at hr
  have hne : e (algebraMap F w.Completion δ) ≠ 0 := (map_ne_zero e).2 ((map_ne_zero _).2 hδ)
  refine lt_of_le_of_ne ?_ hne
  rw [hr]
  nlinarith [mul_self_nonneg z.im]

theorem mem_normGroup_iff_pos {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (hw : w.IsReal)
    (τ : EmbOver E w) (x : (w.Completion)ˣ) :
    x ∈ normGroup F E w.Completion ↔
      0 < InfinitePlace.Completion.ringEquivRealOfIsReal hw (x : w.Completion) := by
  have hinv : ∀ x, σ (σ x) = x := fun x => τ.1.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hne : ∃ x, σ x ≠ x := by
    by_contra h
    push_neg at h
    haveI := hcm.2.1
    refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ.1)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
    exact (hcm.2.2.2 τ.1 x).symm.trans (by rw [h x])
  obtain ⟨δ, b, hδ, h0, hσb, h1⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hcm.2.2.1 hinv hne
  have hδ0 : δ ≠ 0 := fun h => hδ (h ▸ IsSquare.zero)
  have hneg := ringEquivReal_neg hcm hw τ hδ0 hσb h1
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  rw [mem_normGroup_iff_form b h0 h1]
  constructor
  · rintro ⟨p, q, h⟩
    have hx0 : e (x : w.Completion) ≠ 0 := (map_ne_zero e).2 x.ne_zero
    have h2 : e (x : w.Completion) = e p ^ 2 - e (algebraMap F w.Completion δ) * e q ^ 2 := by
      rw [h, map_sub, map_mul, map_pow, map_pow]
    refine lt_of_le_of_ne ?_ hx0.symm
    rw [h2]
    nlinarith [sq_nonneg (e p), sq_nonneg (e q)]
  · intro hpos
    refine ⟨e.symm (Real.sqrt (e x)), 0, ?_⟩
    apply e.injective
    simp [Real.sq_sqrt hpos.le]

theorem piInf_idFF {w : InfinitePlace F} (hw : w.IsReal) (τ : EmbOver E w) (a : (AF F)ˣ) :
    piInf τ ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion) : ℝ) : ℂ) := by
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
  change infEmb τ (compInf F E w (algebraMap (AF F) (AF F ⊗[F] E) a)) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply]
  change infEmb τ (evInf F w a ⊗ₜ[F] (1 : E)) = _
  rw [infEmb_tmul, map_one, mul_one]
  rfl

theorem eta_eq_prod_sign : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ η : (AF F)ˣ →* Circle, IsEtaF E η → ∀ a : (AF F)ˣ, At (evI F) ((a : AF F) - 1) →
      (η a : ℂ) = ∏ w, piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) /
        ((‖piInf (B.emb w) ((idFF F E a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)‖ : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ σ B hB η hη a ha
  have hcm := hB.cm
  haveI : Algebra.IsQuadraticExtension F E := ⟨hcm.2.2.1⟩
  haveI := hcm.1
  rw [eq_signToCircle η hη, MonoidHom.comp_apply, normSign_eq_prod (finComp_eq_one ha), map_prod]
  rw [show ((∏ w : InfinitePlace F, signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) =
      ∏ w : InfinitePlace F, ((signToCircle (eta F E w.Completion (infComp a w)) : Circle) : ℂ) from
    map_prod Circle.coeHom _ _]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hw : w.IsReal := IsTotallyReal.isReal w
  rw [piInf_idFF hw]
  set r := InfinitePlace.Completion.ringEquivRealOfIsReal hw ((infComp a w : (w.Completion)ˣ) : w.Completion)
  have hx := mem_normGroup_iff_pos hcm hw (B.emb w) (infComp a w)
  have hr0 : r ≠ 0 := (map_ne_zero _).2 (infComp a w).ne_zero
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hpos : 0 < r
  · rw [eta_eq_one_iff.2 (hx.2 hpos), map_one, abs_of_pos hpos, div_self (by exact_mod_cast hr0)]
    rfl
  · have hneg : r < 0 := lt_of_le_of_ne (not_lt.1 hpos) hr0
    rw [eta_eq_neg_one_iff.2 (fun h => hpos (hx.1 h)), abs_of_neg hneg]
    change ((if (-1 : ℤˣ) = 1 then (1 : Circle) else -1 : Circle) : ℂ) = _
    rw [if_neg (by decide)]
    push_cast
    rw [div_neg, div_self (by exact_mod_cast hr0)]

end GlobalTheory.EtaSignReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
section
noncomputable section

namespace GlobalTheory.ThK.UnipDom

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def fA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → AE F E) : AE F E :=
  v ⬝ᵥ (incM F J *ᵥ fun i => cA σ (w i))

def coA (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) (g : UA σ J) :
    Fin d₁ → AE F E :=
  fun j => fA σ J (mat g *ᵥ (incM F H'.ι *ᵥ Pi.single j 1)) (incV F H'.y)

def coC (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) (g : UA σ J) : AE F E :=
  fA σ J (mat g *ᵥ incV F H'.y) (incV F H'.y)

end GlobalTheory.ThK.UnipDom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH

noncomputable section

namespace GlobalTheory.Poinc.Tors

def LiesOver {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (w₀ : W0 U) (g : GtPtF D.toPre F) (w : Frm D.toPre F 1 g.b)
    (x : TFK (R := R) F ⟶ A.A) (fr : FrAt x) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ wk : Frm D.toPre F k g.b,
    (∀ z J, Good D.toPre.P.L z J → val wk (𝟙 _) z J = val w (𝟙 _) z J ^ k) → wk.IsGen →
    ∀ (s : SecA A F k) (s' : Fam D.toPre F k) (v : F),
      U.ExpandsF F k w₀ s s' → ValAt s x fr v → SumF I F (coef s' g wk) v

section
open GlobalTheory.UT.PullExp GlobalTheory.FieldBaseChange

theorem coef_twistPull : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], ∀ (E : EndU U.toUnifPre), Function.Injective E.h → ∀ (k' k : ℕ), 1 ≤ k → 1 ≤ k' → (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(k' : ℤ), -(k : ℤ)]), β.IsGen) → (∃ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ) ∧ ∀ (w₀ : W0 U.toUnifPre) (ρ), NormW U.toUnifPre w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') s s', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ → ∀ (g g' : GtPtF D.toPre F), E.Act g g' → ∀ (w' : Frm D.toPre F k' g.b) (w : Frm D.toPre F k g'.b), w'.IsGen → w.IsGen → (∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J * val κ g.b.left z J = val w (𝟙 _) z J) → (∀ χ, coef s' g w' (E.h χ) = coef s g' w χ) ∧ ∀ β, β ∉ Set.range E.h → coef s' g w' β = 0 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ E hh k' k hk hk' ⟨β₀, hβ₀⟩
  have hGF := hL.1.globalFns
  have := hI.1
  have := hI.2.2.2
  have := E.homG
  obtain ⟨β, hβ, hβ'⟩ := exists_normalised U.LG.isLB E.aG k' k β₀ hβ₀
  obtain ⟨κ₀, hκ₀, hrel⟩ := GlobalTheory.T.descent_powerIso_endomorphism_abelianPart_uniformization hL R I hI D A G hG U E k' k β hβ hβ'
  refine ⟨⟨κ₀, hκ₀⟩, ?_⟩
  intro w₀ ρ hw ψ m hm hψ hm' α hα hα' t t' s s' ⟨v, hv, n, c, σ, f, h₁, h₂, h₃⟩ ⟨v', hv', hs'⟩ htw κ hκ g g' hg w' w hw' hw₁ hww
  choose σ' f' p₁ p₂ p₃ p₄ using fun i => GlobalTheory.T.pullback_section_endomorphism_expansion R I D A G U.toUnifPre E hh k' k β hβ κ₀ hκ₀.1 hrel (σ i) (f i) (h₁ i)
  have tw := GlobalTheory.T.endU_twist_of_iso hGF R I D A G U.toUnifPre E F k' k β hβ hβ' w₀ ρ hw ψ m hm hψ hm' α hα hα' t t' v v' hv hv' htw
  have H := secLin_of_expandsG U.toUnifPre (IsAdicComplete.le_jacobson_bot I) F k' v' s' hs' n c σ' f' p₁
    ((secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => by
      rw [tw y J hJ, GlobalTheory.BoxExpansion.secLin_val h₂ _ y hJ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e₁ : ((TFK (R := R) F) ◁ (Over.pullback (jK R)).map E.aG).left ≫
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
        rw [← Over.comp_left, whiskerLeft_fst]
      have e₂ : ((TFK (R := R) F) ◁ (Over.pullback (jK R)).map E.aG).left ≫ UnifPre.gFK (G := G) F =
          UnifPre.gFK (G := G) F ≫ E.aG.left := by
        rw [UnifPre.gFK, ← Category.assoc, ← Over.comp_left, whiskerLeft_snd, Over.comp_left, Category.assoc,
          Category.assoc]
        exact congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)
      rw [p₂ i _ _ y J hJ, gs_scal, gs_scal, e₁, e₂, Category.id_comp, Category.id_comp, _root_.mul_assoc])
  refine ⟨fun χ => CoefBasic.coef_eq fun z J hJ => ?_, fun b hb => CoefBasic.coef_eq fun z J hJ => ?_⟩
  · have a := CoefBasic.isCoef_coef g' hw₁ χ s z J hJ
    have e : g.b.left ≫ D.toPre.P.A.hom = (TF (R := R) F).hom := Over.w g.b
    have e' : g'.b.left = g.b.left ≫ E.aB.left := congrArg (fun q => q.left) hg.1
    rw [sval_comb (h₃ χ) _ z hJ, hg.2 χ z J hJ, ← hww z J hJ, e', normd_val_eq hGF hκ hκ₀ _ z J hJ] at a
    rw [sval_comb (H (E.h χ)) _ z hJ]
    simp only [p₃ _ χ _ _ z J hJ, e, ← _root_.mul_assoc, ← Finset.sum_mul]
    have e₃ : (rigV D.toPre (TF (R := R) F).hom z J).val ^ k' =
        (rigV D.toPre (TF (R := R) F).hom z J).val ^ k * (rigV D.toPre (TF (R := R) F).hom z J ^ ((k' : ℤ) - k)).val := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_natCast,
        ← zpow_add, add_sub_cancel]
    rw [e₃, ← _root_.mul_assoc, a]
    simp only [Units.val_mul]
    ring
  · rw [sval_comb (H b) _ z hJ, CoefBasic.cst_eq, map_zero, zero_mul, Finset.sum_eq_zero, zero_mul, zero_mul]
    intro i _
    exact (congrArg _ ((congrArg (gs _ z _) (p₄ i b hb _)).trans (gs_zero' _ z _ (hJ.mem _ _)))).trans (mul_zero _)

end

section
open GlobalTheory.UT.EvalZero GlobalTheory.UT.CoefBasic GlobalTheory.ExpansionValueZero GlobalTheory.BoxExpansion

theorem sumF_origin : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], (∃ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen) ∧ (∀ ρ : LB.Gen (A.L.pull (eSec A.A)), ρ.IsGen → ∃ w₀, NormW U.toUnifPre w₀ ρ) ∧ ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (k : ℕ) (t : SecA A F k) s, U.ExpandsF F k w₀ t s → ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b), g.IsZero → FrmOne w → ∀ c : F, (∀ z J, Good A.L z J → sA t (ptSecT A.A 1).left z J = @id ((TFK (R := R) F).left.presheaf.stalk z) (cst (R := R) F z c) * (val (rigT A.A A.L ρ (TFK (R := R) F) (k : ℤ)) (𝟙 _) z J).val) → SumF I F (coef s g w) c := by
  intro _ R _ _ _ I hI D A G _ _ _ U F _ _
  refine ⟨exists_gen_pt (Y := Spec (CommRingCat.of (FractionRing R))) A.isLB
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
      (fun y => Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _) _ _,
    exists_normW U.toUnifPre, ?_⟩
  rintro w₀ ρ h k t s ⟨σ', hR, n, c, σ, f, hE, hσ, hs⟩ g w hg hw b hb
  choose a ha using fun i α => exists_value D.toPre k α (f i α)
  choose x hx using fun i => exists_coeff (A := R) U.LG.isLB (σ i) (eSec G) (GeneratorPullback.powGen U.LG.L _ _ U.LG.rig k)
    (powGen_isGen _ _ _ _ U.LG.rigGen k) (fun W _ f => by simp)
  have hx' : ∀ i (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J), Good U.LG.L z J →
      sval (σ i) (r ≫ eSec G) z J = Geo.Tor.cst r z (x i) * (val (L := U.LG.L) U.LG.rig r z J ^ k).val :=
    fun i Z r z J hJ => (hx i Z r z J hJ).trans (by rw [val_pow])
  rw [value_comb U.toUnifPre F h t σ' hR c σ hσ x hx' b hb,
    funext fun α => coef_comb F s c f α (hs α) (fun i => a i α) (fun i => ha i α) g w hg hw]
  exact sumF_comb hI F _ c _ _ fun i => sumF_map I F (a i) (x i) fun e =>
    value_sub_sum_mem U.toUnifPre e k (σ i) (f i) (hE i e) (x i) (hx' i) (a i) (ha i)

end

end GlobalTheory.Poinc.Tors
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactConjCharpolyBoundedDenominatorsAwayPStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_conj_charpoly_bounded_denominators_awayP : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Ω : Set G.GAf), IsCompact Ω → ∃ D : ℕ, 0 < D ∧ ∀ (g : G.GAf) (y : G.C) (x : (AfP p ⊗[ℚ] G.C)ˣ), g ∈ Ω → (((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] G.C) = (x : AfP p ⊗[ℚ] G.C) * inC G (AfP p) y * ((x⁻¹ : (AfP p ⊗[ℚ] G.C)ˣ) : AfP p ⊗[ℚ] G.C)) → ∀ i, ∃ k : ℕ, ∃ a : ℤ, ((D * p ^ k : ℕ) : ℚ) * (LinearMap.mulLeft ℚ y).charpoly.coeff i = a := by
  first | (exact @GlobalTheory.AwayPDen.charpoly_den_bounded) | (exact GlobalTheory.AwayPDen.charpoly_den_bounded) | (intros; apply GlobalTheory.AwayPDen.charpoly_den_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactFiniteAdelesAwayPBoundedDenominatorsStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_finiteAdelesAwayP_bounded_denominators : ∀ (p : ℕ) [Fact p.Prime] (Q : Set (AfP p)), IsCompact Q → ∃ D : ℕ, 0 < D ∧ ∀ a ∈ Q, ∀ v : AwayP p, AfP.eval v ((D : AfP p) * a) ∈ v.1.adicCompletionIntegers ℚ := by
  first | (exact @GlobalTheory.DenAwayCpt.exists_nat_mul_integral_of_isCompact) | (exact GlobalTheory.DenAwayCpt.exists_nat_mul_integral_of_isCompact) | (intros; apply GlobalTheory.DenAwayCpt.exists_nat_mul_integral_of_isCompact  <;> assumption)
end

