module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Cntconj
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.cntconj :
    ∀ (L : Type) [Field L] [NumberField L] (R : ℕ),
    {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R}.Finite ∧
      {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R}.ncard ≤ (2 * R + 1) ^ Module.finrank ℚ L := by
  intro L _ _ R
  have hq : 2 * R + 1 ≠ 0 := by omega
  have hsep : ∀ a ∈ {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R}, ∀ b ∈ {a : 𝓞 L | ∀ w, ‖embO w a‖ ≤ R},
      ∀ x : 𝓞 L, a - b = (2 * R + 1) • x → a = b := by
    intro a ha b hb x hab
    by_cases hx : x = 0
    · rw [hx, smul_zero, sub_eq_zero] at hab
      exact hab
    exfalso
    have key : ∀ w : InfinitePlace L, w (x : L) < 1 := by
      intro w
      have h1 : ‖embO w (a - b)‖ ≤ 2 * R := by
        rw [map_sub]
        calc ‖embO w a - embO w b‖ ≤ ‖embO w a‖ + ‖embO w b‖ := norm_sub_le _ _
          _ ≤ R + R := add_le_add (ha w) (hb w)
          _ = 2 * R := by ring
      rw [hab, map_nsmul, nsmul_eq_mul, norm_mul, Complex.norm_natCast] at h1
      have hn : ‖embO w x‖ = w (x : L) := InfinitePlace.norm_embedding_eq w (x : L)
      rw [hn] at h1
      push_cast at h1
      by_contra hc
      push_neg at hc
      have : (2 * (R : ℝ) + 1) * 1 ≤ (2 * (R : ℝ) + 1) * w (x : L) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      linarith
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace L))
    have := InfinitePlace.one_le_of_lt_one (w := w0) hx (fun z _ => key z)
    linarith [key w0]
  obtain ⟨hfin, hcard⟩ := cardsep (𝓞 L) (2 * R + 1) hq _ hsep
  refine ⟨hfin, ?_⟩
  rwa [RingOfIntegers.rank] at hcard
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Exbasis
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.exbasis :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (M : Set (Lat L N)), Spans M →
    ∃ A : Matrix (Fin N) (Fin N) (𝓞 L), A.det ≠ 0 ∧ ∀ a, (fun i => A i a) ∈ M := by
  intro L _ _ N M hM
  classical
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent L (toL '' M)
  have htop : (⊤ : Submodule L (Fin N → L)) ≤ Submodule.span L (Set.range ((↑) : s → Fin N → L)) := by
    rw [Subtype.range_coe, hspan]
    exact hM.ge
  let B := Module.Basis.mk hli htop
  haveI : Fintype s := @Fintype.ofFinite s (Module.Finite.finite_basis B)
  have hcard : Fintype.card s = N := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e : Fin N ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ a, ∃ y ∈ M, toL y = (e a : Fin N → L) := fun a => hs (e a).2
  choose y hyM hy using hmem
  refine ⟨fun i a => y a i, ?_, fun a => hyM a⟩
  intro h0
  have hli' : LinearIndependent L (fun a => ((e a : s) : Fin N → L)) := hli.comp e e.injective
  let C : Matrix (Fin N) (Fin N) L := fun i a => ((e a : s) : Fin N → L) i
  have hC : IsUnit C := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli'
  let A : Matrix (Fin N) (Fin N) (𝓞 L) := fun i a => y a i
  have hCA : C = (algebraMap (𝓞 L) L).mapMatrix A := by
    ext i a
    simp only [C, A, RingHom.mapMatrix_apply, Matrix.map_apply, ← hy]
    rfl
  have hdet : C.det = algebraMap (𝓞 L) L A.det := by
    rw [hCA]
    exact (RingHom.map_det (algebraMap (𝓞 L) L) A).symm
  have h0' : A.det = 0 := h0
  rw [h0', map_zero] at hdet
  exact (Matrix.isUnit_iff_isUnit_det C |>.mp hC).ne_zero hdet
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Faceexact
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem UpperTheory.V.KT.fe_lift {X : Type} (s : Set X) (c : X →₀ ℤ)
    (hc : c ∈ Finsupp.supported ℤ ℤ s) :
    ∃ f : {t // t ∈ s} →₀ ℤ, Finsupp.mapDomain Subtype.val f = c := by
  have h := Finsupp.lmapDomain_supported ℤ ℤ (Subtype.val : {t // t ∈ s} → X) Set.univ
  rw [Set.image_univ, Subtype.range_coe_subtype, Set.setOf_mem_eq] at h
  rw [← h] at hc
  obtain ⟨f, -, hf⟩ := hc
  exact ⟨f, hf⟩

private theorem UpperTheory.V.KT.fe_mem {X : Type} (s : Set X) (f : {t // t ∈ s} →₀ ℤ) :
    Finsupp.mapDomain Subtype.val f ∈ Finsupp.supported ℤ ℤ s := by
  have h := Finsupp.lmapDomain_supported (M := ℤ) (R := ℤ) (Subtype.val : {t // t ∈ s} → X) Set.univ
  rw [Set.image_univ, Subtype.range_coe] at h
  rw [← h]
  exact Submodule.mem_map_of_mem (by simp [Finsupp.supported_univ])

private theorem UpperTheory.V.KT.fe_comm {I : Type} (S : ∀ n, Set (Fin n → I)) (hS : ConeExtensionAcyclic.FaceClosed S)
    (p : ℕ) (f : {t : Fin (p + 1) → I // t ∈ S (p + 1)} →₀ ℤ) :
    Finsupp.mapDomain Subtype.val
      (KH.faceD (fun (i : Fin (p + 1)) (t : {t : Fin (p + 1) → I // t ∈ S (p + 1)}) =>
        (⟨t.1 ∘ i.succAbove, hS _ t.1 t.2 i⟩ : {t : Fin p → I // t ∈ S p})) f) =
      ConeExtensionAcyclic.bd I p (Finsupp.mapDomain Subtype.val f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add (f := _), Finsupp.mapDomain_add, hf, hg, Finsupp.mapDomain_add, map_add (f := _)]
  | single t c =>
    rw [KH.faceD_single, Finsupp.mapDomain_single]
    simp only [ConeExtensionAcyclic.bd, Finsupp.linearCombination_single, Finset.smul_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finsupp.lmapDomain_apply ℤ ℤ, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_zsmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [mul_comm]

private theorem UpperTheory.V.KT.fe_aug {I : Type} (s : Set (Fin 1 → I)) (f : {t // t ∈ s} →₀ ℤ) :
    ConeExtensionAcyclic.bd I 0 (Finsupp.mapDomain Subtype.val f) =
      Finsupp.single (Fin.elim0 : Fin 0 → I) (KH.aug _ f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add, map_add (f := _), hf, hg, map_add (f := _), Finsupp.single_add]
  | single t c =>
    rw [Finsupp.mapDomain_single, KH.aug_single]
    simp only [ConeExtensionAcyclic.bd, Finsupp.linearCombination_single]
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    congr 1
    funext k
    exact Fin.elim0 k

theorem UpperTheory.V.KT.faceexact :
    ∀ (I : Type) (S : ∀ n, Set (Fin n → I)) (hS : ConeExtensionAcyclic.FaceClosed S), S 0 = Set.univ → ConeExtensionAcyclic.Acyc S → ∀ m : ℕ,
    KH.FaceExactTo (fun p => {t : Fin (p + 1) → I // t ∈ S (p + 1)})
      (fun p i t => ⟨t.1 ∘ i.succAbove, hS _ t.1 t.2 i⟩) m := by
  intro I S hS hS0 hA m
  obtain ⟨hA0, hAn⟩ := hA
  have inj : ∀ n, Function.Injective (Finsupp.mapDomain (M := ℤ) (Subtype.val : {t : Fin n → I // t ∈ S n} → (Fin n → I))) :=
    fun n => Finsupp.mapDomain_injective Subtype.val_injective
  refine ⟨?_, ?_, ?_⟩
  · have hc : Finsupp.single (Fin.elim0 : Fin 0 → I) (1 : ℤ) ∈ Finsupp.supported ℤ ℤ (S 0) := by
      rw [hS0, Finsupp.supported_univ]
      exact Submodule.mem_top
    obtain ⟨b, hb, hbc⟩ := hA0 _ hc
    obtain ⟨f, rfl⟩ := fe_lift (S 1) b hb
    rw [fe_aug] at hbc
    have h1 : KH.aug _ f = 1 := Finsupp.single_injective _ hbc
    intro n
    exact ⟨n • f, by rw [map_zsmul, h1, smul_eq_mul, mul_one]⟩
  · intro y
    constructor
    · intro hy
      have hc := fe_mem (S 1) y
      have hbd : ConeExtensionAcyclic.bd I 0 (Finsupp.mapDomain Subtype.val y) = 0 := by
        rw [fe_aug, hy, Finsupp.single_zero]
      obtain ⟨b, hb, hbc⟩ := hAn 0 _ hc hbd
      obtain ⟨g, rfl⟩ := fe_lift (S 2) b hb
      refine ⟨g, inj 1 ?_⟩
      rw [fe_comm S hS 1 g, hbc]
    · rintro ⟨g, rfl⟩
      have h := fe_aug (S 1) (KH.faceD (fun (i : Fin 2) (t : {t : Fin 2 → I // t ∈ S 2}) =>
        (⟨t.1 ∘ i.succAbove, hS _ t.1 t.2 i⟩ : {t : Fin 1 → I // t ∈ S 1})) g)
      rw [fe_comm S hS 1 g, ConeExtensionAcyclic.bd_bd] at h
      exact Finsupp.single_eq_zero.mp h.symm
  · intro p _ y
    constructor
    · intro hy
      have hc := fe_mem (S (p + 2)) y
      have hbd : ConeExtensionAcyclic.bd I (p + 1) (Finsupp.mapDomain Subtype.val y) = 0 := by
        rw [← fe_comm S hS (p + 1) y, hy, Finsupp.mapDomain_zero]
      obtain ⟨b, hb, hbc⟩ := hAn (p + 1) _ hc hbd
      obtain ⟨g, rfl⟩ := fe_lift (S (p + 3)) b hb
      refine ⟨g, inj (p + 2) ?_⟩
      rw [fe_comm S hS (p + 2) g, hbc]
    · rintro ⟨g, rfl⟩
      apply inj (p + 1)
      rw [fe_comm S hS (p + 1), fe_comm S hS (p + 2) g, ConeExtensionAcyclic.bd_bd, Finsupp.mapDomain_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Gramdet
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

@[to_additive]
private theorem UpperTheory.V.KT.prod_emb (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L]
    {M : Type} [CommMonoid M] (f : (L →+* ℂ) → M) :
    ∏ φ, f φ = ∏ w : InfinitePlace L, (f w.embedding * f (ComplexEmbedding.conjugate w.embedding)) := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk f]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := by
    intro e
    have := IsTotallyComplex.isComplex w
    rw [InfinitePlace.isComplex_iff] at this
    exact this (ComplexEmbedding.isReal_iff.mpr e.symm)
  rw [← Finset.prod_pair hne]
  congr 1
  ext φ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    rw [← InfinitePlace.mk_embedding w, eq_comm, InfinitePlace.mk_eq_iff] at h
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (rfl | rfl)
    · exact InfinitePlace.mk_embedding w
    · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

private theorem UpperTheory.V.KT.det_emb (L : Type) [Field L] [NumberField L] :
    star (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)).det *
      (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)).det =
      (absD L : ℂ) := by
  classical
  have hE : (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)) =
      ((basisMatrix L).submatrix (equivReindex L).symm (equivReindex L).symm)ᵀ := by
    ext k i
    simp [canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
  rw [hE, det_transpose, det_submatrix_equiv_self]
  have h := congrArg norm (discr_eq_basisMatrix_det_sq L)
  rw [norm_pow, Complex.norm_intCast] at h
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, ← h, absD, ← Int.cast_abs,
    ← Int.natCast_natAbs]
  rw [Int.cast_natCast, Complex.ofReal_natCast]

theorem UpperTheory.V.KT.gramdet :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ) (h : HS L N),
    2 ^ dd L N * (gram h).det = (absD L : ℝ) ^ N * (∏ w, (mat h w).det.re) ^ 2 := by
  intro L _ _ _ N h
  classical
  let A : (L →+* ℂ) → Matrix (Fin N) (Fin N) ℂ := fun φ =>
    if φ = (InfinitePlace.mk φ).embedding then mat h (InfinitePlace.mk φ)
    else (mat h (InfinitePlace.mk φ))ᵀ
  have hne : ∀ w : InfinitePlace L, ComplexEmbedding.conjugate w.embedding ≠ w.embedding := by
    intro w e
    have := IsTotallyComplex.isComplex w
    rw [InfinitePlace.isComplex_iff] at this
    exact this (ComplexEmbedding.isReal_iff.mpr e)
  have hA1 : ∀ w : InfinitePlace L, A w.embedding = mat h w := by
    intro w; simp [A, InfinitePlace.mk_embedding]
  have hA2 : ∀ w : InfinitePlace L, A (ComplexEmbedding.conjugate w.embedding) = (mat h w)ᵀ := by
    intro w; simp only [A, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, if_neg (hne w)]
  have key := UpperTheory.V.KT.blockdet (BI L) N
    (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L))
    (fun k => A ((equivReindex L).symm k))
  rw [UpperTheory.V.KT.det_emb, Equiv.prod_comp (equivReindex L).symm (fun φ => (A φ).det),
    UpperTheory.V.KT.prod_emb L] at key
  have hM : (Matrix.of fun s t : Fin N × BI L => ∑ k,
      star ((Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)) k s.2) *
        A ((equivReindex L).symm k) s.1 t.1 *
        (Matrix.of fun k i : BI L => ((equivReindex L).symm k) (RingOfIntegers.basis L i : L)) k t.2) =
      Complex.ofRealHom.mapMatrix ((2 : ℝ) • gram h) := by
    ext s t
    simp only [of_apply]
    rw [Equiv.sum_comp (equivReindex L).symm (fun φ => star (φ (RingOfIntegers.basis L s.2 : L)) *
      A φ s.1 t.1 * φ (RingOfIntegers.basis L t.2 : L)), UpperTheory.V.KT.sum_emb L]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hA1, hA2, RingHom.mapMatrix_apply, map_apply, Matrix.smul_apply, gram, of_apply,
      smul_eq_mul, Finset.mul_sum, map_sum, Complex.ofRealHom_eq_coe]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [← Complex.add_conj]
    have hh : mat h w t.1 s.1 = star (mat h w s.1 t.1) := ((mat_herm h w).apply t.1 s.1).symm
    simp [embO, hh, ComplexEmbedding.conjugate_coe_eq]
  rw [hM, ← RingHom.map_det, det_smul] at key
  have hc : Fintype.card (Fin N × BI L) = dd L N := by
    rw [Fintype.card_prod, Fintype.card_fin, ← Module.finrank_eq_card_chooseBasisIndex,
      RingOfIntegers.rank, mul_comm]
  have hd : ∀ w, (mat h w).det = ((mat h w).det.re : ℂ) := by
    intro w
    have : star (mat h w).det = (mat h w).det := by
      rw [← det_conjTranspose, (mat_herm h w).eq]
    exact (Complex.conj_eq_iff_re.mp this).symm
  simp only [hA1, hA2, det_transpose, hc] at key
  rw [Finset.prod_congr rfl fun w _ => by rw [hd w]] at key
  apply Complex.ofReal_injective
  rw [← Complex.ofRealHom_eq_coe, key, Finset.prod_mul_distrib]
  push_cast
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.LowbdSmul
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem lowbd_cont (L : Type) [Field L] [NumberField L] (N : ℕ) :
    Continuous (fun p : HS L N × VR L N => qR p.1 p.2) := by
  unfold qR mat
  simp only [dotProduct, mulVec, Matrix.of_apply, Pi.star_apply]
  have hv : Continuous fun p : HS L N × VR L N => (p.1 : InfinitePlace L → Fin N → Fin N → ℂ) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous fun p : HS L N × VR L N => (p.2 : InfinitePlace L → Fin N → ℂ) := continuous_snd
  refine continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_
  refine continuous_finsetSum _ fun i _ => ?_
  refine (continuous_star.comp ((continuous_apply i).comp ((continuous_apply w).comp hz))).mul ?_
  refine continuous_finsetSum _ fun j _ => ?_
  exact ((continuous_apply j).comp ((continuous_apply i).comp ((continuous_apply w).comp hv))).mul
    ((continuous_apply j).comp ((continuous_apply w).comp hz))

private theorem lowbd_smul {L : Type} [Field L] [NumberField L] {N : ℕ} (k : HS L N) (r : ℝ)
    (z : VR L N) : qR k (r • z) = r ^ 2 * qR k z := by
  unfold qR
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Pi.smul_apply, star_smul, star_trivial, mulVec_smul, dotProduct_smul, smul_dotProduct,
    Complex.smul_re, smul_eq_mul]
  ring

private theorem lowbd_pos {L : Type} [Field L] [NumberField L] {N : ℕ} {h : HS L N}
    (hh : h ∈ Pos L N) {z : VR L N} (hz : z ≠ 0) : 0 < qR h z := by
  have hne : ∃ w, z w ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hz (funext hc)
  obtain ⟨w0, hw0⟩ := hne
  have hp : ∀ w, (mat h w).PosDef := hh
  unfold qR
  apply Finset.sum_pos'
  · intro w _
    by_cases hw : z w = 0
    · simp [hw]
    · exact le_of_lt (Complex.pos_iff.mp ((hp w).dotProduct_mulVec_pos hw)).1
  · exact ⟨w0, Finset.mem_univ _, (Complex.pos_iff.mp ((hp w0).dotProduct_mulVec_pos hw0)).1⟩

theorem UpperTheory.V.KT.lowbd :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (h : HS L N), h ∈ Pos L N →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in nhds h, ∀ z : VR L N, c * ‖z‖ ^ 2 ≤ qR k z := by
  intro L _ _ N h hh
  have hK : IsCompact (Metric.sphere (0 : VR L N) 1) := isCompact_sphere 0 1
  have hcont := lowbd_cont L N
  have hsec : Continuous fun z : VR L N => (h, z) := by fun_prop
  obtain ⟨m, hm, hmle⟩ := hK.exists_forall_le' (f := fun z => qR h z)
    (hcont.comp hsec).continuousOn (a := 0)
    (fun z hz => lowbd_pos hh (by
      intro h0
      rw [h0] at hz
      simp at hz))
  refine ⟨m / 2, by positivity, ?_⟩
  have hev : ∀ᶠ k in nhds h, ∀ z ∈ Metric.sphere (0 : VR L N) 1, m / 2 < qR k z := by
    apply hK.eventually_forall_of_forall_eventually
    intro z hz
    have hlt : m / 2 < qR h z := by linarith [hmle z hz]
    exact (hcont.tendsto (h, z)).eventually (lt_mem_nhds hlt)
  filter_upwards [hev] with k hk z
  by_cases hz : z = 0
  · subst hz
    have h0 : qR k (0 : VR L N) = 0 := by simpa using lowbd_smul k 0 (0 : VR L N)
    simp [h0]
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hu : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : VR L N) 1 := by
      simp [norm_smul, hn.ne']
    have hzu : ‖z‖ • (‖z‖⁻¹ • z) = z := by
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hlt := hk _ hu
    calc m / 2 * ‖z‖ ^ 2 ≤ ‖z‖ ^ 2 * qR k (‖z‖⁻¹ • z) := by
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hlt.le (by positivity)
      _ = qR k (‖z‖ • (‖z‖⁻¹ • z)) := (lowbd_smul k ‖z‖ _).symm
      _ = qR k z := by rw [hzu]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Orbnum
section
open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

private theorem UpperTheory.V.KT.orbit_number_power_bound (D d N p : ℕ) (hD : 1 ≤ D) (hN : 1 ≤ N) (hd : N ≤ d) :
    (D ^ N * d ^ d) ^ (1 + d * N) *
      ((2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1) ^ (d * N * (p + 1)) ≤
    (2 * D * d) ^ (12 * (p + 1) * d ^ 3 * N) := by
  have hd1 : 1 ≤ d := le_trans hN hd
  set B := 2 * D * d with hBdef
  have hB2 : 2 ≤ B := by
    have : 1 ≤ D * d := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    rw [hBdef, mul_assoc]
    omega
  have hDB : D ≤ B := by
    rw [hBdef]
    nlinarith
  have hdB : d ≤ B := by
    rw [hBdef]
    nlinarith
  have hNB : N ≤ B := le_trans hd hdB
  have hX : D ^ N * d ^ d ≤ B ^ (2 * d) := by
    have a : D ^ N ≤ B ^ d :=
      le_trans (Nat.pow_le_pow_left hDB N) (Nat.pow_le_pow_right (by omega) hd)
    have b : d ^ d ≤ B ^ d := Nat.pow_le_pow_left hdB d
    calc D ^ N * d ^ d ≤ B ^ d * B ^ d := Nat.mul_le_mul a b
      _ = B ^ (2 * d) := by ring
  have hX1 : 1 ≤ D ^ N * d ^ d :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ (by omega)))
  have hNN : N ^ N ≤ B ^ d :=
    le_trans (Nat.pow_le_pow_left hNB N) (Nat.pow_le_pow_right (by omega) hd)
  have hNN1 : 1 ≤ N ^ N := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
  have f1 : (D ^ N * d ^ d) ^ (1 + d * N) ≤ B ^ (2 * d * (1 + d * N)) := by
    rw [pow_mul B]
    exact Nat.pow_le_pow_left hX _
  have hin : 2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1 ≤ B ^ (5 * d + 2) := by
    have hY1 : 1 ≤ N ^ N * (D ^ N * d ^ d) ^ 2 := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega)))
    have hY : N ^ N * (D ^ N * d ^ d) ^ 2 ≤ B ^ d * (B ^ (2 * d)) ^ 2 :=
      Nat.mul_le_mul hNN (Nat.pow_le_pow_left hX 2)
    have h4 : 4 ≤ B ^ 2 := by nlinarith
    calc 2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1 ≤ 4 * (N ^ N * (D ^ N * d ^ d) ^ 2) := by omega
      _ ≤ B ^ 2 * (B ^ d * (B ^ (2 * d)) ^ 2) := Nat.mul_le_mul h4 hY
      _ = B ^ (5 * d + 2) := by ring
  have hin2 : (2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1 ≤ B ^ ((5 * d + 2) * d + 1) := by
    have a : (2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d ≤ B ^ ((5 * d + 2) * d) := by
      rw [pow_mul B]
      exact Nat.pow_le_pow_left hin d
    have b : 1 ≤ B ^ ((5 * d + 2) * d) := Nat.one_le_pow _ _ (by omega)
    calc (2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1 ≤ 2 * B ^ ((5 * d + 2) * d) := by omega
      _ ≤ B * B ^ ((5 * d + 2) * d) := Nat.mul_le_mul_right _ hB2
      _ = B ^ ((5 * d + 2) * d + 1) := by ring
  have f2 : ((2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1) ^ (d * N * (p + 1)) ≤
      B ^ (((5 * d + 2) * d + 1) * (d * N * (p + 1))) := by
    rw [pow_mul B]
    exact Nat.pow_le_pow_left hin2 _
  have hexp : 2 * d * (1 + d * N) + ((5 * d + 2) * d + 1) * (d * N * (p + 1)) ≤
      12 * (p + 1) * d ^ 3 * N := by
    have e1 : d ≤ d ^ 3 * N * (p + 1) := by
      have : 1 ≤ d ^ 2 * N * (p + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    have e2 : d ^ 2 * N ≤ d ^ 3 * N * (p + 1) := by
      have : 1 ≤ d * (p + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    have e3 : d * N * (p + 1) ≤ d ^ 3 * N * (p + 1) := by
      have : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ (by omega)
      nlinarith
    have e4 : d ^ 2 * N * (p + 1) ≤ d ^ 3 * N * (p + 1) := by
      have : d ^ 2 * N * (p + 1) * 1 ≤ d ^ 2 * N * (p + 1) * d := Nat.mul_le_mul_left _ hd1
      nlinarith
    nlinarith
  calc (D ^ N * d ^ d) ^ (1 + d * N) *
        ((2 * (N ^ N * (D ^ N * d ^ d) ^ 2) + 1) ^ d + 1) ^ (d * N * (p + 1))
      ≤ B ^ (2 * d * (1 + d * N)) * B ^ (((5 * d + 2) * d + 1) * (d * N * (p + 1))) :=
        Nat.mul_le_mul f1 f2
    _ = B ^ (2 * d * (1 + d * N) + ((5 * d + 2) * d + 1) * (d * N * (p + 1))) := by ring
    _ ≤ B ^ (12 * (p + 1) * d ^ 3 * N) := Nat.pow_le_pow_right (by omega) hexp

theorem UpperTheory.V.KT.orbnum :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (p : ℕ), 1 ≤ N →
    orbBound L N p ≤ (2 * absD L * dd L N) ^ (12 * (p + 1) * dd L N ^ 3 * N) := by
  intro L _ _ N p hN
  have hD : 1 ≤ absD L := Nat.one_le_iff_ne_zero.mpr (by
    simp only [absD, ne_eq, Int.natAbs_eq_zero]
    exact NumberField.discr_ne_zero L)
  have hd : N ≤ dd L N := by
    simp only [dd]
    have : 1 ≤ Module.finrank ℚ L := Module.finrank_pos
    nlinarith
  have := orbit_number_power_bound (absD L) (dd L N) N p hD hN hd
  simpa only [orbBound, I0, RR] using this
end

