module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0087
public import Development.AbelianVarietyTheory.Definitions.Foundations.AuxiliaryFrameNormalizedSpaces
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Formalism.LocalToGlobal.Divisibility.Bundle0001
public import Formalism.LocalToGlobal.Divisibility.RowSideTie
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem.BaseExt

section ext

variable {K K' : Type} [Field K] [Field K'] (f : K →+* K')

theorem span_image_span (s : Set K) :
    Submodule.span (𝓞 K') (f '' (Submodule.span (𝓞 K) s : Set K)) = Submodule.span (𝓞 K') (f '' s) := by
  refine le_antisymm (Submodule.span_le.2 ?_)
    (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    have : f (a • x) = RingOfIntegers.mapRingHom f a • f x := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul]; rfl
    rw [this]
    exact Submodule.smul_mem _ _ hx

def extend : Submodule (𝓞 K) K →* Submodule (𝓞 K') K' where
  toFun M := Submodule.span (𝓞 K') (f '' (M : Set K))
  map_one' := by
    rw [Submodule.one_eq_span, span_image_span, Submodule.one_eq_span]; simp
  map_mul' M N := by
    conv_lhs => rw [← M.span_eq, ← N.span_eq, Submodule.span_mul_span, span_image_span]
    rw [Submodule.span_mul_span, Set.image_mul]

theorem extend_span (s : Set K) :
    extend f (Submodule.span (𝓞 K) s) = Submodule.span (𝓞 K') (f '' s) := span_image_span f s

end ext

section host

variable {R : Ranks} (H : Host R)

theorem conjugate_emb (g : R.GG) :
    ComplexEmbedding.conjugate (H.emb g) = H.emb (g * R.cc) := by
  rw [Formalism.L2.Geo.emb_mul_cc_comp]
  refine RingHom.ext fun x => ?_
  have hcm := H.isCMField_hostE
  have h : IsCMField.complexConj H.E x = H.conj x := by
    apply H.φ₀.injective
    rw [IsCMField.complexEmbedding_complexConj, H.conjE_apply]
  show starRingEnd ℂ (H.emb g x) = H.emb g (H.conj x)
  rw [← h, IsCMField.complexEmbedding_complexConj]

theorem conjugate_emb_apply (g : R.GG) (x : H.E) :
    ComplexEmbedding.conjugate (H.emb g) x = H.emb g (H.conj x) := by
  rw [conjugate_emb, Formalism.L2.Geo.emb_mul_cc_comp]; rfl

theorem ex_emb_iff (g : R.GG) :
    (∃ t : Tau R, H.emb t = H.emb g) ↔ g ∈ R.Psi :=
  ⟨fun ⟨t, ht⟩ => (factEmb R H).1.1 ht ▸ t.2, fun h => ⟨⟨g, h⟩, rfl⟩⟩

theorem emb_cm (σ : H.E →+* ℂ) :
    (∃ t : Tau R, H.emb t = σ) ↔ ¬ ∃ t : Tau R, H.emb t = ComplexEmbedding.conjugate σ := by
  obtain ⟨g, rfl⟩ := (factEmb R H).1.2 σ
  rw [conjugate_emb, ex_emb_iff, ex_emb_iff]
  exact Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g

theorem sum_emb_bijective : Function.Bijective
    (Sum.elim (fun t : Tau R => H.emb t) fun t : Tau R => ComplexEmbedding.conjugate (H.emb t)) := by
  have hc : ∀ σ : H.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => star_star σ
  have hi : ∀ {a b : Tau R}, H.emb a = H.emb b → a = b := fun h => Subtype.ext ((factEmb R H).1.1 h)
  constructor
  · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · rw [hi h]
    · exact absurd ⟨a, h⟩ ((emb_cm H (H.emb b)).1 ⟨b, rfl⟩)
    · exact absurd ⟨b, h.symm⟩ ((emb_cm H (H.emb a)).1 ⟨a, rfl⟩)
    · have := congrArg ComplexEmbedding.conjugate h
      rw [hc, hc] at this
      rw [hi this]
  · intro σ
    by_cases h : ∃ t : Tau R, H.emb t = ComplexEmbedding.conjugate σ
    · obtain ⟨t, ht⟩ := h
      exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
    · obtain ⟨t, ht⟩ := (emb_cm H σ).2 h
      exact ⟨Sum.inl t, ht⟩


open Classical in
def typeExp (p q : ℕ) (σ : H.E →+* ℂ) : ℕ := if ∃ t : Tau R, H.emb t = σ then p else q

theorem typeExp_emb (p q : ℕ) (t : Tau R) : typeExp H p q (H.emb t) = p := if_pos ⟨t, rfl⟩

theorem typeExp_conj (p q : ℕ) (t : Tau R) :
    typeExp H p q (ComplexEmbedding.conjugate (H.emb t)) = q := if_neg ((emb_cm H _).1 ⟨t, rfl⟩)

theorem typeExp_add (p q : ℕ) (σ : H.E →+* ℂ) :
    typeExp H p q σ + typeExp H p q (ComplexEmbedding.conjugate σ) = p + q := by
  unfold typeExp
  by_cases h : ∃ t : Tau R, H.emb t = σ
  · rw [if_pos h, if_neg ((emb_cm H σ).1 h)]
  · rw [if_neg h, if_pos (not_not.1 (fun h' => h ((emb_cm H σ).2 h'))), add_comm]

theorem prod_typeExp {M : Type} [CommMonoid M] (p q : ℕ) (F : (H.E →+* ℂ) → M) :
    ∏ σ, F σ ^ typeExp H p q σ =
      ∏ t : Tau R, (F (H.emb t) ^ p * F (ComplexEmbedding.conjugate (H.emb t)) ^ q) := by
  rw [← (sum_emb_bijective H).prod_comp, Fintype.prod_sum_type, Finset.prod_mul_distrib]
  simp only [Sum.elim_inl, Sum.elim_inr, typeExp_emb, typeExp_conj]

end host

theorem isAlgebraic_exp (N : ℕ) : IsAlgebraic ℚ (Complex.exp (2 * Real.pi * Complex.I / N)) := by
  rcases Nat.eq_zero_or_pos N with rfl | h
  · simpa using isAlgebraic_one
  · exact ((Complex.isPrimitiveRoot_exp N h.ne').isIntegral h).tower_top.isAlgebraic

theorem exists_gens (E : Type) [Field E] [NumberField E] : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ K : IntermediateField ℚ ℂ, (∀ z ∈ S, z ∈ K) → ∀ (τ : E →+* ℂ) x, τ x ∈ K := by
  classical
  let b := Module.finBasis ℚ E
  refine ⟨Finset.univ.image fun p : (E →+* ℂ) × Fin (Module.finrank ℚ E) => p.1 (b p.2), ?_, ?_⟩
  · intro z hz
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hz
    exact (Algebra.IsAlgebraic.isAlgebraic (b p.2)).algHom p.1.toRatAlgHom
  · intro K hK τ x
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact K.smul_mem (hK _ (Finset.mem_image.2 ⟨(τ, i), Finset.mem_univ _, rfl⟩))

@[instance_reducible] def starOf (K : IntermediateField ℚ ℂ) (h : ∀ z ∈ K, starRingEnd ℂ z ∈ K) : StarRing K where
  star x := ⟨starRingEnd ℂ x, h _ x.2⟩
  star_involutive x := Subtype.ext (Complex.conj_conj _)
  star_mul x y := Subtype.ext (by
    show starRingEnd ℂ ((x : ℂ) * y) = starRingEnd ℂ y * starRingEnd ℂ x
    rw [map_mul, mul_comm])
  star_add x y := Subtype.ext (map_add (starRingEnd ℂ) (x : ℂ) (y : ℂ))

def toTop (K : IntermediateField ℚ ℂ) : K →+* (⊤ : IntermediateField ℚ K) :=
  (IntermediateField.topEquiv (F := ℚ) (E := K)).symm

theorem image_top {E : Type} [Field E] (K : IntermediateField ℚ ℂ) (𝔞 : Ideal (𝓞 E)) (τ : E →+* ℂ) (e : E → K)
    (he : ∀ a, (e a : ℂ) = τ a) :
    extend (toTop K) (Submodule.span (𝓞 K) {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : E)}) =
      Submodule.span (𝓞 (⊤ : IntermediateField ℚ K))
        {x : (⊤ : IntermediateField ℚ K) | ∃ a ∈ 𝔞, (x : K) = e (a : E)} := by
  rw [extend_span]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, hy⟩, rfl⟩
    exact ⟨a, ha, Subtype.ext (hy.trans (he _).symm)⟩
  · rintro ⟨a, ha, hx⟩
    exact ⟨x.1, ⟨a, ha, (congrArg Subtype.val hx).trans (he _)⟩, rfl⟩

theorem exists_base : ∀ (B : Pre) (S₀ S₁ S₂ : Finset ℂ), (∀ z ∈ S₀, IsAlgebraic ℚ z) → (∀ z ∈ S₁, IsAlgebraic ℚ z) → (∀ z ∈ S₂, IsAlgebraic ℚ z) → ∃ B' : Base, B'.toPre = B ∧ (∀ z ∈ S₀, ∃ x ∈ B'.Ks, B'.embLL x = z) ∧ (∀ z ∈ S₁, ∃ x ∈ B'.LL0, B'.embLL x = z) ∧ ∀ z ∈ S₂, ∃ x : B'.LL, B'.embLL x = z := by
  classical
  intro B S₀ S₁ S₂ h₀ h₁ h₂
  have hcm : IsCMField B.host.E := B.host.isCMField_hostE
  have hgal : IsGalois ℚ B.host.E := B.host.hostE_isGalois
  obtain ⟨SE, hSE, hE⟩ := exists_gens B.host.E
  choose MainNotions hSK hK using fun j : ℕ => GlobalTheory.Mem.exists_finset_typeNorm_principal B.host.E
    (typeExp B.host (B.R.sigW j).1 (B.R.sigW j).2) _ (typeExp_add B.host _ _)
  obtain ⟨SC, hSC, hC⟩ := GlobalTheory.Mem.exists_finset_capitulation B.host.E B.host.φ₀
  let l : List ℕ := [B.restRowsFiniteGroupCard, B.host.g 0 * (B.host.g 0 - 1), B.host.g 1 * (B.host.g 1 - 1), 3 ^ 4, 5 ^ 4]
  let l' : List ℕ := [B.host.pde, B.host.pde', classNumber B.host.E]
  let A : Finset ℕ := l.toFinset ∪ l'.toFinset ∪ {B.ramOrder} ∪ Finset.univ.image B.T
  let SR : Finset ℂ := A.image fun N : ℕ => Complex.exp (2 * Real.pi * Complex.I / N)
  obtain ⟨K, hfd, hKgal, hS, -, hconj⟩ := GlobalTheory.exists_galois_subfield_conj_stable
    (S₀ ∪ S₁ ∪ S₂ ∪ SE ∪ SC ∪ SR ∪ (Finset.range (B.R.m + 1)).biUnion MainNotions) (by
      intro z hz
      simp only [Finset.mem_union, Finset.mem_biUnion] at hz
      rcases hz with (((((hz | hz) | hz) | hz) | hz) | hz) | ⟨j, -, hz⟩
      exacts [h₀ z hz, h₁ z hz, h₂ z hz, hSE z hz, hSC z hz, by
        obtain ⟨N, -, rfl⟩ := Finset.mem_image.1 hz
        exact isAlgebraic_exp N, hSK j z hz])
  simp only [Finset.mem_union, Finset.mem_biUnion] at hS
  have hEK := hE K fun z hz => hS z (by tauto)
  have hR : ∀ N ∈ A, Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ K := fun N hN => by
    have hz : Complex.exp (2 * Real.pi * Complex.I / N) ∈ SR := Finset.mem_image.2 ⟨N, hN, rfl⟩
    exact hS _ (by tauto)
  have : NumberField K := {}
  let f := toTop K
  refine ⟨{ toPre := B
            LL := K
            starLL := starOf K hconj
            embLL := K.val
            starLL_cx := fun _ => rfl
            embE := B.host.φ₀.codRestrict K (hEK _)
            embE_φ₀ := rfl
            LL0 := ⊤
            coeffGaloisSubfield_isGalois := IsGalois.of_algEquiv IntermediateField.topEquiv.symm
            Ks := ⊤
            Ks_le := le_rfl
            E_le_Ks := fun _ => trivial
            roots_Ks := ?_
            roots_Ks' := ?_
            capit := ?_
            kPsi := ?_
            rootOfUnity_eightQ_mem_coeffGaloisSubfield := ⟨⟨_, hR B.ramOrder (Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_singleton_self _)))⟩, trivial, rfl⟩
            roots_LL := fun u => ⟨⟨_, hR (B.T u) (Finset.mem_union_right _
              (Finset.mem_image_of_mem _ (Finset.mem_univ u)))⟩, rfl⟩ }, rfl, ?_, ?_, ?_⟩
  · intro N hN
    exact ⟨⟨_, hR N (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (List.mem_toFinset.2 hN))))⟩, trivial, rfl⟩
  · intro N hN
    exact ⟨⟨_, hR N (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (List.mem_toFinset.2 hN))))⟩, trivial, rfl⟩
  · intro 𝔞
    obtain ⟨β, hsp⟩ := hC K (fun z hz => hS z (by tauto)) (hEK _) 𝔞
    refine ⟨f β, ?_⟩
    have h := congrArg (extend f) hsp
    rw [extend_span, Set.image_singleton] at h
    exact h.trans (image_top K 𝔞 B.host.φ₀ (B.host.φ₀.codRestrict K (hEK _)) fun _ => rfl)
  · intro j _ hj 𝔞 h𝔞
    obtain ⟨β, hβ, hsp, hn⟩ := hK j K
      (fun z hz => hS z (Or.inr ⟨j, Finset.mem_range.2 (by omega), hz⟩)) hEK 𝔞 h𝔞
    refine ⟨f β, (map_ne_zero f).2 hβ, ?_, fun σ => hn (σ.comp f)⟩
    have h := congrArg (extend f) hsp
    rw [prod_typeExp, extend_span, Set.image_singleton, map_prod] at h
    rw [h]
    refine Finset.prod_congr rfl fun g _ => ?_
    have e1 := image_top K 𝔞 (B.host.emb g)
      (fun a => B.host.φ₀.codRestrict K (hEK _) (B.host.sigmaOf g a)) fun _ => rfl
    have e2 := image_top K 𝔞 (ComplexEmbedding.conjugate (B.host.emb g))
      (fun a => B.host.φ₀.codRestrict K (hEK _) (B.host.sigmaOf g (B.host.conj a)))
      fun a => (conjugate_emb_apply B.host g a).symm
    rw [map_mul, map_pow, map_pow]
    exact congrArg₂ (· * ·) (congrArg (· ^ (B.R.sigW j).1) e1) (congrArg (· ^ (B.R.sigW j).2) e2)
  · exact fun z hz => ⟨⟨z, hS z (by tauto)⟩, trivial, rfl⟩
  · exact fun z hz => ⟨⟨z, hS z (by tauto)⟩, trivial, rfl⟩
  · exact fun z hz => ⟨⟨z, hS z (by tauto)⟩, rfl⟩

end GlobalTheory.Mem.BaseExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfTameLoc
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.ModelChar

def argU : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ))
    (div_ne_zero z.ne_zero (by exact_mod_cast norm_ne_zero_iff.2 z.ne_zero))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [mul_div_mul_comm]

theorem argU_val (z : ℂˣ) : ((argU z : ℂˣ) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

theorem norm_argU (z : ℂˣ) : ‖((argU z : ℂˣ) : ℂ)‖ = 1 := by
  rw [argU_val, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)]

theorem continuous_argU : Continuous argU := by
  rw [Units.isEmbedding_val₀.continuous_iff]
  exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
    fun z => by exact_mod_cast norm_ne_zero_iff.2 z.ne_zero

variable {L : Type} [Field L] [NumberField L]

def finEv (v : HeightOneSpectrum (𝓞 L)) : AdeleRing (𝓞 L) L →* v.adicCompletion L where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def infEv (w : InfinitePlace L) : AdeleRing (𝓞 L) L →* w.Completion where
  toFun a := a.1 w
  map_one' := rfl
  map_mul' _ _ := rfl

theorem continuous_finEv (v : HeightOneSpectrum (𝓞 L)) : Continuous (finEv v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

theorem continuous_infEv (w : InfinitePlace L) : Continuous (infEv w) :=
  (continuous_apply w).comp continuous_fst

theorem finEv_local_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    Units.map (finEv v) (Neutral.B1.localIdele L v x) = x := by
  classical
  apply Units.ext
  exact Function.update_self v (x : v.adicCompletion L) (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L))

theorem finEv_local_ne {v w : HeightOneSpectrum (𝓞 L)} (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    Units.map (finEv w) (Neutral.B1.localIdele L v x) = 1 := by
  classical
  apply Units.ext
  exact Function.update_of_ne h (x : v.adicCompletion L) (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L))

theorem infEv_local (w : InfinitePlace L) (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    Units.map (infEv w) (Neutral.B1.localIdele L v x) = 1 := Units.ext rfl

theorem finEv_inf (v : HeightOneSpectrum (𝓞 L)) (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    Units.map (finEv v) (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w x) = 1 := Units.ext rfl

theorem infEv_inf_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    Units.map (infEv w) (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w x) = x := by
  classical
  apply Units.ext
  exact Pi.mulSingle_eq_same (M := fun w : InfinitePlace L => w.Completion) w (x : w.Completion)

theorem infEv_inf_ne {w u : InfinitePlace L} (h : u ≠ w) (x : (w.Completion)ˣ) :
    Units.map (infEv u) (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L w x) = 1 := by
  classical
  apply Units.ext
  exact Pi.mulSingle_eq_of_ne (M := fun w : InfinitePlace L => w.Completion) h (x : w.Completion)

theorem infEv_infDiag (w : InfinitePlace L) (k : Lˣ) : Units.map (infEv w) (infDiag k) = atInf w k := by
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, map_prod, Finset.prod_eq_single w]
  · exact infEv_inf_self w _
  · intro u _ hu
    exact infEv_inf_ne hu.symm _
  · simp

theorem finEv_infDiag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : Units.map (finEv v) (infDiag k) = 1 := by
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => finEv_inf v w _

theorem infEv_diag (w : InfinitePlace L) (k : Lˣ) : Units.map (infEv w) (Neutral.B1.diagUnits L k) = atInf w k := Units.ext rfl

theorem finEv_diag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : Units.map (finEv v) (Neutral.B1.diagUnits L k) = atFin v k :=
  Units.ext rfl

theorem continuous_of_tameLoc {v : HeightOneSpectrum (𝓞 L)} {θ : (v.adicCompletion L)ˣ →* ℂˣ} (h : TameLoc v θ) :
    Continuous θ := by
  refine continuous_of_continuousAt_one θ ?_
  have hc : Continuous fun x : (v.adicCompletion L)ˣ => (x : v.adicCompletion L) - 1 :=
    Units.continuous_val.sub continuous_const
  have ho : IsOpen {y : v.adicCompletion L | Valued.v y < 1} := by
    have := Valued.isOpen_ball (v.adicCompletion L) 1
    simpa only [Valuation.restrict_lt_one_iff] using this
  have hn : {x : (v.adicCompletion L)ˣ | Valued.v ((x : v.adicCompletion L) - 1) < 1} ∈ nhds (1 : (v.adicCompletion L)ˣ) :=
    (ho.preimage hc).mem_nhds (by simp)
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  filter_upwards [hn] with x hx
  refine (h.2 x ?_ ?_).symm
  · have := Valuation.map_one_add_of_lt (Valued.v : Valuation (v.adicCompletion L) _) hx
    rwa [add_sub_cancel] at this
  · have := (WithZero.lt_mul_exp_iff_le (x := Valued.v ((x : v.adicCompletion L) - 1)) (y := WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero).1
    apply this
    rw [← WithZero.exp_add]
    simpa using hx


open Classical in
theorem exists_modelChar : ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ), (Function.Bijective fun i => InfinitePlace.mk (φ i)) → ∀ (n : I → ℤ) (S : Finset (HeightOneSpectrum (𝓞 L))) (θ : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ →* ℂˣ), (∀ v ∈ S, TameLoc v (θ v)) → ∃ ψ : Neutral.B1.Ideles L →* ℂˣ, Continuous ψ ∧ (∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1) ∧ (∀ i (k : Lˣ), ((ψ (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele L (InfinitePlace.mk (φ i)) (atInf _ k)) : ℂˣ) : ℂ) = (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) ∧ (∀ v ∈ S, ∀ x, ψ (Neutral.B1.localIdele L v x) = θ v x) ∧ (∀ v ∉ S, ∀ x, ψ (Neutral.B1.localIdele L v x) = 1) ∧ ∀ k : Lˣ, ψ (Neutral.B1.diagUnits L k) = ψ (infDiag k) * ∏ v ∈ S, θ v (atFin v k) := by
  intro L _ _ I _ φ hφ n S θ hθ
  choose e hec he using fun i => GlobalTheory.InfTypeLocal.exists_ext (φ i)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Neutral.B1.Ideles L →* ℂˣ, ∀ a, ψ a =
      (∏ i, argU (Units.map (e i).toMonoidHom (Units.map (infEv (InfinitePlace.mk (φ i))) a)) ^ n i) *
        ∏ v ∈ S, θ v (Units.map (finEv v) a) :=
    ⟨{ toFun := fun a =>
        (∏ i, argU (Units.map (e i).toMonoidHom (Units.map (infEv (InfinitePlace.mk (φ i))) a)) ^ n i) *
          ∏ v ∈ S, θ v (Units.map (finEv v) a)
       map_one' := by simp only [map_one, one_zpow, Finset.prod_const_one, mul_one]
       map_mul' := fun a b => by
        simp only [map_mul, mul_zpow, Finset.prod_mul_distrib]
        rw [mul_mul_mul_comm] }, fun _ => rfl⟩
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (ψ : Neutral.B1.Ideles L → ℂˣ) = _ from funext hψ]
    refine Continuous.mul (continuous_finsetProd _ fun i _ => ?_) (continuous_finsetProd _ fun v hv => ?_)
    · exact (continuous_argU.comp ((Continuous.units_map _ (hec i)).comp
        (Continuous.units_map _ (continuous_infEv _)))).zpow _
    · exact (continuous_of_tameLoc (hθ v hv)).comp (Continuous.units_map _ (continuous_finEv v))
  · intro x
    rw [hψ, Units.val_mul, Units.coe_prod, Units.coe_prod, norm_mul, norm_prod, norm_prod,
      Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
    · exact fun v hv => (hθ v hv).1 _
    · intro i _
      rw [Units.val_zpow_eq_zpow_val, norm_zpow, norm_argU, one_zpow]
  · intro i k
    rw [hψ, Finset.prod_eq_one (s := S), mul_one, Finset.prod_eq_single i, infEv_inf_self,
      Units.val_zpow_eq_zpow_val, argU_val, ← he i k]
    · rfl
    · intro j _ hj
      rw [infEv_inf_ne (fun hh => hj (hφ.1 hh)), map_one, map_one, one_zpow]
    · simp
    · intro v _
      rw [finEv_inf, map_one]
  · intro v hv x
    rw [hψ, Finset.prod_eq_one, one_mul, Finset.prod_eq_single_of_mem v hv, finEv_local_self]
    · intro w _ hw
      rw [finEv_local_ne hw, map_one]
    · intro i _
      rw [infEv_local, map_one, map_one, one_zpow]
  · intro v hv x
    rw [hψ, Finset.prod_eq_one, one_mul, Finset.prod_eq_one]
    · intro w hw
      have hne : w ≠ v := fun hh => hv (hh ▸ hw)
      rw [finEv_local_ne hne, map_one]
    · intro i _
      rw [infEv_local, map_one, map_one, one_zpow]
  · intro k
    rw [hψ, hψ]
    simp only [infEv_diag, finEv_diag, infEv_infDiag, finEv_infDiag, map_one, Finset.prod_const_one, mul_one]

end GlobalTheory.ModelChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnitsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idele_character_trivial_on_local_units : ∀ (L : Type) [Field L] [NumberField L] (ψ : Neutral.B1.Ideles L →* ℂˣ), Continuous ψ → ∀ a : Neutral.B1.Ideles L, a ∈ unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ v (x : (v.adicCompletion L)ˣ), (x : v.adicCompletion L) = (a : AdeleRing (𝓞 L) L).2 v → ψ (Neutral.B1.localIdele L v x) = 1) → ψ a = 1 := by
  first | exact @GlobalTheory.Mem.LocTriv.eq_one_of_local | exact GlobalTheory.Mem.LocTriv.eq_one_of_local | (intros; apply GlobalTheory.Mem.LocTriv.eq_one_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LPrjSurjective
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory.Mem.LiftProjOnto

theorem lPrj_surjective : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (k : Fin D.R.m) (t : T) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : (Fin (lDim D A P ψ k t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] W) (op : W →ₗ[ℂ] W), A.fam.Ok 1 → FormsTie D.what₂.embLL j (lH D A P ψ k t) (lE D A P ψ k t) op → Function.Surjective (lPrj D A P ψ Zs k t).mulVec := by
  intro D G _ _ Pl0 T A P ψ Zs k t W _ _ j op hOk _
  have hB : BlockHyp (A.fam.L k t) (A.fam.lvlA P ψ) A.v0 1 := ⟨hOk.conj, hOk.irr, hOk.lifts k t⟩
  exact BlockDat.lf_lPr_surj (Z := Zs.Zl k t) hB

end GlobalTheory.Mem.LiftProjOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefMapEmbeddingOfPositiveAtPlaceStatement
section
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K), Formalism.L2.Rows.PosAt H v → (H.map v.embedding).PosDef := by
  first | exact @GlobalTheory.AmbTiePosDef.posDef_map_of_posAt | exact GlobalTheory.AmbTiePosDef.posDef_map_of_posAt | (intros; apply GlobalTheory.AmbTiePosDef.posDef_map_of_posAt <;> assumption)
end

