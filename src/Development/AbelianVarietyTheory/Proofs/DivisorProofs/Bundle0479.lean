module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral
public import Formalism.PairingDivisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0459
public import ReciprocityTheory.Automorphisms.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsElementPosImUnderCmType
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

open NumberField IsDedekindDomain GlobalTheory.CMVal

namespace GlobalTheory.CMTypeImPos

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem denseRange_embeddings : DenseRange fun (x : E) (w : InfinitePlace E) => w.embedding x := by
  first
  | exact @_root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi
  | exact _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi
  | (apply _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenseEmbeddingProduct.denseRange_embedding_pi ..)

theorem exists_im_pos (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) : ∃ θ : E, ∀ i, 0 < (φ i θ).im := by
  classical

  let f : I → (InfinitePlace E → ℂ) → ℝ := fun i z =>
    if (InfinitePlace.mk (φ i)).embedding = φ i then (z (InfinitePlace.mk (φ i))).im
    else -(z (InfinitePlace.mk (φ i))).im
  have hfc : ∀ i, Continuous (f i) := by
    intro i
    by_cases h : (InfinitePlace.mk (φ i)).embedding = φ i
    · simp only [f, h, if_true]
      exact Complex.continuous_im.comp (continuous_apply _)
    · simp only [f, h, if_false]
      exact (Complex.continuous_im.comp (continuous_apply _)).neg
  let U : Set (InfinitePlace E → ℂ) := {z | ∀ i, 0 < f i z}
  have hU : IsOpen U := by
    have : U = ⋂ i, {z | 0 < f i z} := by ext z; simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (hfc i)

  let y : InfinitePlace E → ℂ := fun w => if ∃ j, w.embedding = φ j then Complex.I else -Complex.I
  have hy : y ∈ U := by
    intro i
    have hnr : ¬ ComplexEmbedding.IsReal (φ i) :=
      InfinitePlace.isComplex_mk_iff.1 (IsTotallyComplex.isComplex _)
    rcases InfinitePlace.embedding_mk_eq (φ i) with h | h
    · have hex : ∃ j, (InfinitePlace.mk (φ i)).embedding = φ j := ⟨i, h⟩
      simp [f, y, h, hex]
    · have hne : (InfinitePlace.mk (φ i)).embedding ≠ φ i := by
        rw [h]; exact fun h' => hnr (ComplexEmbedding.isReal_iff.2 h')
      have hex : ¬ ∃ j, (InfinitePlace.mk (φ i)).embedding = φ j := by
        rintro ⟨j, hj⟩
        obtain ⟨k, _, hk⟩ := hφ (InfinitePlace.mk (φ i)).embedding
        have hi : i = k := hk i (Or.inr h)
        have hj' : j = k := hk j (Or.inl hj)
        subst hi; subst hj'
        exact hne hj
      simp [f, y, hne, hex]
  obtain ⟨θ, hθ⟩ := denseRange_embeddings.exists_mem_open hU ⟨y, hy⟩
  refine ⟨θ, fun i => ?_⟩
  have := hθ i
  rcases InfinitePlace.embedding_mk_eq (φ i) with h | h
  · simpa [f, h] using this
  · by_cases h' : (InfinitePlace.mk (φ i)).embedding = φ i
    · simpa [f, h'] using this
    · simp only [f, h', if_false] at this
      rw [h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_im] at this
      linarith

end GlobalTheory.CMTypeImPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddingsMaxRealSubfield
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.CMTypeRealEmb

theorem comp_isReal {E : Type} [Field E] [NumberField E] [IsCMField E] (φ : E →+* ℂ) :
    ComplexEmbedding.IsReal (φ.comp (algebraMap (maximalRealSubfield E) E)) := by
  rw [ComplexEmbedding.isReal_iff]
  ext a
  simp only [ComplexEmbedding.conjugate_coe_eq, RingHom.coe_comp, Function.comp_apply]
  rw [← IsCMField.complexEmbedding_complexConj]
  congr 1
  exact IsCMField.complexConj_apply_eq_self E a

theorem exists_equiv (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ) (hφ : IsCMType φ) :
    ∃ e : I ≃ Emb (maximalRealSubfield E), ∀ (i : I) (a : maximalRealSubfield E),
      φ i (a : E) = ((e i a : ℝ) : ℂ) := by
  set F := maximalRealSubfield E
  let ψ : I → F →+* ℂ := fun i => (φ i).comp (algebraMap F E)
  have hre : ∀ i, ComplexEmbedding.IsReal (ψ i) := fun i => comp_isReal (φ i)
  let e : I → Emb F := fun i => (hre i).embedding
  have he : ∀ i a, ((e i a : ℝ) : ℂ) = φ i (a : E) := fun i a =>
    (hre i).coe_embedding_apply a
  have hplace : ∀ i, (InfinitePlace.mk (φ i)).comap (algebraMap F E) = InfinitePlace.mk (ψ i) :=
    fun i => InfinitePlace.comap_mk _ _
  refine ⟨Equiv.ofBijective e ⟨?_, ?_⟩, fun i a => (he i a).symm⟩
  · intro i j hij
    have hψ : ψ i = ψ j := by
      ext a
      show φ i (a : E) = φ j (a : E)
      rw [← he, ← he, hij]
    have h1 : InfinitePlace.mk (φ i) = InfinitePlace.mk (φ j) := by
      apply (IsCMField.equivInfinitePlace E).injective
      simp only [IsCMField.equivInfinitePlace_apply]
      rw [hplace, hplace, hψ]
    rcases InfinitePlace.mk_eq_iff.mp h1 with h | h
    · obtain ⟨k, _, hk⟩ := hφ (φ j)
      exact (hk i (Or.inl h.symm)).trans (hk j (Or.inl rfl)).symm
    · obtain ⟨k, _, hk⟩ := hφ (φ j)
      exact (hk i (Or.inr h.symm)).trans (hk j (Or.inl rfl)).symm
  · intro f
    let fc : F →+* ℂ := Complex.ofRealHom.comp f
    have hfc : ComplexEmbedding.IsReal fc := by
      rw [ComplexEmbedding.isReal_iff]
      ext a
      simp [fc]
    let w : InfinitePlace E := (IsCMField.equivInfinitePlace E).symm (InfinitePlace.mk fc)
    obtain ⟨i, hi, _⟩ := hφ w.embedding
    have hmk : InfinitePlace.mk (φ i) = w := by
      rcases hi with h | h
      · rw [← h, InfinitePlace.mk_embedding]
      · rw [← InfinitePlace.mk_conjugate_eq, ← h, InfinitePlace.mk_embedding]
    have h2 : InfinitePlace.mk (ψ i) = InfinitePlace.mk fc := by
      rw [← hplace, hmk]
      have := (IsCMField.equivInfinitePlace E).apply_symm_apply (InfinitePlace.mk fc)
      rw [IsCMField.equivInfinitePlace_apply] at this
      exact this
    have h3 : ψ i = fc := by
      rcases InfinitePlace.mk_eq_iff.mp h2 with h | h
      · exact h
      · rw [← h]; exact ((ComplexEmbedding.isReal_iff).mp (hre i)).symm
    refine ⟨i, ?_⟩
    ext a
    apply Complex.ofReal_injective
    rw [he]
    show ψ i a = fc a
    rw [h3]

end GlobalTheory.CMTypeRealEmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusHodgeTateLatticeAinf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.Frob

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frob_phiInv (a : Ainf p O) : WittVector.frobenius (phiInv p O a) = a := by
  ext n
  rw [WittVector.coeff_frobenius_charP, phiInv, WittVector.map_coeff]
  exact frobeniusEquiv_symm_pow_p _ p _

theorem phiInv_ofPadic' (c : ℤ_[p]) : phiInv p O (ofPadic p O c) = ofPadic p O c := by
  ext n
  simp only [phiInv, ofPadic, RingHom.coe_comp, Function.comp_apply, WittVector.map_coeff]
  exact RingHom.congr_fun (RingHom.ext_zmod
    (((_root_.frobeniusEquiv (PreTilt O p) p).symm : PreTilt O p →+* PreTilt O p).comp
      (ZMod.castHom (dvd_refl p) (PreTilt O p))) (ZMod.castHom (dvd_refl p) (PreTilt O p))) _

theorem frob_ofPadic (c : ℤ_[p]) :
    WittVector.frobenius (ofPadic p O c) = ofPadic p O c := by
  conv_lhs => rw [← phiInv_ofPadic' c]
  exact frob_phiInv _

def frobT (G : PDivGroup p O) (y : TDual G) : TDual G where
  toFun t := WittVector.frobenius (y t)
  map_add' s t := by rw [map_add (f := _), map_add (f := _)]
  map_smul' c t := by
    rw [LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, frob_ofPadic, smul_eq_mul]

def xiPhiInvT (ε : PreTilt O p) (G : PDivGroup p O) (m : TDual G) : TDual G where
  toFun t := xi ε * phiInv p O (m t)
  map_add' s t := by rw [map_add (f := _), map_add (f := _), mul_add]
  map_smul' c t := by
    rw [LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, phiInv_ofPadic', smul_eq_mul, mul_left_comm]

def frobLatt (G : PDivGroup p O) :
    latt G →ₛₗ[(WittVector.frobenius : Ainf p O →+* Ainf p O)] latt G where
  toFun y := ⟨frobT G y.1, fun n => by
    obtain ⟨x, hx⟩ := y.2 (n + 1)
    exact ⟨x, fun t => by rw [← hx]; rfl⟩⟩
  map_add' y z := by
    apply Subtype.ext; apply LinearMap.ext; intro t
    show WittVector.frobenius ((y.1 + z.1) t) = _
    rw [LinearMap.add_apply, map_add (f := _)]; rfl
  map_smul' a y := by
    apply Subtype.ext; apply LinearMap.ext; intro t
    show WittVector.frobenius ((a • y.1) t) = _
    rw [LinearMap.smul_apply, smul_eq_mul, map_mul]; rfl

end GlobalTheory.PDivLat.Frob


open GlobalTheory.PDivLat.Frob in
theorem GlobalTheory.PDivLat.exists_frobenius_latt : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ φ : ∀ G : PDivGroup p O, latt G →ₛₗ[(WittVector.frobenius : Ainf p O →+* Ainf p O)] latt G, (∀ G y t, (φ G y).1 t = WittVector.frobenius (y.1 t)) ∧ ∀ G m, ∃ n, φ G n = (WittVector.frobenius (xi ε) : Ainf p O) • m := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε
  obtain ⟨-, -, -, h0, hs, hphi⟩ := _root_.GlobalTheory.PDivLat.ghost_values p C v O hv ε hε
  refine ⟨fun G => frobLatt G, fun G y t => rfl, fun G m => ?_⟩
  refine ⟨⟨xiPhiInvT ε G m.1, fun n => ?_⟩, ?_⟩
  · cases n with
    | zero => exact ⟨0, fun t => by
        show ghost p O 0 (xi ε * phiInv p O (m.1 t)) = _
        rw [ghost_mul, h0, zero_mul, LinearMap.zero_apply]⟩
    | succ k =>
      obtain ⟨x, hx⟩ := m.2 k
      exact ⟨(p : O) • x, fun t => by
        show ghost p O (k + 1) (xi ε * phiInv p O (m.1 t)) = _
        rw [ghost_mul, hs, hphi, hx, LinearMap.smul_apply, smul_eq_mul]⟩
  · apply Subtype.ext; apply LinearMap.ext; intro t
    show WittVector.frobenius (xi ε * phiInv p O (m.1 t)) = _
    rw [map_mul, frob_phiInv]; rfl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealGeometricRankIffOfLieConditionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideal_geometric_rank_iff_of_lie_condition : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
  (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B),
    ∃ K₂ : Ideal B, ∀ (T : Type) [CommRing T] (f : B →+* T), lieIdeal b βB M ≤ RingHom.ker f →
      ((∀ (k : Type) [Field k] [IsAlgClosed k] (h : T →+* k) (i : Fin D.a),
          Module.finrank k (eigSub (matAct M (h.comp f)) ((h.comp (f.comp βB)).comp (b.t i))) = D.m) ↔
        K₂ ≤ RingHom.ker f) := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.RankIdeal.exists_ideal_rank_iff) | (exact GlobalTheory.UPel.HT.LieLin.RankIdeal.exists_ideal_rank_iff) | (intros; apply GlobalTheory.UPel.HT.LieLin.RankIdeal.exists_ideal_rank_iff  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralTraceOneUnramified
section
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

noncomputable section

namespace GlobalTheory.LieDisc

theorem exists_integral_add_cc_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    Unr E → ∃ t : E, IsIntegral ℤ t ∧ t + cc t = 1 := by
  intro E _ _ _ hE
  have : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := hE
  let σ := IsCMField.ringOfIntegersComplexConj E
  let I : Ideal (𝓞 (maximalRealSubfield E)) :=
    { carrier := {a | ∃ t : 𝓞 E, algebraMap _ (𝓞 E) a = t + σ t}
      add_mem' := by
        rintro a b ⟨s, hs⟩ ⟨t, ht⟩
        exact ⟨s + t, by rw [map_add (f := _), hs, ht, map_add (f := _)]; ring⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨t, ht⟩
        refine ⟨algebraMap _ (𝓞 E) c * t, ?_⟩
        rw [smul_eq_mul, map_mul, ht, map_mul, AlgEquiv.commutes]
        ring }
  have hI : I = ⊤ := by
    by_contra hI
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal _ hI
    obtain ⟨P, hP, hPm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) m
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1
        (FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E))]; exact bot_le)
    have htr : ∀ t : 𝓞 E, t + σ t ∈ P := by
      intro t
      have hco : ((t + σ t : 𝓞 E) : E) = (t : E) + IsCMField.complexConj E t := by
        rw [← IsCMField.coe_ringOfIntegersComplexConj]
        rfl
      have hfix := (IsCMField.complexConj_eq_self_iff E ((t : E) + IsCMField.complexConj E t)).1 (by
        rw [map_add (f := _), IsCMField.complexConj_apply_apply, add_comm])
      have hi : IsIntegral ℤ (⟨_, hfix⟩ : maximalRealSubfield E) := by
        have h0 : IsIntegral ℤ ((t + σ t : 𝓞 E) : E) := (t + σ t).isIntegral_coe
        rw [hco] at h0
        exact (isIntegral_algebraMap_iff ).1 h0
      let a : 𝓞 (maximalRealSubfield E) := ⟨_, hi⟩
      have hA : algebraMap _ (𝓞 E) a = t + σ t := by
        apply RingOfIntegers.ext
        rw [hco]
        rfl
      have h1 : a ∈ Ideal.comap (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) P := by
        change a ∈ Ideal.under (𝓞 (maximalRealSubfield E)) P
        rw [hPm]
        exact hIm ⟨t, hA⟩
      exact hA ▸ Ideal.mem_comap.1 h1
    have hσ : ∃ s, σ.toAlgHom s ≠ s := by
      by_contra hc
      push Not at hc
      apply IsCMField.complexConj_ne_one E
      ext x
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
      have hc' : ∀ s : 𝓞 E, IsCMField.complexConj E (algebraMap (𝓞 E) E s) = algebraMap (𝓞 E) E s :=
        fun s => congrArg (fun z : 𝓞 E => (z : E)) (hc s)
      simp [hc']
    obtain ⟨t, ht⟩ := GlobalTheory.UCls.Det.exists_sub_notMem σ.toAlgHom hσ P hP.ne_top
    apply ht
    have h2 := P.sub_mem (htr t) (P.mul_mem_right (σ t) (htr 1))
    convert h2 using 1
    change t - σ t = t + σ t - (1 + σ 1) * σ t
    rw [map_one]
    ring
  obtain ⟨t, ht⟩ : (1 : 𝓞 (maximalRealSubfield E)) ∈ I := hI ▸ Submodule.mem_top
  refine ⟨(t : E), t.isIntegral_coe, ?_⟩
  have h := congrArg (fun z : 𝓞 E => (z : E)) ht
  rw [map_one] at h
  change (1 : E) = (t : E) + ((σ t : 𝓞 E) : E) at h
  rw [IsCMField.coe_ringOfIntegersComplexConj] at h
  rw [cc]
  exact h.symm

end GlobalTheory.LieDisc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitRepresentativesSplitPrime
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

namespace GlobalTheory.CMVal.Euler.Resid

variable {E : Type} [Field E] [NumberField E]

theorem le_exp_iff (x : WithZero (Multiplicative ℤ)) : x ≤ WithZero.exp (-((1 : ℕ) : ℤ)) ↔ x < 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← WithZero.exp_log hx, ← WithZero.exp_zero, WithZero.exp_le_exp, WithZero.exp_lt_exp]
    omega

theorem val_iota_lt_iff {P : HeightOneSpectrum (𝓞 E)} {q : HeightOneSpectrum (OF E)} (h : Over P q) (a : OF E) :
    Valued.v (iota a P) < 1 ↔ a ∈ q.asIdeal := by
  rw [← le_exp_iff, val_iota_le_iff, pow_one, ← Ideal.mem_comap, h]

theorem val_iota_eq_one {P : HeightOneSpectrum (𝓞 E)} {q : HeightOneSpectrum (OF E)} (h : Over P q) {a : OF E}
    (ha : a ∉ q.asIdeal) : Valued.v (iota a P) = 1 :=
  le_antisymm (val_iota_le_one P a) (not_lt.1 fun h' => ha ((val_iota_lt_iff h a).1 h'))

theorem exists_iota_approx {P : HeightOneSpectrum (𝓞 E)}
    (h : ∀ b : 𝓞 E, ∃ a : OF E, b - algebraMap (OF E) (𝓞 E) a ∈ P.asIdeal) (x : P.adicCompletion E)
    (hx : Valued.v x ≤ 1) : ∃ a : OF E, Valued.v (x - iota a P) < 1 := by
  obtain ⟨b, hb⟩ := ReciprocityTheory.Aut.adic_exists_approx (R := 𝓞 E) (K := E) P x hx
  obtain ⟨a, ha⟩ := h b
  refine ⟨a, ?_⟩
  rw [ReciprocityTheory.Aut.adic_algebraMap_R] at hb
  have h1 : iota a P = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (algebraMap (OF E) (𝓞 E) a)) := rfl
  have h2 : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (b - algebraMap (OF E) (𝓞 E) a))) < 1 := by
    rw [ReciprocityTheory.Aut.adic_valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    exact (P.intValuation_lt_one_iff_mem _).2 ha
  have := Valuation.map_add_lt _ hb h2
  rwa [map_sub, map_sub, sub_add_sub_cancel, ← h1] at this

theorem locIn_iff {q : HeightOneSpectrum (OF E)} {P P' : HeightOneSpectrum (𝓞 E)} (hP : Over P q) (hP' : Over P' q)
    (hne : P' ≠ P) (hall : ∀ R, Over R q → R = P ∨ R = P') (y : (Af E)ˣ) {a b t : OF E}
    (ha : Valued.v ((y : Af E) P' - iota a P') < 1) (hb : Valued.v ((y : Af E) P - iota b P) < 1)
    (ht : t ∉ q.asIdeal) (r : (P.adicCompletion E)ˣ) (hr : (r : P.adicCompletion E) = iota t P) :
    LocIn 1 q (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) ↔ b - t * a ∈ q.asIdeal := by
  have e1 : (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) P = (iota t P)⁻¹ * (y : Af E) P := by
    rw [Units.val_mul, mul_coord, inv_coord, single_self, hr]
  have e2 : (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) P' = (y : Af E) P' := by
    rw [Units.val_mul, mul_coord, inv_coord, suppAt_single P r P' hne, inv_one, one_mul]
  have hv := val_iota_eq_one hP ht
  have h0 : iota t P ≠ 0 := hr ▸ r.ne_zero
  constructor
  · rintro ⟨d, hd⟩
    have h1 := (le_exp_iff _).1 (hd P hP)
    have h2 := (le_exp_iff _).1 (hd P' hP')
    rw [e1] at h1
    rw [e2] at h2
    have h3 : d - a ∈ q.asIdeal := by
      rw [← val_iota_lt_iff hP', iota_sub, sub_coord]
      have := Valuation.map_sub_lt _ ha h2
      rwa [sub_sub_sub_cancel_left] at this
    have h4 : b - t * d ∈ q.asIdeal := by
      rw [← val_iota_lt_iff hP, iota_sub, iota_mul, sub_coord, mul_coord]
      have : iota b P - iota t P * iota d P =
          iota t P * ((iota t P)⁻¹ * (y : Af E) P - iota d P) - ((y : Af E) P - iota b P) := by
        rw [mul_sub, mul_inv_cancel_left₀ h0]; ring
      rw [this]
      refine Valuation.map_sub_lt _ ?_ hb
      rwa [map_mul, hv, one_mul]
    have := add_mem h4 (q.asIdeal.mul_mem_left t h3)
    convert this using 1
    ring
  · intro h
    refine ⟨a, fun R hR => (le_exp_iff _).2 ?_⟩
    rcases hall R hR with rfl | rfl
    · rw [← val_iota_lt_iff hP, iota_sub, iota_mul, sub_coord, mul_coord] at h
      have : (iota t R)⁻¹ * (y : Af E) R - iota a R =
          (iota t R)⁻¹ * (((y : Af E) R - iota b R) + (iota b R - iota t R * iota a R)) := by
        rw [sub_add_sub_cancel, mul_sub, inv_mul_cancel_left₀ h0]
      rw [e1, this, map_mul, map_inv₀, hv, inv_one, one_mul]
      exact Valuation.map_add_lt _ hb h
    · rwa [e2]

theorem notMem_of_approx {q : HeightOneSpectrum (OF E)} {P : HeightOneSpectrum (𝓞 E)} (hP : Over P q)
    {x : P.adicCompletion E} (hx : Valued.v x = 1) {a : OF E} (ha : Valued.v (x - iota a P) < 1) : a ∉ q.asIdeal := by
  intro h
  have := Valuation.map_add_lt _ ha ((val_iota_lt_iff hP a).2 h)
  rw [sub_add_cancel, hx] at this
  exact lt_irrefl _ this

theorem exists_representatives : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : HeightOneSpectrum (OF E))
    (P : HeightOneSpectrum (𝓞 E)), Splits q → Over P q → ∃ R : Finset (P.adicCompletion E)ˣ,
      R.card + 1 = Ideal.absNorm q.asIdeal ∧ (∀ r ∈ R, Valued.v (r : P.adicCompletion E) = 1) ∧
      ∀ y : (Af E)ˣ, (∀ P', Over P' q → Valued.v ((y : Af E) P') = 1) →
        ∃! r, r ∈ R ∧ LocIn 1 q (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) := by
  intro E _ _ _ q P hs hP
  classical
  obtain ⟨htwo, hf⟩ := GlobalTheory.CMVal.Euler.SplitPlace.split_place E q hs
  obtain ⟨P', hne, hP'⟩ : ∃ P', P' ≠ P ∧ Over P' q := by
    obtain ⟨P₁, P₂, h, h1, h2⟩ := hs
    by_cases h' : P₁ = P
    · exact ⟨P₂, fun e => h (h'.trans e.symm), h2⟩
    · exact ⟨P₁, h', h1⟩
  have hall := htwo P P' hP hP' hne.symm
  haveI := q.isMaximal
  letI : Field (OF E ⧸ q.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (OF E ⧸ q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ q.ne_bot
  letI : Fintype (OF E ⧸ q.asIdeal) := Fintype.ofFinite _
  choose t ht using fun c : (OF E ⧸ q.asIdeal)ˣ => Ideal.Quotient.mk_surjective (c : OF E ⧸ q.asIdeal)
  have htq : ∀ c, t c ∉ q.asIdeal := fun c h => c.ne_zero (by rw [← ht c]; exact Ideal.Quotient.eq_zero_iff_mem.2 h)
  have h0 : ∀ c, iota (t c) P ≠ 0 := fun c h => by
    have := val_iota_eq_one hP (htq c)
    rw [h, map_zero] at this
    exact zero_ne_one this
  let u : (OF E ⧸ q.asIdeal)ˣ → (P.adicCompletion E)ˣ := fun c => Units.mk0 _ (h0 c)
  have hu : ∀ c, (u c : P.adicCompletion E) = iota (t c) P := fun c => rfl
  have hinj : Function.Injective u := fun c c' h => by
    have h1 : iota (t c) P = iota (t c') P := by rw [← hu, ← hu, h]
    have h2 : t c - t c' ∈ q.asIdeal := by
      rw [← val_iota_lt_iff hP, iota_sub, sub_coord, h1, sub_self, map_zero]
      exact zero_lt_one
    apply Units.ext
    rw [← ht c, ← ht c']
    exact Ideal.Quotient.eq.2 h2
  refine ⟨Finset.univ.image u, ?_, ?_, fun y hy => ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_units, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    exact Nat.sub_add_cancel Fintype.card_pos
  · intro r hr
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    exact val_iota_eq_one hP (htq c)
  · obtain ⟨a, ha⟩ := exists_iota_approx (hf P' hP').2.2 _ (hy P' hP').le
    obtain ⟨b, hb⟩ := exists_iota_approx (hf P hP).2.2 _ (hy P hP).le
    have ha0 : Ideal.Quotient.mk q.asIdeal a ≠ 0 := fun h =>
      notMem_of_approx hP' (hy P' hP') ha (Ideal.Quotient.eq_zero_iff_mem.1 h)
    have hb0 : Ideal.Quotient.mk q.asIdeal b ≠ 0 := fun h =>
      notMem_of_approx hP (hy P hP) hb (Ideal.Quotient.eq_zero_iff_mem.1 h)
    have key : ∀ c, LocIn 1 q (((single P (u c))⁻¹ * y : (Af E)ˣ) : Af E) ↔
        c = Units.mk0 _ hb0 * (Units.mk0 _ ha0)⁻¹ := fun c => by
      rw [locIn_iff hP hP' hne hall y ha hb (htq c) (u c) (hu c), ← Ideal.Quotient.eq, map_mul, ht, eq_mul_inv_iff_mul_eq,
        Units.ext_iff, Units.val_mul, Units.val_mk0, Units.val_mk0, eq_comm]
    refine ⟨u _, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key _).2 rfl⟩, ?_⟩
    rintro r ⟨hr, h⟩
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hr
    rw [(key c).1 h]

end GlobalTheory.CMVal.Euler.Resid
end
end

