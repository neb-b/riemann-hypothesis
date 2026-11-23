module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDual
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimeIdempotentIntegralAdeles
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryStabilizerLiftOfSplitIdempotent
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsChoiceAndIsChoiceOfCard
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.SplitChoice

theorem exists_int_sub_mem_pow {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 E))
    (hP : P.IsMaximal) (hm : (p : 𝓞 E) ∈ P) (hN : Ideal.absNorm P = p) (h2 : (p : 𝓞 E) ∉ P ^ 2) (k : ℕ)
    (a : 𝓞 E) : ∃ m : ℤ, a - m ∈ P ^ k := by
  first
  | exact @_root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow
  | exact _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow
  | (apply _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSubMemPow.exists_int_sub_mem_pow ..)

theorem not_isConj_self (I : AutInst) {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 I.E))
    (hm : (p : 𝓞 I.E) ∈ v.asIdeal) (hN : Ideal.absNorm v.asIdeal = p) (h2 : (p : 𝓞 I.E) ∉ v.asIdeal ^ 2) :
    ¬ IsConj I v v := by
  intro h
  let st : 𝓞 I.E →+* 𝓞 I.E := RingOfIntegers.mapRingHom (starRingEnd I.E)
  have hst : ∀ a : 𝓞 I.E, (st a : I.E) = star (a : I.E) := fun a => rfl
  have hmap : v.asIdeal.map st ≤ v.asIdeal :=
    Ideal.map_le_iff_le_comap.2 fun a ha => (h a (st a) (hst a)).1 ha
  have hfix : ∀ a, st a = a := fun a => by
    have hall : ∀ k, st a - a ∈ v.asIdeal ^ k := fun k => by
      obtain ⟨m, hm'⟩ := exists_int_sub_mem_pow hp v.asIdeal v.isMaximal hm hN h2 k a
      have h3 : st (a - m) ∈ v.asIdeal ^ k := by
        have := Ideal.mem_map_of_mem st hm'
        rw [Ideal.map_pow] at this
        exact Ideal.pow_right_mono hmap k this
      rw [map_sub, map_intCast] at h3
      simpa using sub_mem h3 hm'
    have := Ideal.iInf_pow_eq_bot_of_isDomain v.asIdeal v.isPrime.ne_top
    have h4 : st a - a ∈ (⊥ : Ideal (𝓞 I.E)) := this ▸ Ideal.mem_iInf.2 hall
    exact sub_eq_zero.1 h4
  have hfixE : ∀ x : I.E, star x = x := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 I.E) x
    have ha : star (algebraMap (𝓞 I.E) I.E a) = algebraMap (𝓞 I.E) I.E a := by
      rw [← hst a, hfix]
    have hb : star (algebraMap (𝓞 I.E) I.E b) = algebraMap (𝓞 I.E) I.E b := by
      rw [← hst b, hfix]
    rw [star_div₀, ha, hb]
  have hsurj : Function.Surjective (algebraMap I.F I.E) := fun x => (I.cm.fixed x).1 (hfixE x)
  have h1 : Module.finrank I.F I.E = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap I.F I.E).injective, hsurj⟩
  have := I.cm.deg2
  omega

theorem ncard_places_eq {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 E) | (p : 𝓞 E) ∈ v.asIdeal}.ncard =
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hp0 : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).mpr hpZ
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := hpr.isMaximal hp0
  rw [← Set.ncard_image_of_injective _ (fun _ _ h => HeightOneSpectrum.ext h :
    Function.Injective (HeightOneSpectrum.asIdeal : HeightOneSpectrum (𝓞 E) → _))]
  congr 1
  ext P
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨v.isPrime, ⟨hmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) ?_⟩⟩
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
    exact hv
  · rintro ⟨hP, hl⟩
    refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 P⟩, ?_, rfl⟩
    have : (p : ℤ) ∈ P.under ℤ := hl.over ▸ Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at this
    exact this

theorem exists_isChoice_and_isChoice_of_card : ∀ (I : AutInst) (g : Fin 2 → ℕ), (∀ k, (g k).Prime) → g 0 ≠ g 1 → (∀ k (P : Ideal (𝓞 I.E)), P.IsMaximal → ((g k : ℕ) : 𝓞 I.E) ∈ P → Ideal.absNorm P = g k ∧ ((g k : ℕ) : 𝓞 I.E) ∉ P ^ 2) → (∃ w : ∀ _ : Fin 2, Fin I.f → HeightOneSpectrum (𝓞 I.E), IsChoice I g (fun _ => Fin I.f) w) ∧ ∀ (Pl : Fin 2 → Type) [∀ k, Fintype (Pl k)] (w : ∀ k, Pl k → HeightOneSpectrum (𝓞 I.E)), (∀ k, Fintype.card (Pl k) = I.f) → (∀ k v, ((g k : ℕ) : 𝓞 I.E) ∈ (w k v).asIdeal) → (∀ k, Function.Injective (w k)) → (∀ k v v', ¬ IsConj I (w k v) (w k v')) → IsChoice I g Pl w := by
  intro I g hg hne h
  have hdeg : Module.finrank ℚ I.E = 2 * I.f := by
    rw [← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2, AutInst.f, mul_comm]
  refine GlobalTheory.Mem.RowsBundle.isChoice_of_card I g hg hne (fun k v hv => ?_) Module.finrank_pos fun k => ?_
  · obtain ⟨h1, h2⟩ := h k v.asIdeal v.isMaximal hv
    exact ⟨h1, h2, not_isConj_self I (hg k) v hv h1 h2⟩
  · rw [ncard_places_eq (hg k),
      GlobalTheory.ncard_primesOver_eq_finrank_of_absNorm_eq_of_not_mem_sq I.E (g k) (hg k) (h k), hdeg]

end GlobalTheory.SplitChoice
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLatticeCovolumeInverseIdeal
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm Module
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.CovIdeal

open GlobalTheory.LatFacts

variable (E : Type) [Field E] [NumberField E]

def lat (I : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) (Fin 1 → E) :=
  (I : Submodule (𝓞 E) E).comap (LinearMap.proj 0)

theorem mem_lat (I : FractionalIdeal (𝓞 E)⁰ E) (y : Fin 1 → E) : y ∈ lat E I ↔ y 0 ∈ I := by
  simp [lat]

theorem lat_eq_map (I : FractionalIdeal (𝓞 E)⁰ E) :
    lat E I = (I : Submodule (𝓞 E) E).map (LinearMap.single (𝓞 E) (fun _ : Fin 1 => E) 0) := by
  ext y
  rw [mem_lat, Submodule.mem_map]
  constructor
  · intro h
    refine ⟨y 0, h, ?_⟩
    funext a
    fin_cases a
    simp
  · rintro ⟨x, hx, rfl⟩
    simpa using hx

theorem isLattice_lat (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≠ 0) : Submodule.IsLattice E (lat E I) := by
  apply Submodule.IsLattice.of_fg
  rw [lat_eq_map]
  exact (FractionalIdeal.fg_of_isNoetherianRing le_rfl I).map _

theorem latAt_lat [_root_.NumberField.IsTotallyComplex E] (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    latAt E 1 (lat E I.1) (oneInf E 1) = Submodule.span ℤ (Set.range
      ((Pi.basis fun _ : Fin 1 => mixedEmbedding.fractionalIdealLatticeBasis E I).map (mix E 1))) := by
  set B := mixedEmbedding.fractionalIdealLatticeBasis E I

  let φ : mixedEmbedding.mixedSpace E →ₗ[ℤ] VecInf E 1 :=
    ((mix E 1).toLinearMap.toAddMonoidHom.comp
      (AddMonoidHom.single (fun _ : Fin 1 => mixedEmbedding.mixedSpace E) 0)).toIntLinearMap
  have hφ : ∀ z, φ z = mix E 1 (Pi.single 0 z) := fun _ => rfl

  have key : ∀ (y : Fin 1 → E) (w : InfinitePlace E),
      (Matrix.of (oneInf E 1 w))⁻¹ *ᵥ (fun a => w.embedding (y a)) = φ (mixedEmbedding E (y 0)) w := by
    intro y w
    rw [of_oneInf, inv_one, one_mulVec, hφ]
    funext a
    fin_cases a
    simp [mix_apply]
  have hrange : Set.range ((Pi.basis fun _ : Fin 1 => B).map (mix E 1)) = φ '' Set.range B := by
    ext x
    constructor
    · rintro ⟨⟨a, k⟩, rfl⟩
      have ha : a = 0 := Subsingleton.elim _ _
      subst ha
      exact ⟨B k, ⟨k, rfl⟩, by simp [hφ, Basis.map_apply, Pi.basis_apply]⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      exact ⟨⟨0, k⟩, by simp [hφ, Basis.map_apply, Pi.basis_apply]⟩

  have hspan : Submodule.span ℤ (mixedEmbedding E '' (I.1 : Set E)) = Submodule.span ℤ (Set.range B) := by
    conv_rhs => rw [← Submodule.span_eq (Submodule.span ℤ (Set.range B))]
    congr 1
    ext x
    rw [SetLike.mem_coe, mixedEmbedding.mem_span_fractionalIdealLatticeBasis]
  unfold latAt
  rw [hrange, Submodule.span_image, ← hspan, ← Submodule.span_image, ← Set.image_comp]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y 0, (mem_lat E _ y).1 hy, funext fun w => (key y w).symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨fun _ => t, (mem_lat E _ _).2 ht, funext fun w => key _ w⟩

theorem covAt_lat [_root_.NumberField.IsTotallyComplex E] (I : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    covAt E 1 (latAt E 1 (lat E I.1) (oneInf E 1)) =
      (FractionalIdeal.absNorm I.1 : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E := by

  have hO := volume_fd_intB E 1
  rw [mul_one, intB, volume_fd_map, pow_one, measureReal_def] at hO

  rw [latAt_lat, covAt_span, volume_fd_map, pow_one, measureReal_def,
    mixedEmbedding.volume_fundamentalDomain_fractionalIdealLatticeBasis, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)), hO]

theorem covolume_inv_ideal : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ Λ₀ : Submodule (𝓞 E) (Fin 1 → E), (∀ y, y ∈ Λ₀ ↔ ∀ t ∈ 𝔞, (t : E) * y 0 ∈ (algebraMap (𝓞 E) E).range) ∧ Submodule.IsLattice E Λ₀ ∧ covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) = Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E / (Ideal.absNorm 𝔞 : ℝ) := by
  intro E _ _ hE 𝔞 h𝔞
  have hne : (𝔞 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]

  let J : (FractionalIdeal (𝓞 E)⁰ E)ˣ := Units.mk0 (𝔞 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ (inv_ne_zero hne)
  refine ⟨lat E J.1, fun y => ?_, isLattice_lat E J.1 (inv_ne_zero hne), ?_⟩
  · rw [mem_lat]
    change y 0 ∈ (𝔞 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ ↔ _
    rw [FractionalIdeal.mem_inv_iff hne]
    constructor
    · intro h t ht
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1
        (h (t : E) (FractionalIdeal.mem_coeIdeal_of_mem _ ht))
      exact ⟨r, by rw [hr, mul_comm]⟩
    · intro h x hx
      obtain ⟨t, ht, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
      obtain ⟨r, hr⟩ := h t ht
      exact (FractionalIdeal.mem_one_iff _).2 ⟨r, by rw [hr, mul_comm]⟩
  · have := hE
    rw [covAt_lat E J]
    change (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : ℝ) * _ = _
    rw [map_inv₀, FractionalIdeal.coeIdeal_absNorm]
    push_cast
    ring

end GlobalTheory.CovIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasurableUnitaryLeviBlockMap
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm UJ inUJ isClosedEmbeddingMatrix)

noncomputable section

namespace GlobalTheory.LeviIso

theorem measurable_matInv (m : ℕ) :
    Measurable fun x : Fin m → Fin m → ℂ => (fun r s => (Matrix.of x)⁻¹ r s : Fin m → Fin m → ℂ) := by

  have hdet : Continuous fun x : Fin m → Fin m → ℂ => (Matrix.of x).det :=
    (continuous_id (X := Matrix (Fin m) (Fin m) ℂ)).matrix_det
  have hadj : Continuous fun x : Fin m → Fin m → ℂ => (Matrix.of x).adjugate :=
    (continuous_id (X := Matrix (Fin m) (Fin m) ℂ)).matrix_adjugate
  refine Measurable.of_eval fun r => Measurable.of_eval fun s => ?_
  have key : (fun x : Fin m → Fin m → ℂ => (Matrix.of x)⁻¹ r s) =
      fun x => ((Matrix.of x).det)⁻¹ * (Matrix.of x).adjugate r s := by
    funext x
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [key]
  exact (hdet.measurable.inv).mul
    (((continuous_apply s).comp ((continuous_apply r).comp hadj)).measurable)

theorem measurableEmbedding_uMat {n : ℕ} (ε : Fin n → Bool) :
    MeasurableEmbedding fun g : UJ ε => (fun r s => uMat g r s : Fin n → Fin n → ℂ) := by

  have h : Topology.IsClosedEmbedding fun g : UJ ε => (fun r s => uMat g r s : Fin n → Fin n → ℂ) :=
    (isClosedEmbeddingMatrix n ε).1
  exact h.measurableEmbedding

theorem measurable_lev {n n₀ a : ℕ} {j : Fin a → ℕ} (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ) :
    Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ =>
      (fun r s => lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) r s : Fin n → Fin n → ℂ) := by

  let Φ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) →
      Fin n → Fin n → ℂ := fun w r s =>
    (∑ i, B i * Matrix.of (w.1 i) * (B i)ᴴ + ∑ i, Jm ε * B i * (Matrix.of (w.2.1 i))ᴴ * (B i)ᴴ * Jm ε +
      B₀ * Matrix.of w.2.2 * B₀ᴴ) r s
  have hΦ : Continuous Φ := by
    refine continuous_pi fun r => continuous_pi fun s => ?_
    refine Continuous.matrix_elem ?_ r s
    refine Continuous.add (Continuous.add ?_ ?_) ?_
    · refine continuous_finsetSum _ fun i _ => ?_
      exact (continuous_const.matrix_mul
        ((continuous_apply i).comp continuous_fst : Continuous fun w : (∀ i, Fin (j i) → Fin (j i) → ℂ) ×
          (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) => (Matrix.of (w.1 i)))).matrix_mul
        continuous_const
    · refine continuous_finsetSum _ fun i _ => ?_
      exact ((continuous_const.matrix_mul
        ((continuous_apply i).comp (continuous_fst.comp continuous_snd) : Continuous fun w :
          (∀ i, Fin (j i) → Fin (j i) → ℂ) × (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) =>
            (Matrix.of (w.2.1 i))).matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
        continuous_const
    · exact (continuous_const.matrix_mul
        ((continuous_snd.comp continuous_snd) : Continuous fun w : (∀ i, Fin (j i) → Fin (j i) → ℂ) ×
          (∀ i, Fin (j i) → Fin (j i) → ℂ) × (Fin n₀ → Fin n₀ → ℂ) => (Matrix.of w.2.2))).matrix_mul
        continuous_const
  have hinv : Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ =>
      (fun i r s => (Matrix.of (z.1 i))⁻¹ r s : ∀ i, Fin (j i) → Fin (j i) → ℂ) :=
    Measurable.of_eval fun i =>
      (measurable_matInv (j i)).comp ((measurable_pi_apply i).comp measurable_fst)
  have hg : Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ =>
      (fun r s => uMat z.2 r s : Fin n₀ → Fin n₀ → ℂ) :=
    (measurableEmbedding_uMat ε₀).measurable.comp measurable_snd
  have hcomp := hΦ.measurable.comp (measurable_fst.prodMk (hinv.prodMk hg))
  convert hcomp using 1
  funext z r s
  simp only [Function.comp_apply, Φ, lev]
  rfl

theorem exists_measurable_levMap (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool)
    (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ) (h : IsFrame ε ε₀ B B₀) :
    ∃ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ → UJ ε, Measurable θ ∧
      ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) →
        uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) := by
  classical

  let S : Set ((∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀) := {z | ∀ i, (Matrix.of (z.1 i)).det ≠ 0}
  have hex : ∀ z ∈ S, ∃ g : UJ ε, uMat g = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) := by
    intro z hz
    have hU : inUJ ε (lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) := h.inUJ_lev _ _ hz z.2.2
    have hr : lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) ∈
        Set.range (fun g : UJ ε => ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) := by
      rw [(isClosedEmbeddingMatrix n ε).2]
      exact hU
    obtain ⟨g, hg⟩ := hr
    exact ⟨g, hg⟩
  let θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ → UJ ε := fun z =>
    if hz : z ∈ S then (hex z hz).choose else 1
  have hθ : ∀ z ∈ S, uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) := by
    intro z hz
    simp only [θ, dif_pos hz]
    exact (hex z hz).choose_spec
  refine ⟨θ, ?_, fun z hz => hθ z hz⟩
  have hdet : ∀ i, Measurable fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ => (Matrix.of (z.1 i)).det :=
    fun i =>
      have hc : Continuous fun x : Fin (j i) → Fin (j i) → ℂ => (Matrix.of x).det :=
        (continuous_id (X := Matrix (Fin (j i)) (Fin (j i)) ℂ)).matrix_det
      hc.measurable.comp ((measurable_pi_apply i).comp measurable_fst)
  have hS : MeasurableSet S := by
    have : S = ⋂ i, (fun z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × UJ ε₀ => (Matrix.of (z.1 i)).det) ⁻¹' {0}ᶜ := by
      ext z
      simp [S]
    rw [this]
    exact MeasurableSet.iInter fun i => (hdet i) (measurableSet_singleton 0).compl
  rw [← (measurableEmbedding_uMat ε).measurable_comp_iff]
  have heq : ((fun g : UJ ε => (fun r s => uMat g r s : Fin n → Fin n → ℂ)) ∘ θ) = fun z =>
      if z ∈ S then (fun r s => lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2) r s : Fin n → Fin n → ℂ)
      else (fun r s => uMat (1 : UJ ε) r s) := by
    funext z
    by_cases hz : z ∈ S
    · simp only [Function.comp_apply, if_pos hz, hθ z hz]
    · simp only [Function.comp_apply, if_neg hz, θ, dif_neg hz]
  rw [heq]
  exact Measurable.ite hS (measurable_lev ε ε₀ B B₀) measurable_const

end GlobalTheory.LeviIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMemKsetActsAsGLModSplitPrime
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev

theorem sigR_sigR_af (I : AutInst) (x : I.E ⊗[I.F] Af I.F) :
    Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.sigR I.cm.sig (Af I.F) x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp [Formalism.UG.sigR, Formalism.BasicNotions.CMData.sig]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem isHerm_af (I : AutInst) :
    Formalism.UG.IsHerm (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) := by
  have hs : ∀ a : I.E, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) a) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (star a) := by
    intro a
    simp [Formalism.UG.sigR, Formalism.UG.inclE, Formalism.BasicNotions.CMData.sig] <;> rfl
  have hJ := I.J_herm
  unfold Formalism.UG.IsHerm Formalism.UG.cT at hJ ⊢
  ext i j
  have h := congrArg (fun M => M i j) hJ
  simp only [Matrix.transpose_apply, Matrix.map_apply, starRingEnd_apply] at h ⊢
  rw [hs, h]

theorem isUnit_det_af (I : AutInst) : IsUnit (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).det := by
  have h : (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))).det = Formalism.UG.inclE (F := I.F) (Af I.F) I.J.det :=
    (RingHom.map_det _ _).symm
  rw [h]
  exact (Ne.isUnit I.J_det).map _

theorem exists_mem_Kset_actsAs_trivial_away : ∀ (I : AutInst) (N p : ℕ) (w : HeightOneSpectrum (𝓞 I.E)) (fr : PlFrame I N p w), I.n = N → p.Prime → Ideal.absNorm w.asIdeal = p → ¬ IsConj I w w → ∀ M : GL (Fin N) (ZMod p), ∃ x ∈ I.Kset, (∀ (y : I.Lf) (h : I.fmat x *ᵥ (y : Fin I.n → _) ∈ I.Lf), fr.c ⟨_, h⟩ = (M : Matrix (Fin N) (Fin N) (ZMod p)) *ᵥ fr.c y) ∧ ∀ u : HeightOneSpectrum (𝓞 I.E), u ≠ w → ¬ IsConj I w u → ∀ y ∈ I.Lf, (I.fmat x - 1) *ᵥ y ∈ extId I u.asIdeal • I.Lf := by
  intro I N p w fr hN hp hw hw' M
  subst hN
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ε, hεε, h1ε, hεu, hεt, hεσ⟩ := _root_.GlobalTheory.RowLev.exists_prime_idempotent I w
  have hA := GlobalTheory.RowLev.intAf_approx_inter_unit_conj I 1 le_rfl
  have hL := GlobalTheory.AdelicLattice.adelicLattice_spec I 1 le_rfl
  have hX := GlobalTheory.RowLev.extId_mul_sup_natCast_conj I
  have hker : ∀ z, fr.r z = 0 ↔ z ∈ extId I w.asIdeal := fun z => by
    rw [← RingHom.mem_ker, fr.ker_r]
  have hrε : fr.r ε = 1 := by
    have h0 : fr.r (1 - ε) = 0 := (hker _).2 h1ε
    rw [map_sub, map_one, sub_eq_zero] at h0
    exact h0.symm
  obtain ⟨x, hxU, hxS, hact, htriv⟩ := _root_.GlobalTheory.SplitLift.exists_unitary_lift (I.E ⊗[I.F] Af I.F) (Formalism.UG.sigR I.cm.sig (Af I.F))
    (IntAf I.F I.E) I.n (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) I.Lf (ZMod p) fr.r fr.c ε
    (fun a => sigR_sigR_af I a) (fun a ha => hA.2.2.2 a ha) (isHerm_af I) (isUnit_det_af I)
    hL.2.2.2.1 hL.2.2.1 (fun y => GlobalTheory.AdelicLattice.adelicLattice_selfDual I y) hεε (hεσ hw') hrε
    (ZMod.ringHom_surjective fr.r) (fun z hz => hεt z fun h => hz ((hker z).2 h)) fr.c_surj
    (fun y hy => by rw [fr.ker_r]; exact (fr.c_ker y).1 hy) M
  refine ⟨⟨x, hxU⟩, hxS, fun y h => hact y h, ?_⟩
  intro u hu hcu y hy
  obtain ⟨z, hz, e⟩ := htriv y hy
  obtain ⟨u', hu'⟩ := hX.2.2.2.1 u
  have hu'w : u' ≠ w := by
    rintro rfl
    exact hcu (hX.2.2.2.2.1 u u' hu')
  obtain ⟨z', hz', hz'e⟩ := hX.2.2.2.2.2.2 u' u (hX.2.2.2.2.1 u u' hu') ε (hεu u' hu'w)
  have hmem : ε + z' ∈ extId I u.asIdeal := add_mem (hεu u hu) hz'
  have hfin : (I.fmat ⟨x, hxU⟩ - 1) *ᵥ y = (ε + z') • z := by
    change ((x : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) - 1) *ᵥ y = _
    rw [e, ← hz'e]
    rfl
  rw [hfin]
  exact Submodule.smul_mem_smul hmem hz

end GlobalTheory.RowLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRetractionOfProjective
section
namespace GlobalTheory.ProjectiveRetraction

open NumberField

theorem exists_retraction_of_projective {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [Module.Projective R (M ⧸ N)] :
    ∃ p : M →ₗ[R] M, (∀ x, p x ∈ N) ∧ ∀ x ∈ N, p x = x := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ (LinearMap.id : (M ⧸ N) →ₗ[R] (M ⧸ N))
    N.mkQ_surjective
  refine ⟨LinearMap.id - s ∘ₗ N.mkQ, fun x => ?_, fun x hx => ?_⟩
  · have h1 : N.mkQ (s (N.mkQ x)) = N.mkQ x := LinearMap.congr_fun hs (N.mkQ x)
    have h2 : N.mkQ (x - s (N.mkQ x)) = 0 := by rw [map_sub, h1, sub_self]
    exact (Submodule.Quotient.mk_eq_zero N).1 h2
  · have h0 : N.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero N).2 hx
    show x - s (N.mkQ x) = x
    rw [h0, map_zero, sub_zero]

theorem exists_retraction {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (M0 L : Submodule (𝓞 E) V) (hL : L.FG)
    (h : Formalism.MainNotions.S.Lat.IsPrimitiveSub M0 L) :
    ∃ r : L →ₗ[𝓞 E] M0, ∀ x : M0, r ⟨(x : V), h.1 x.2⟩ = x := by
  set N : Submodule (𝓞 E) L := M0.comap L.subtype with hN
  have hsat : ∀ (a : 𝓞 E), a ≠ 0 → ∀ x : L, a • x ∈ N → x ∈ N := by
    intro a ha x hx
    have hx' : a • (x : V) ∈ M0 := hx
    have ha' : (algebraMap (𝓞 E) E a) ≠ 0 := by
      intro h0
      exact ha ((IsFractionRing.injective (𝓞 E) E) (by rw [h0, map_zero]))
    have h1 : (algebraMap (𝓞 E) E a) • (x : V) ∈ Submodule.span E (M0 : Set V) := by
      rw [algebraMap_smul]
      exact Submodule.subset_span hx'
    have h2 : (x : V) ∈ Submodule.span E (M0 : Set V) :=
      (Submodule.smul_mem_iff _ ha').1 h1
    show (x : V) ∈ M0
    rw [h.2]
    exact ⟨x.2, h2⟩
  have htor : Submodule.torsion (𝓞 E) (L ⧸ N) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := N.mkQ_surjective q
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hq
    have ha2 : N.mkQ ((a : 𝓞 E) • x) = 0 := by
      rw [map_smul]
      exact ha
    have hx : x ∈ N :=
      hsat a (nonZeroDivisors.ne_zero a.2) x ((Submodule.Quotient.mk_eq_zero N).1 ha2)
    exact (Submodule.Quotient.mk_eq_zero N).2 hx
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  haveI : Module.Flat (𝓞 E) (L ⧸ N) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  haveI : Module.FinitePresentation (𝓞 E) (L ⧸ N) := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) (L ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨p, hp1, hp2⟩ := exists_retraction_of_projective N
  refine ⟨LinearMap.codRestrict M0 (L.subtype ∘ₗ p) (fun x => hp1 x), fun x => ?_⟩
  apply Subtype.ext
  have hx : (⟨(x : V), h.1 x.2⟩ : L) ∈ N := x.2
  show ((p ⟨(x : V), h.1 x.2⟩ : L) : V) = x
  rw [hp2 _ hx]

end GlobalTheory.ProjectiveRetraction
end

