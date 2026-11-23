module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0193
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl

open IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.FinPl

section General

variable {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]

theorem exists_int_smul_mem_of_mem_span (M : Submodule (𝓞 E) V) {y : V}
    (hy : y ∈ Submodule.span E (M : Set V)) : ∃ c : ℤ, c ≠ 0 ∧ c • y ∈ M := by
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • y = a • (b • y) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact M.add_mem (zsmul_mem hax b) (zsmul_mem hby a)
  | smul e x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨c, hc, hint⟩ := exists_integral_multiples ℤ ℚ ({e} : Finset E)
    have he : IsIntegral ℤ (c • e) := hint e (by simp)
    refine ⟨c * a, mul_ne_zero hc ha, ?_⟩
    obtain ⟨o, ho⟩ : ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = c • e := ⟨⟨c • e, he⟩, rfl⟩
    have h : (c * a) • (e • x) = o • (a • x) := by
      rw [← algebraMap_smul E o (a • x), ho, mul_smul, smul_comm a e x, smul_assoc]
    rw [h]
    exact M.smul_mem o hax

theorem exists_int_smul_le (L M : Submodule (𝓞 E) V) (hL : L.FG)
    (hM : Submodule.span E (M : Set V) = ⊤) : ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ L, d • x ∈ M := by
  classical
  obtain ⟨G, rfl⟩ := hL
  have hg : ∀ g ∈ G, ∃ c : ℤ, c ≠ 0 ∧ c • g ∈ M := fun g _ =>
    exists_int_smul_mem_of_mem_span M (by rw [hM]; trivial)
  choose! c hc0 hcM using hg
  refine ⟨∏ g ∈ G, c g, Finset.prod_ne_zero_iff.2 hc0, fun x hx => ?_⟩
  let N : Submodule (𝓞 E) V :=
    { carrier := {y | (∏ g ∈ G, c g) • y ∈ M}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, smul_add] at *; exact M.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun r y hy => by
        simp only [Set.mem_setOf_eq] at *
        rw [smul_comm]; exact M.smul_mem r hy }
  have hle : Submodule.span (𝓞 E) (G : Set V) ≤ N := by
    rw [Submodule.span_le]
    intro g hg
    show (∏ g ∈ G, c g) • g ∈ M
    rw [← Finset.mul_prod_erase G c hg, mul_comm, mul_smul]
    exact zsmul_mem (hcM g hg) _
  exact hle hx

end General

variable {D : D7}

theorem finite_places_int (d : ℤ) (hd : d ≠ 0) :
    {v : Pl D | ((d : 𝓞 D.host.F)) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {((d : 𝓞 D.host.F))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hd
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem pairA_tmul_int_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (d : ℤ) (hd : d ≠ 0)
    (α : Af F) (e : E) :
    pairA F 0 α ⊗ₜ[F] (1 * e) = pairA F 0 ((d : F)⁻¹ • α) ⊗ₜ[F] (1 * (d • e)) := by
  have hdF : (d : F) ≠ 0 := Int.cast_ne_zero.2 hd
  have h : (d : F) • pairA F 0 ((d : F)⁻¹ • α) = pairA F 0 α := by
    have h1 : (d : F) • pairA F 0 ((d : F)⁻¹ • α) = pairA F 0 ((d : F) • (d : F)⁻¹ • α) :=
      Prod.ext (smul_zero (d : F)) rfl
    rw [h1, smul_smul, mul_inv_cancel₀ hdF, one_smul]
  rw [one_mul, one_mul, ← Int.cast_smul_eq_zsmul F, ← TensorProduct.smul_tmul, h]

theorem latV_le_of_int_smul (S : HSp D) (L M : Lat S) (d : ℤ) (hd : d ≠ 0)
    (hLM : ∀ x ∈ L, d • x ∈ M) (v : Pl D) (hv : ((d : 𝓞 D.host.F)) ∉ v.asIdeal) :
    latV S L (· = v) ≤ latV S M (· = v) := by
  rw [latV, latMul, AddSubgroup.closure_le]
  rintro y ⟨α, hα, hsupp, a, ha, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at ha
  subst ha
  have hval : Valued.v (algebraMap D.host.F (v.adicCompletion D.host.F) (d : D.host.F)) = 1 := by
    have h1 := (v.valuation_eq_one_iff_notMem (K := D.host.F)).mpr hv
    have h2 := v.valuedAdicCompletion_eq_valuation' (K := D.host.F) ((d : D.host.F))
    have h4 : (((d : 𝓞 D.host.F)) : D.host.F) = ((d : D.host.F)) :=
      map_intCast (algebraMap (𝓞 D.host.F) D.host.F) _
    exact h2.trans (h4 ▸ h1)
  apply AddSubgroup.subset_closure
  refine ⟨((d : D.host.F))⁻¹ • α, ?_, ?_, 1, rfl, d • x, hLM x hx, ?_⟩
  · intro w
    rw [map_smul]
    by_cases hw : w = v
    · subst hw
      have hαw := hα w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hαw ⊢
      rw [Algebra.smul_def, map_mul, map_inv₀, map_inv₀, hval, inv_one, one_mul]
      exact hαw
    · rw [hsupp w hw, smul_zero]
      exact zero_mem _
  · intro w hw
    rw [map_smul, hsupp w hw, smul_zero]
  · funext i
    exact pairA_tmul_int_gen d hd α (x i)

theorem latV_eq_off_finite : ∀ (D : D7) (S : HSp D) (L M : Lat S), Submodule.IsFullLattice D.host.E L →
    Submodule.IsFullLattice D.host.E M → ∃ T : Finset (Pl D), ∀ v, v ∉ T → latV S L (· = v) = latV S M (· = v) := by
  intro D S L M hL hM
  obtain ⟨d₁, hd₁, h₁⟩ := exists_int_smul_le L M hL.fg hM.span_eq_top
  obtain ⟨d₂, hd₂, h₂⟩ := exists_int_smul_le M L hM.fg hL.span_eq_top
  have hd : d₁ * d₂ ≠ 0 := mul_ne_zero hd₁ hd₂
  refine ⟨(finite_places_int (D := D) (d₁ * d₂) hd).toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Int.cast_mul] at hv
  have hv₁ : ((d₁ : 𝓞 D.host.F)) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_right _ h)
  have hv₂ : ((d₂ : 𝓞 D.host.F)) ∉ v.asIdeal := fun h => hv (v.asIdeal.mul_mem_left _ h)
  exact le_antisymm (latV_le_of_int_smul S L M d₁ hd₁ h₁ v hv₁) (latV_le_of_int_smul S M L d₂ hd₂ h₂ v hv₂)

end GlobalTheory.FinPl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel ValuativeRel
open scoped Pointwise TensorProduct
open IsDedekindDomain NumberField

noncomputable section

namespace GlobalTheory.FinPl

theorem tensorProductBasis_repr_map_firstFactor {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A]
    [CommRing B] [Algebra F B] {ι : Type} (b : Module.Basis ι F E) (f : A →ₐ[F] B) (x : A ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis B b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) x) i =
      f ((Algebra.TensorProduct.basis A b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add (f := _), hx, hy]
  | tmul a m =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul, Algebra.smul_def]

theorem CMAdele_eq_zero_of_infinite_and_finite_components_zero (D : D7) (a : AE D) (h0 : infPart D a = 0) (hw : ∀ w : Pl D, compAt D w a = 0) :
    a = 0 := by
  let b := Module.Free.chooseBasis D.host.F D.host.E
  let bA := Algebra.TensorProduct.basis (AF D.host.F) b
  suffices hc : ∀ i, bA.repr a i = 0 by
    apply bA.repr.injective
    ext i
    simpa using hc i
  intro i
  have h1 : fstA D.host.F (bA.repr a i) = 0 := by
    have := tensorProductBasis_repr_map_firstFactor b (fstA D.host.F) a i
    rw [← this]
    change (Algebra.TensorProduct.basis _ b).repr (infPart D a) i = 0
    rw [h0]; simp only [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have h2 : ∀ w : Pl D, evalV D.host.F w (sndA D.host.F (bA.repr a i)) = 0 := by
    intro w
    have e1 := tensorProductBasis_repr_map_firstFactor b (sndA D.host.F) a i
    have e2 := tensorProductBasis_repr_map_firstFactor b (evalV D.host.F w)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) a) i
    have hw' : Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) a) = 0 := hw w
    rw [← e1, ← e2, hw', LinearEquiv.map_zero]
    rfl
  apply Prod.ext
  · exact h1
  · apply Subtype.ext
    funext w
    exact h2 w

theorem mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere (D : D7) (P : Pl D → Prop) (a : AE D) :
    a ∈ idAt D P ↔ infPart D a = 0 ∧ ∀ w : Pl D, ¬ P w → compAt D w a = 0 := by
  simp only [idAt, Submodule.mem_inf, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]

theorem placeIdempotent_infinite_and_finite_components (D : D7) (v : Pl D) (ε : AF D.host.F) (α : Af D.host.F)
    (hε : ε = pairA D.host.F 0 α) :
    infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 ∧
      ∀ w : Pl D, compAt D w (algebraMap (AF D.host.F) (AE D) ε) = evalV D.host.F w α ⊗ₜ[D.host.F] (1 : D.host.E) := by
  have ha : algebraMap (AF D.host.F) (AE D) ε = ε ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  refine ⟨?_, fun w => ?_⟩
  · rw [ha]
    change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (ε ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    rw [Algebra.TensorProduct.map_tmul, hε]
    exact TensorProduct.zero_tmul _ _
  · rw [ha]
    change Algebra.TensorProduct.map (evalV D.host.F w) (AlgHom.id D.host.F D.host.E)
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) (ε ⊗ₜ[D.host.F] (1 : D.host.E))) = _
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, hε]
    rfl

theorem mem_supportedAtPlace_iff_placeIdempotent_mul (D : D7) (v : Pl D) (e : AE D) (h0 : infPart D e = 0) (c1 : compAt D v e = 1)
    (c0 : ∀ w : Pl D, w ≠ v → compAt D w e = 0) (a : AE D) : a ∈ idAt D (· = v) ↔ e * a = a := by
  constructor
  · intro ha
    rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha
    obtain ⟨ha0, haw⟩ := ha
    rw [← sub_eq_zero]
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [RingHom.map_sub, RingHom.map_mul, h0, ha0, zero_mul, sub_zero]
    · intro w
      rw [RingHom.map_sub, RingHom.map_mul]
      by_cases h : w = v
      · subst h; rw [c1, one_mul, sub_self]
      · rw [haw w h, mul_zero, sub_zero]
  · intro ha
    rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
    refine ⟨?_, fun w hw' => ?_⟩
    · rw [← ha, RingHom.map_mul, h0, zero_mul]
    · rw [← ha, RingHom.map_mul, c0 w hw', zero_mul]

theorem placeIdempotent_mul_supportedOffPlace_eq_zero (D : D7) (v : Pl D) (e : AE D) (h0 : infPart D e = 0)
    (c0 : ∀ w : Pl D, w ≠ v → compAt D w e = 0) (a : AE D) (ha : a ∈ idAt D (· ≠ v)) : e * a = 0 := by
  rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere] at ha
  obtain ⟨ha0, haw⟩ := ha
  apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
  · rw [RingHom.map_mul, h0, zero_mul]
  · intro w
    rw [RingHom.map_mul]
    by_cases h : w = v
    · rw [haw w (fun h' => h' h), mul_zero]
    · rw [c0 w h, zero_mul]

theorem placeIdem_acts : ∀ (D : D7) (v : Pl D) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∀ a : AE D, a ∈ idAt D (· = v) ↔ algebraMap (AF D.host.F) (AE D) ε * a = a) ∧
    (∀ a : AE D, a ∈ idAt D (· ≠ v) → algebraMap (AF D.host.F) (AE D) ε * a = 0) := by
  intro D v ε ⟨α, hε, hv, hw⟩
  obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D v ε α hε
  have c1 : compAt D v (algebraMap (AF D.host.F) (AE D) ε) = 1 := by
    rw [hc, hv]; rfl
  have c0 : ∀ w : Pl D, w ≠ v → compAt D w (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    intro w h; rw [hc, hw w h, TensorProduct.zero_tmul]
  exact ⟨mem_supportedAtPlace_iff_placeIdempotent_mul D v _ h0 c1 c0, placeIdempotent_mul_supportedOffPlace_eq_zero D v _ h0 c0⟩

end GlobalTheory.FinPl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SkewHermitianTracePairingStandardCharacterPerfec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SkewPairing

theorem trace_one_tmul {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [CommRing R] [Algebra F R] (x : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] x) = algebraMap F R (Algebra.trace F E x) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

variable {D : D7}

theorem trace_incA (x : D.host.E) :
    Algebra.trace (AF D.host.F) (AE D) (incA D x) =
      algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E x) :=
  trace_one_tmul x

theorem cA_smul (c : AF D.host.F) (a : AE D) : cA D (c • a) = c • cA D a := by
  induction a using TensorProduct.inductionOn with
  | tmul x y => rfl
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem trace_star (x : D.host.E) :
    Algebra.trace D.host.F D.host.E (star x) = Algebra.trace D.host.F D.host.E x :=
  Algebra.trace_eq_of_algEquiv (AlgEquiv.ofBijective D.sp.cm.sig D.sp.cm.sig.bijective) x

theorem eq_zero_of_char {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {q : D.host.F}
    (h : ∀ t : AF D.host.F, ψ (t * algebraMap D.host.F (AF D.host.F) q) = 1) : q = 0 := by
  by_contra hq
  obtain ⟨I, hI, hP⟩ := Ring.not_isField_iff_exists_prime.1 (RingOfIntegers.not_isField D.host.F)
  obtain ⟨y, hy⟩ := GlobalTheory.StdCharLocal.psiV_ne_one D ψ hψ ⟨I, hP, hI⟩
  have h1 := h (pairA D.host.F 0 (singleV D.host.F ⟨I, hP, hI⟩ y) * algebraMap D.host.F (AF D.host.F) q⁻¹)
  rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hq, map_one, mul_one] at h1
  exact hy h1

theorem skew_perfect : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (M : Matrix (Fin ρ) (Fin ρ) D.host.E), Mᴴ = -M → (∀ c : skewA D ρ, ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) ((rat M : Mx D ρ ρ) * c.1).trace) = 1) → M = 0 := by
  intro D ψ hψ ρ M hM h
  have key : ∀ A : Matrix (Fin ρ) (Fin ρ) D.host.E, Algebra.trace D.host.F D.host.E (M * A).trace = 0 := by
    intro A
    refine eq_zero_of_char hψ fun t => ?_
    have hN : adj (rat (A - Aᴴ) : Mx D ρ ρ) = -rat (A - Aᴴ) := by
      rw [← rat_conjTranspose, ← rat_neg, conjTranspose_sub, conjTranspose_conjTranspose, neg_sub]
    have hc : t • (rat (A - Aᴴ) : Mx D ρ ρ) ∈ skewA D ρ := by
      rw [mem_skewA, ← smul_neg, ← hN]
      funext i j
      exact cA_smul t (rat (A - Aᴴ) j i)
    have h1 := h ⟨_, hc⟩
    have e1 : (M * (A - Aᴴ)).trace = (M * A).trace + star (M * A).trace := by
      rw [← trace_conjTranspose, conjTranspose_mul, hM, Matrix.mul_neg, trace_neg, trace_mul_comm Aᴴ, Matrix.mul_sub,
        trace_sub, sub_eq_add_neg]
    have e2 : ((rat M : Mx D ρ ρ) * (t • (rat (A - Aᴴ) : Mx D ρ ρ))).trace = t • incA D (M * (A - Aᴴ)).trace := by
      have hmul : (rat (M * (A - Aᴴ)) : Mx D ρ ρ) = rat M * rat (A - Aᴴ) :=
        Matrix.map_mul
      rw [Matrix.mul_smul, trace_smul, ← hmul, AddMonoidHom.map_trace (incA D)]
      rfl
    have e3 : algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D)
        ((rat M : Mx D ρ ρ) * (t • (rat (A - Aᴴ) : Mx D ρ ρ))).trace =
        t * algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E (M * A).trace) := by
      rw [e2, map_smul, trace_incA, e1, map_add (f := _), trace_star, smul_eq_mul, mul_left_comm, ← map_mul]
      congr 2
      ring
    rw [← e3]
    exact h1
  funext j i
  refine (traceForm_nondegenerate D.host.F D.host.E).1 (M j i) fun s => ?_
  have := key (Matrix.single i j s)
  rwa [trace_mul_single] at this

end GlobalTheory.SkewPairing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StarSmulVec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.LinkExist

theorem star_smul_vec {D : D7} {n : ℕ} (k : D.host.E) (v : Fin n → D.host.E) : star (k • v) = star k • star v := by
  funext i
  simp only [Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul']

theorem norm_smul_vec {D : D7} (L' : HSp D) (k : D.host.E) (v : Fin L'.rank → D.host.E) :
    star (k • v) ⬝ᵥ L'.gram *ᵥ (k • v) = star k * k * (star v ⬝ᵥ L'.gram *ᵥ v) := by
  rw [star_smul_vec, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

theorem link_of_norm : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ) (L' : HSp D) (ζ' : Fin L'.rank → D.host.E) (c : D.host.E), IsLineVec L' ζ' → star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = c * star c * (star ζ' ⬝ᵥ L'.gram *ᵥ ζ') → IsLineVec L' ((c / D.host.xi0) • ζ') ∧ Nonempty (Link B L' ((c / D.host.xi0) • ζ')) := by
  intro D ρ B L' ζ' c hl hn
  have hxi : D.host.xi0 ≠ 0 := GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hN := B.line.2
  rw [hn] at hN
  have hc : c ≠ 0 := fun h => hN (by simp [h])
  have hv : star ζ' ⬝ᵥ L'.gram *ᵥ ζ' ≠ 0 := fun h => hN (by simp [h])
  have hk : c / D.host.xi0 ≠ 0 := div_ne_zero hc hxi
  have hsk : star (c / D.host.xi0) ≠ 0 := star_ne_zero.2 hk
  set x := (c / D.host.xi0) • ζ' with hx
  have hnx : star x ⬝ᵥ L'.gram *ᵥ x = star (c / D.host.xi0) * (c / D.host.xi0) * (star ζ' ⬝ᵥ L'.gram *ᵥ ζ') :=
    norm_smul_vec L' _ ζ'
  have hn0 : star x ⬝ᵥ L'.gram *ᵥ x ≠ 0 := by
    rw [hnx]; exact mul_ne_zero (mul_ne_zero hsk hk) hv
  refine ⟨⟨hl.1, hn0⟩, ⟨{ τ := (-(star x ⬝ᵥ L'.gram *ᵥ x)⁻¹) • vecMulVec B.ζ (star x ᵥ* L'.gram), map := ?_, norm := ?_ }⟩⟩
  · rw [Matrix.smul_mulVec, vecMulVec_mulVec, ← Matrix.dotProduct_mulVec, op_smul_eq_smul, smul_smul, neg_mul, inv_mul_cancel₀ hn0, neg_one_smul]
  · rw [hn, hnx]
    have hsx : star D.host.xi0 ≠ 0 := star_ne_zero.2 hxi
    rw [star_div₀]
    field_simp

end GlobalTheory.Unf.LinkExist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalDoubleCosetRepsMul
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section

namespace GlobalTheory.ZonalSum

open GlobalTheory.CuspRep.ParLaws

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

theorem diagU_mul (p q : borel k (Fin N)) (i : Fin N) : diagU (p * q) i = diagU p i * diagU q i := by
  unfold diagU
  erw [map_mul]
  rw [Pi.mul_apply, map_mul]

theorem borelSph_mul_left {γ : Fin N → ℂ} {ψ : GL (Fin N) k → ℂ} (h : IsBorelSph k γ ψ) (hγ : ∀ i, γ i ≠ 0)
    {b : GL (Fin N) k} (hb : b ∈ borel k (Fin N)) (x : GL (Fin N) k) : ψ (b * x) = ψ b * ψ x := by
  obtain ⟨b', hb', w, hw, rfl⟩ := iwasawa_blockTriangular k (Fin N) Fin.val x
  have hb'' : b' ∈ borel k (Fin N) := (mem_borel _).2 hb'
  have hbb : b * b' ∈ borel k (Fin N) := mul_mem hb hb''
  have e1 : b * (b' * w) = (b * b') * w := (mul_assoc _ _ _).symm
  rw [e1, h.1 _ _ hw, h.1 _ _ hw]
  have t1 := fun i => (val_diagU ⟨b, hb⟩ i).symm
  have t2 := fun i => (val_diagU ⟨b', hb''⟩ i).symm
  have t3 := fun i => (val_diagU ⟨b * b', hbb⟩ i).symm
  rw [h.2 _ hb _ t1, h.2 _ hb'' _ t2, h.2 _ hbb _ t3, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e2 : (⟨b * b', hbb⟩ : borel k (Fin N)) = ⟨b, hb⟩ * ⟨b', hb''⟩ := rfl
  rw [e2, diagU_mul, ord_mul, zpow_add₀ (hγ i)]

theorem eq_of_isRepsK {g₀ : GL (Fin N) k} {R : Finset (GL (Fin N) k)} (hR : IsRepsK g₀ R)
    {g₁ g₂ : GL (Fin N) k} (h₁ : g₁ ∈ R) (h₂ : g₂ ∈ R) (h : g₁⁻¹ * g₂ ∈ KO k (Fin N)) : g₁ = g₂ := by
  obtain ⟨κ, hκ, κ', hκ', e⟩ := hR.1 g₂ h₂
  obtain ⟨g, -, hu⟩ := hR.2 κ hκ
  have a2 : g₂⁻¹ * (κ * g₀) ∈ KO k (Fin N) := by
    have : g₂⁻¹ * (κ * g₀) = κ'⁻¹ := by rw [e]; group
    rw [this]; exact inv_mem hκ'
  have a1 : g₁⁻¹ * (κ * g₀) ∈ KO k (Fin N) := by
    have : g₁⁻¹ * (κ * g₀) = (g₁⁻¹ * g₂) * (g₂⁻¹ * (κ * g₀)) := by group
    rw [this]; exact mul_mem h a2
  rw [hu g₁ ⟨h₁, a1⟩, hu g₂ ⟨h₂, a2⟩]

theorem exists_isRepsK {g₀ : GL (Fin N) k} {R : Finset (GL (Fin N) k)} (hR : IsRepsK g₀ R)
    {κ : GL (Fin N) k} (hκ : κ ∈ KO k (Fin N)) {g : GL (Fin N) k} (hg : g ∈ R) :
    ∃ g' ∈ R, g'⁻¹ * (κ * g) ∈ KO k (Fin N) := by
  obtain ⟨κ₁, hκ₁, κ₁', hκ₁', e⟩ := hR.1 g hg
  obtain ⟨g', ⟨hg', hm⟩, -⟩ := hR.2 (κ * κ₁) (mul_mem hκ hκ₁)
  refine ⟨g', hg', ?_⟩
  have : g'⁻¹ * (κ * g) = (g'⁻¹ * (κ * κ₁ * g₀)) * κ₁' := by rw [e]; group
  rw [this]; exact mul_mem hm hκ₁'

theorem sum_kappa_mul {γ : Fin N → ℂ} {ψ : GL (Fin N) k → ℂ} (h : IsBorelSph k γ ψ)
    {g₀ : GL (Fin N) k} {R : Finset (GL (Fin N) k)} (hR : IsRepsK g₀ R)
    {κ : GL (Fin N) k} (hκ : κ ∈ KO k (Fin N)) : ∑ g ∈ R, ψ (κ * g) = ∑ g ∈ R, ψ g := by
  classical
  choose f hf hfK using fun g (hg : g ∈ R) => exists_isRepsK hR hκ hg
  refine Finset.sum_bij f hf (fun a ha b hb e => ?_) (fun c hc => ?_) (fun a ha => ?_)
  · have h1 := hfK a ha
    have h2 := hfK b hb
    rw [e] at h1
    apply eq_of_isRepsK hR ha hb
    have : a⁻¹ * b = ((f b hb)⁻¹ * (κ * a))⁻¹ * ((f b hb)⁻¹ * (κ * b)) := by group
    rw [this]; exact mul_mem (inv_mem h1) h2
  · obtain ⟨a, ha, hm⟩ := exists_isRepsK hR (inv_mem hκ) hc
    refine ⟨a, ha, eq_of_isRepsK hR (hf a ha) hc ?_⟩
    have : (f a ha)⁻¹ * c = ((f a ha)⁻¹ * (κ * a)) * (a⁻¹ * (κ⁻¹ * c)) := by group
    rw [this]; exact mul_mem (hfK a ha) hm
  · have : κ * a = f a ha * ((f a ha)⁻¹ * (κ * a)) := by group
    rw [this, h.1 _ _ (hfK a ha)]

end GlobalTheory.ZonalSum


open GlobalTheory.ZonalSum in
theorem GlobalTheory.ZonalSum.sum_mul_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → (∀ i, γ i ≠ 0) → ∀ (g₀ : GL (Fin N) k) (R : Finset (GL (Fin N) k)), IsRepsK g₀ R → ∀ m : GL (Fin N) k, ∑ g ∈ R, ψ (m * g) = ψ m * ∑ g ∈ R, ψ g := by
  intro k _ _ _ _ N γ ψ h hγ g₀ R hR m
  obtain ⟨b, hb, κ, hκ, rfl⟩ := iwasawa_blockTriangular k (Fin N) Fin.val m
  have hb' : b ∈ borel k (Fin N) := (mem_borel _).2 hb
  have e : ∀ g, ψ (b * κ * g) = ψ b * ψ (κ * g) := fun g => by
    rw [mul_assoc]; exact borelSph_mul_left h hγ hb' _
  simp only [e]
  rw [← Finset.mul_sum, sum_kappa_mul h hR hκ, h.1 _ _ hκ]

end
end

