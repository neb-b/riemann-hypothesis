module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryActionHermitianInvariantsTransitive
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0094
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantImageOpenClosedLocalSections
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.ImgSec

theorem charpoly_companion_coeff : ∀ (k : Type) [CommRing k] (r : ℕ) (p : Fin r → k) (i : Fin r), (companion p).charpoly.coeff (i : ℕ) = p i := _root_.GlobalTheory.JR.CompanionCharpoly.charpoly_companion_coeff_ring
theorem exists_compact_open_nhd : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (U : Set (Inv r F)) (a₀ : Inv r F), IsOpen U → a₀ ∈ U → ∃ Ω : Set (Inv r F), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ Ω ⊆ U := GlobalTheory.T.borderedMatrixInvariantSpace_exists_compact_open_subset
theorem isCompact_orbit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E) (h : Inv r F → Matrix (Fin r) (Fin r) E), IsCompact Ω → ContinuousOn s Ω → ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det ∧ Bm (s a).toGl = h a) → ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C} := _root_.GlobalTheory.JR.orbit_proper_of_columns
theorem continuousOn_mkX : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Ω : Set (Inv r F)) (h : Inv r F → Matrix (Fin r) (Fin r) E), ContinuousOn h Ω → (∀ a ∈ Ω, IsUnit (h a).det) → ContinuousOn (fun a => GlobalTheory.JR.ImgSec.mkX a (h a)) Ω := GlobalTheory.T.continuousOn_hermitianBlockMatrixOfInvariants

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  [Unram F E] {r : ℕ}

theorem hasInv_mkX {a : Inv r F} {h : Matrix (Fin r) (Fin r) E} (hh : hᴴ * h = (hankel a).map (algebraMap F E))
    (hd : IsUnit h.det) : HasInv (mkX a h) a := by
  unfold HasInv inv
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i
    show ((mkX a h).1.1).charpoly.coeff i = algebraMap F E (a.1 i)
    rw [mkX_fst hh hd]
    let u : (Matrix (Fin r) (Fin r) E)ˣ := Matrix.nonsingInvUnit h hd
    have e : h * (companion a.1).map (algebraMap F E) * h⁻¹ =
        (u : Matrix (Fin r) (Fin r) E) * (companion a.1).map (algebraMap F E) *
          (u : Matrix (Fin r) (Fin r) E)⁻¹ := rfl
    rw [e, Matrix.charpoly_units_conj, Matrix.charpoly_map, Polynomial.coeff_map, charpoly_companion_coeff]
  · funext i; exact mom_mkX hh hd i
  · rfl

end GlobalTheory.JR.ImgSec


open GlobalTheory.JR.ImgSec in
theorem GlobalTheory.JR.image_openClosed_section : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (a₀ : Inv r F), Delta a₀ ≠ 0 → ((¬ ∃ X : Hn r F E, HasInv X a₀) → ∀ᶠ a in 𝓝 a₀, ¬ ∃ X : Hn r F E, HasInv X a) ∧ ((∃ X : Hn r F E, HasInv X a₀) → ∃ (Ω : Set (Inv r F)) (s : Inv r F → Hn r F E), IsCompact Ω ∧ IsOpen Ω ∧ a₀ ∈ Ω ∧ ContinuousOn s Ω ∧ (∀ a ∈ Ω, Delta a ≠ 0 ∧ HasInv (s a) a) ∧ ∀ C : Set (Hn r F E), IsCompact C → IsCompact {p : Matrix.unitaryGroup (Fin r) E × Inv r F | p.2 ∈ Ω ∧ actU p.1 (s p.2) ∈ C}) := by
  intro F E _ _ _ _ _ r a₀ hΔ
  haveI := continuousStar (E := E) F
  obtain ⟨-, -, -, hcrit⟩ := _root_.GlobalTheory.JR.HermInv.herm_invariants F E r
  obtain ⟨Ω₁, κ, hΩ₁, hH₀, hκ, -, hκeq⟩ := _root_.GlobalTheory.symm_congr_local_continuous F E r (hankel a₀) (hankel_isSymm a₀) hΔ
  set φ := algebraMap F E with hφ
  let U : Set (Inv r F) := {a | Delta a ≠ 0} ∩ (fun a => hankel a) ⁻¹' Ω₁
  have hU : IsOpen U := (isOpen_ne_fun continuous_delta continuous_const).inter (hΩ₁.preimage continuous_hankel)
  have ha₀ : a₀ ∈ U := ⟨hΔ, hH₀⟩
  have hK : ∀ a ∈ U, (κ (hankel a))ᵀ * hankel a₀ * κ (hankel a) = hankel a :=
    fun a ha => hκeq _ ha.2 (hankel_isSymm a)
  have hKd : ∀ a ∈ U, IsUnit (κ (hankel a)).det := by
    intro a ha
    refine isUnit_iff_ne_zero.2 fun h0 => ha.1 ?_
    have := congrArg Matrix.det (hK a ha)
    rw [det_mul, det_mul, h0, mul_zero] at this
    exact this.symm
  have hdm : ∀ M : Matrix (Fin r) (Fin r) F, (M.map φ).det = φ M.det := fun M => (RingHom.map_det φ M).symm
  have hKd' : ∀ a ∈ U, IsUnit ((κ (hankel a)).map φ).det := fun a ha => by
    rw [hdm]; exact (hKd a ha).map φ
  have hmapK : ∀ a ∈ U, ((κ (hankel a)).map φ)ᴴ * ((hankel a₀).map φ * (κ (hankel a)).map φ) = (hankel a).map φ := by
    intro a ha
    rw [ImgSec.conjTranspose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.mul_assoc, hK a ha]
  have transport : ∀ a ∈ U, (∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a).map φ) →
      ∃ h : Matrix (Fin r) (Fin r) E, hᴴ * h = (hankel a₀).map φ := by
    rintro a ha ⟨h, hh⟩
    set K' := (κ (hankel a)).map φ
    have hu' : IsUnit K'ᴴ.det := by rw [det_conjTranspose]; exact (hKd' a ha).star
    refine ⟨h * K'⁻¹, ?_⟩
    rw [conjTranspose_mul, conjTranspose_nonsing_inv]
    calc K'ᴴ⁻¹ * hᴴ * (h * K'⁻¹) = K'ᴴ⁻¹ * (hᴴ * h) * K'⁻¹ := by simp only [Matrix.mul_assoc]
      _ = K'ᴴ⁻¹ * (K'ᴴ * ((hankel a₀).map φ * K')) * K'⁻¹ := by rw [hh, ← hmapK a ha]
      _ = (hankel a₀).map φ := by
        rw [nonsing_inv_mul_cancel_left _ _ hu', mul_nonsing_inv_cancel_right _ _ (hKd' a ha)]
  refine ⟨fun hno => ?_, fun hex => ?_⟩
  · filter_upwards [hU.mem_nhds ha₀] with a ha
    rintro ⟨X, hX⟩
    apply hno
    rw [hcrit a₀ hΔ]
    exact transport a ha ((hcrit a ha.1).1 ⟨X, hX⟩)
  · obtain ⟨h₀, hh₀⟩ := (hcrit a₀ hΔ).1 hex
    have hd₀ : IsUnit h₀.det := by
      refine isUnit_iff_ne_zero.2 fun h0 => ?_
      have := congrArg Matrix.det hh₀
      rw [det_mul, h0, mul_zero, hdm] at this
      exact hΔ ((map_eq_zero_iff φ φ.injective).1 this.symm)
    obtain ⟨Ω, hΩc, hΩo, ha₀Ω, hΩU⟩ := exists_compact_open_nhd F E r U a₀ hU ha₀
    let hf : Inv r F → Matrix (Fin r) (Fin r) E := fun a => h₀ * (κ (hankel a)).map φ
    have hhf : ∀ a ∈ U, (hf a)ᴴ * hf a = (hankel a).map φ := by
      intro a ha
      simp only [hf]
      rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc h₀ᴴ, hh₀, hmapK a ha]
    have hdf : ∀ a ∈ U, IsUnit (hf a).det := fun a ha => by
      simp only [hf]; rw [det_mul]; exact hd₀.mul (hKd' a ha)
    have hcf : ContinuousOn hf Ω := by
      have h1 : ContinuousOn (fun a => κ (hankel a)) Ω :=
        hκ.comp continuous_hankel.continuousOn fun a ha => (hΩU ha).2
      exact continuousOn_const.mul ((continuous_id.matrix_map (continuous_algebraMap F E)).comp_continuousOn h1)
    have hcs : ContinuousOn (fun a => mkX a (hf a)) Ω :=
      continuousOn_mkX F E r Ω hf hcf fun a ha => hdf a (hΩU ha)
    refine ⟨Ω, fun a => mkX a (hf a), hΩc, hΩo, ha₀Ω, hcs,
      fun a ha => ⟨(hΩU ha).1, hasInv_mkX (hhf a (hΩU ha)) (hdf a (hΩU ha))⟩, ?_⟩
    intro C hC
    exact isCompact_orbit F E r Ω (fun a => mkX a (hf a)) hf hΩc hcs hcf
      (fun a ha => ⟨hdf a (hΩU ha), bm_mkX (hhf a (hΩU ha)) (hdf a (hΩU ha))⟩) C hC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvolutionIdempotentDecompositionOfSeparableChar
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open Classical

section Generic

variable {R : Type} [CommRing R]

def FieldIdem (f : R) : Prop :=
  IsIdempotentElem f ∧ f ≠ 0 ∧ ∀ y, f * y ≠ 0 → ∃ z, f * y * z = f

theorem FieldIdem.mul_eq_left {u v : R} (hu : FieldIdem u) (hv : IsIdempotentElem v) (h : u * v ≠ 0) :
    u * v = u := by
  obtain ⟨z, hz⟩ := hu.2.2 v h
  calc u * v = (u * v * z) * v := by rw [hz]
    _ = u * v * z * v := rfl
    _ = u * (v * v) * z := by ring
    _ = u := by rw [hv.eq, hz]

theorem FieldIdem.eq_of_mul_ne_zero {u v : R} (hu : FieldIdem u) (hv : FieldIdem v) (h : u * v ≠ 0) :
    u = v := by
  have h1 : u * v = u := hu.mul_eq_left hv.1 h
  have h2 : v * u = v := hv.mul_eq_left hu.1 (by rwa [mul_comm])
  calc u = u * v := h1.symm
    _ = v * u := mul_comm _ _
    _ = v := h2

theorem FieldIdem.map {u : R} (hu : FieldIdem u) (σ : R ≃+* R) : FieldIdem (σ u) := by
  refine ⟨?_, ?_, ?_⟩
  · show σ u * σ u = σ u
    rw [← map_mul, hu.1.eq]
  · intro h0
    exact hu.2.1 (σ.injective (by rw [h0, map_zero]))
  · intro y hy
    have hy' : u * σ.symm y ≠ 0 := by
      intro h0
      apply hy
      have h1 := congrArg σ h0
      rwa [map_mul, RingEquiv.apply_symm_apply, map_zero] at h1
    obtain ⟨z, hz⟩ := hu.2.2 _ hy'
    refine ⟨σ z, ?_⟩
    have h1 := congrArg σ hz
    rwa [map_mul, map_mul, RingEquiv.apply_symm_apply] at h1

theorem exists_fieldIdem_family [IsReduced R] [IsArtinianRing R] :
    ∃ (M : Type) (_ : Fintype M) (f : M → R), CompleteOrthogonalIdempotents f ∧ ∀ m, FieldIdem (f m) := by

  let φ := IsArtinianRing.equivPi R
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  have hc : CompleteOrthogonalIdempotents (fun m : MaximalSpectrum R => φ.symm (Pi.single m 1)) :=
    (CompleteOrthogonalIdempotents.single (fun I : MaximalSpectrum R => R ⧸ I.asIdeal)).map
      φ.symm.toRingEquiv.toRingHom
  refine ⟨MaximalSpectrum R, inferInstance, fun m => φ.symm (Pi.single m 1), hc, fun m => ?_⟩
  refine ⟨hc.idem m, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun x => φ x m) h0
    simp only [AlgEquiv.apply_symm_apply, map_zero, Pi.single_eq_same, Pi.zero_apply] at h1
    exact one_ne_zero h1
  · intro y hy
    have ha : φ y m ≠ 0 := by
      intro h0
      apply hy
      apply φ.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, map_zero]
      funext j
      rw [Pi.mul_apply, Pi.zero_apply]
      by_cases hj : j = m
      · subst hj
        rw [Pi.single_eq_same, one_mul]
        exact h0
      · simp only [Pi.single_eq_of_ne hj, zero_mul]
    obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv ha
    refine ⟨φ.symm (Pi.single m b), ?_⟩
    apply φ.injective
    rw [map_mul, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
    funext j
    rw [Pi.mul_apply, Pi.mul_apply]
    by_cases hj : j = m
    · subst hj
      rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
      exact hb
    · simp only [Pi.single_eq_of_ne hj, zero_mul]

end Generic

theorem exists_isPre (K : UQ) (B : InvAlg K) (hP : B.P.Separable) :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → B.A) (S : Finset ι), IsPre B e S := by
  have := InvAlg.isReduced_of_separable_P K B hP
  have : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  obtain ⟨M, _, f, hf, hF⟩ := exists_fieldIdem_family (R := B.A)

  have hex : ∀ m, ∃ m', B.σ (f m) = f m' := by
    intro m
    by_contra hcon
    push Not at hcon
    have hσ := (hF m).map B.σ
    have hzero : ∀ m', B.σ (f m) * f m' = 0 := fun m' => by
      by_contra h
      exact hcon m' (hσ.eq_of_mul_ne_zero (hF m') h)
    apply hσ.2.1
    calc B.σ (f m) = B.σ (f m) * 1 := (mul_one _).symm
      _ = ∑ m', B.σ (f m) * f m' := by rw [← hf.complete, Finset.mul_sum]
      _ = 0 := Finset.sum_eq_zero (fun m' _ => hzero m')
  choose τ hτ using hex
  have finj : Function.Injective f := by
    intro a b hab
    by_contra h
    apply (hF a).2.1
    calc f a = f a * f a := (hF a).1.eq.symm
      _ = f a * f b := congrArg (f a * ·) hab
      _ = 0 := hf.ortho h
  have hττ : ∀ m, τ (τ m) = m := by
    intro m
    apply finj
    calc f (τ (τ m)) = B.σ (f (τ m)) := (hτ (τ m)).symm
      _ = B.σ (B.σ (f m)) := by rw [hτ m]
      _ = f m := B.σ_σ _

  obtain ⟨rep, rep_mem, rep_tau⟩ : ∃ rep : M → M, (∀ m, rep m = m ∨ rep m = τ m) ∧
      ∀ m, rep (τ m) = rep m := by
    let enc := Fintype.equivFin M
    refine ⟨fun m => if enc m ≤ enc (τ m) then m else τ m, fun m => ?_, fun m => ?_⟩
    · dsimp only
      split_ifs <;> simp
    · dsimp only
      rw [hττ m]
      by_cases h1 : enc m ≤ enc (τ m) <;> by_cases h2 : enc (τ m) ≤ enc m
      · have h3 : m = τ m := enc.injective (le_antisymm h1 h2)
        rw [if_pos h2, if_pos h1]
        exact h3.symm
      · rw [if_neg h2, if_pos h1]
      · rw [if_pos h2, if_neg h1]
      · exact (le_total (enc m) (enc (τ m))).elim (fun h => absurd h h1) (fun h => absurd h h2)
  have rep_rep : ∀ m, rep (rep m) = rep m := by
    intro m
    rcases rep_mem m with h | h
    · rw [h, h]
    · rw [h, rep_tau, h]
  obtain ⟨g, hg⟩ : ∃ g : M → {m : M // rep m = m}, ∀ m, (g m).1 = rep m :=
    ⟨fun m => ⟨rep m, rep_rep m⟩, fun _ => rfl⟩
  have hfib : ∀ (i : {m : M // rep m = m}) (m : M), g m = i ↔ m = i.1 ∨ m = τ i.1 := by
    intro i m
    rw [Subtype.ext_iff, hg]
    constructor
    · intro h
      rcases rep_mem m with h' | h'
      · exact Or.inl (h'.symm.trans h)
      · right
        have h3 : τ m = i.1 := h'.symm.trans h
        calc m = τ (τ m) := (hττ m).symm
          _ = τ i.1 := by rw [h3]
    · rintro (h | h)
      · rw [h]
        exact i.2
      · rw [h, rep_tau]
        exact i.2
  obtain ⟨e, he⟩ : ∃ e : {m : M // rep m = m} → B.A,
      ∀ i, e i = ∑ m ∈ Finset.univ.filter (fun m => g m = i), f m := ⟨_, fun _ => rfl⟩
  have hsum : ∀ i, e i = if τ i.1 = i.1 then f i.1 else f i.1 + f (τ i.1) := by
    intro i
    have hfil : Finset.univ.filter (fun m => g m = i) = {i.1, τ i.1} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact hfib i m
    rw [he, hfil]
    split_ifs with h
    · simp [h]
    · exact Finset.sum_pair (Ne.symm h)
  refine ⟨{m : M // rep m = m}, inferInstance, e, Finset.univ.filter (fun i => τ i.1 = i.1),
    ⟨⟨fun i => ?_, fun i j hij => ?_⟩, ?_⟩, fun i => ?_⟩
  · rw [he]
    exact hf.1.isIdempotentElem_sum
  · show e i * e j = 0
    rw [he, he, Finset.sum_mul]
    apply Finset.sum_eq_zero
    intro a ha
    apply hf.1.mul_sum_of_notMem
    intro ha'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
    exact hij (ha.symm.trans ha')
  · simp_rw [he]
    rw [Finset.sum_fiberwise]
    exact hf.complete
  · refine ⟨f i.1, (hF _).1, (hF _).2.1, (hF _).2.2, fun hi => ?_, fun hi => ?_⟩
    · have hi' : τ i.1 = i.1 := (Finset.mem_filter.mp hi).2
      exact ⟨by rw [hsum i, if_pos hi'], by rw [hτ, hi']⟩
    · have hi' : τ i.1 ≠ i.1 := fun h => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      exact ⟨by rw [hτ]; exact hf.ortho (Ne.symm hi'), by rw [hsum i, if_neg hi', hτ]⟩

theorem isPre_of_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable →
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → B.A) (S : Finset ι), IsPre B e S := fun K B hP => exists_isPre K B hP

end GlobalTheory.UnitLemma.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralIntegersUnramifiedInvolutionExt
section
noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial IsLocalRing

theorem intO_lift_of_val_nonneg (K : UQ) (x : K.E) (h : 0 ≤ val K.O x) : ∃ a : K.O, algebraMap K.O K.E a = x := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  apply IsDiscreteValuationRing.exists_lift_of_le_one
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E x ≠ 0 := by simpa using hx
  unfold val at h
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

theorem intO_val_algebraMap_nonneg (K : UQ) (a : K.O) : 0 ≤ val K.O (algebraMap K.O K.E a) := by
  by_cases ha : a = 0
  · simp [ha, val]
  have h1 := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_le_one (K := K.E) a
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ha
  unfold val
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  omega

theorem intO_val_ne_zero_of_mem (K : UQ) (a : K.O) (ha0 : a ≠ 0) (ha : a ∈ maximalIdeal K.O) :
    val K.O (algebraMap K.O K.E a) ≠ 0 := by
  have h1 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) < 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 ha
  have h0 : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E a) ≠ 0 := by
    simpa using (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 ha0
  unfold val
  rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
  omega

theorem intO : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ y : K'.O,
    @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra (algebraMap K'.O K'.E y) := by
  intro K K' d φ hU hd y
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfr : Module.finrank K.E K'.E = d := hU.2.2.2.2
  haveI : FiniteDimensional K.E K'.E := Module.finite_of_finrank_pos (by omega)
  haveI : Algebra.IsSeparable K.E K'.E := Algebra.IsSeparable.of_integral _ _
  let S := integralClosure K.O K'.E
  haveI : Module.Finite K.O S := IsIntegralClosure.finite K.O K.E K'.E S
  haveI : IsDedekindDomain S := IsIntegralClosure.isDedekindDomain K.O K.E K'.E S
  haveI : IsFractionRing S K'.E := IsIntegralClosure.isFractionRing_of_finite_extension K.O K.E K'.E S
  haveI : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := K.O) S
  have hinj : Function.Injective (algebraMap K.O S) :=
    algebraMap_injective_of_field_isFractionRing K.O S K.E K'.E
  have hnf : ¬ IsField S := fun h =>
    IsDiscreteValuationRing.not_isField K.O (isField_of_isIntegral_of_isField hinj h)
  haveI : IsDiscreteValuationRing S := ((IsDiscreteValuationRing.TFAE S hnf).out 3 1).1
    (inferInstance : IsDedekindDomain S)

  have hv : ∀ a : K.O, 0 ≤ val K'.O (φ (algebraMap K.O K.E a)) := fun a => by
    rw [hU.2.2.1]; exact intO_val_algebraMap_nonneg K a
  choose ψf hψf using fun a : K.O => intO_lift_of_val_nonneg K' _ (hv a)
  have hinj' : Function.Injective (algebraMap K'.O K'.E) := IsFractionRing.injective _ _
  let ψ : K.O →+* K'.O :=
    { toFun := ψf
      map_one' := hinj' (by rw [hψf]; simp)
      map_mul' := fun a b => hinj' (by simp [hψf])
      map_zero' := hinj' (by rw [hψf]; simp)
      map_add' := fun a b => hinj' (by simp [hψf]) }
  have hψ : ∀ a, algebraMap K'.O K'.E (ψ a) = algebraMap K.O K'.E a := fun a => hψf a

  have hS : ∀ t : K'.E, IsIntegral K.O t → ∃ z : K'.O, algebraMap K'.O K'.E z = t := by
    intro t ht
    have : IsIntegral K'.O t :=
      IsIntegral.map_of_comp_eq (T := K'.O) (U := K'.E) ψ (RingHom.id K'.E) (by ext a; exact hψ a) ht
    exact IsIntegrallyClosed.isIntegral_iff.1 this
  set x := algebraMap K'.O K'.E y with hx
  rcases ValuationRing.isInteger_or_isInteger S x with ⟨s, hs⟩ | ⟨s, hs⟩
  · rw [← hs]; exact s.2
  by_cases hx0 : x = 0
  · rw [hx0]; exact isIntegral_zero
  by_cases hsu : IsUnit s
  · have hu1 : ((hsu.unit⁻¹ : Sˣ) : S) * s = 1 := by
      have := hsu.unit.inv_mul; rwa [IsUnit.unit_spec] at this
    have e : algebraMap S K'.E ((hsu.unit⁻¹ : Sˣ) : S) * algebraMap S K'.E s = 1 := by
      rw [← map_mul, hu1, map_one]
    have : x = algebraMap S K'.E ((hsu.unit⁻¹ : Sˣ) : S) := by
      rw [eq_inv_of_mul_eq_one_left e, hs, inv_inv]
    rw [this]; exact ((hsu.unit⁻¹ : Sˣ) : S).2
  exfalso
  have hall : ∀ n : Ideal S, n.IsMaximal → s ∈ n := fun n hn => by
    rw [IsLocalRing.eq_maximalIdeal hn]; exact (mem_maximalIdeal s).2 hsu
  obtain ⟨N, -, hN⟩ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal (R := K.O) S s hall
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hN
  obtain ⟨t, ht⟩ := hN
  obtain ⟨z, hz⟩ := hS _ t.2
  have h1 : algebraMap K'.O K'.E (y ^ N * (ψ π * z)) = 1 := by
    have := congrArg (algebraMap S K'.E) ht
    rw [map_mul, map_pow, hs, ← IsScalarTower.algebraMap_apply] at this
    have h' : (t : K'.E) * algebraMap K.O K'.E π = x⁻¹ ^ N := this
    rw [map_mul, map_pow, map_mul, hψ, hz, ← hx, mul_comm (algebraMap K.O K'.E π), h', ← mul_pow,
      mul_inv_cancel₀ hx0, one_pow]
  have hu : IsUnit (ψ π) := by
    have : y ^ N * (ψ π * z) = 1 := hinj' (by rw [h1, map_one])
    exact IsUnit.of_mul_eq_one (z * y ^ N) (by rw [← this]; ring)
  have h2 := GlobalTheory.UnitLemma.Orbit.val_unit (K := K') _ hu
  rw [hψ] at h2
  have h3 := hU.2.2.1 (algebraMap K.O K.E π)
  change val K'.O (φ (algebraMap K.O K.E π)) = 0 at h2
  rw [h3] at h2
  exact intO_val_ne_zero_of_mem K π hπ.ne_zero hπ.not_isUnit h2

end GlobalTheory.UnitLemma.Unr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KrasnerLemmaDecompositionGroupStabilizerVersion
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory

theorem krasner_val_lt_apply_iff {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {σ : G E Ω} (hσ : σ ∈ Dec (F := E) A) (a b : Ω) :
    A.valuation (σ a) < A.valuation (σ b) ↔ A.valuation a < A.valuation b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  · have hb' : A.valuation b ≠ 0 := by simpa using hb
    have hsb : σ b ≠ 0 := (map_ne_zero_iff _ σ.injective).mpr hb
    have hsb' : A.valuation (σ b) ≠ 0 := by simpa using hsb
    rw [← div_lt_one₀ (zero_lt_iff.mpr hb'), ← div_lt_one₀ (zero_lt_iff.mpr hsb'),
      ← map_div₀, ← map_div₀, ← map_div₀, valuation_apply_lt_one_iff hσ]

theorem krasner_stabiliser (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (β β' : Ω)
    (h : ∀ d ∈ Dec (F := E) A, d β ≠ β → A.valuation (β' - β) < A.valuation (d β - β)) :
    ∀ σ ∈ Dec (F := E) A, σ β' = β' → σ β = β := by
  intro σ hσ hfix
  by_contra hne
  have hσi : σ⁻¹ ∈ Dec (F := E) A := (Dec (F := E) A).inv_mem hσ
  have hne' : (σ⁻¹ : G E Ω) β ≠ β := by
    intro he
    apply hne
    conv_lhs => rw [← he]
    exact mul_inv_apply β
  have h1 := h σ hσ hne
  have h2 := h σ⁻¹ hσi hne'
  rw [← krasner_val_lt_apply_iff hσ, map_sub σ, map_sub σ, mul_inv_apply, hfix] at h2
  have e : β - σ β = (β - β') + (β' - σ β) := by ring
  have h3 : A.valuation (β - σ β) = A.valuation (σ β - β) := Valuation.map_sub_swap _ _ _
  have h4 : A.valuation (β - β') = A.valuation (β' - β) := Valuation.map_sub_swap _ _ _
  have key : A.valuation (β - σ β) < A.valuation (β - σ β) := by
    conv_lhs => rw [e]
    refine Valuation.map_add_lt _ ?_ h2
    rw [h4, h3]; exact h1
  exact lt_irrefl _ key

end GlobalTheory
end

