module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumCharDetFixHyperplaneEqZero
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory


open Matrix in
theorem finsum_char_det_fix_hyperplane_eq_zero :
    ∀ (k : Type) [Field k] [Finite k] (r : ℕ) (ξ : kˣ →* ℂˣ), ξ ≠ 1 → ∀ a : Fin r → k, a ≠ 0 →
      ∑ᶠ g ∈ {g : GL (Fin r) k | ∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) k).mulVec v = v},
        ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) = 0 := by
  intro k _ _ r ξ hξ a ha
  set S : Set (GL (Fin r) k) :=
    {g : GL (Fin r) k | ∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) k).mulVec v = v} with hS
  obtain ⟨c, hc⟩ : ∃ c : kˣ, ξ c ≠ 1 := by
    by_contra h
    push_neg at h
    exact hξ (MonoidHom.ext h)
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
    by_contra h
    push_neg at h
    exact ha (funext h)
  set v₀ : Fin r → k := Pi.single i (a i)⁻¹ with hv₀
  have hav₀ : a ⬝ᵥ v₀ = 1 := by
    rw [hv₀, dotProduct_single, mul_inv_cancel₀ hi]
  set u : Fin r → k := ((c : k) - 1) • v₀ with hu
  set M : Matrix (Fin r) (Fin r) k :=
    1 + replicateCol (Fin 1) u * replicateRow (Fin 1) a with hM
  have hdet : M.det = (c : k) := by
    have h1 := det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) u a
    rw [hM]
    refine h1.trans ?_
    rw [hu, dotProduct_smul, hav₀, smul_eq_mul, mul_one]
    ring
  have hMfix : ∀ v, a ⬝ᵥ v = 0 → M *ᵥ v = v := by
    intro v hv
    rw [hM, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
    have : replicateRow (Fin 1) a *ᵥ v = 0 := by
      ext j
      simp [Matrix.mulVec, replicateRow, hv]
    rw [this, Matrix.mulVec_zero, add_zero]
  let h₀ : GL (Fin r) k := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact c.ne_zero)
  have hh₀ : (h₀ : Matrix (Fin r) (Fin r) k) = M := rfl
  have hdeth₀ : Matrix.GeneralLinearGroup.det h₀ = c := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply, hh₀, hdet]
  have hh₀S : h₀ ∈ S := fun v hv => by rw [hh₀]; exact hMfix v hv
  have hmulS : ∀ g ∈ S, h₀ * g ∈ S := by
    intro g hg v hv
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg v hv, hh₀S v hv]
  have hinvS : ∀ g ∈ S, h₀⁻¹ * g ∈ S := by
    intro g hg v hv
    have h1 : (h₀ : Matrix (Fin r) (Fin r) k) *ᵥ v = v := hh₀S v hv
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg v hv]
    conv_lhs => rw [← h1]
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hbij : Set.BijOn (fun g => h₀ * g) S S := by
    refine ⟨fun g hg => hmulS g hg, fun x _ y _ hxy => mul_left_cancel hxy, ?_⟩
    intro g hg
    exact ⟨h₀⁻¹ * g, hinvS g hg, by simp⟩
  set F : GL (Fin r) k → ℂ := fun g => ((ξ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) with hF
  have hFmul : ∀ g, F (h₀ * g) = ((ξ c : ℂˣ) : ℂ) * F g := by
    intro g
    simp [hF, map_mul, hdeth₀]
  have key : ∑ᶠ g ∈ S, F (h₀ * g) = ∑ᶠ g ∈ S, F g :=
    finsum_mem_eq_of_bijOn (fun g => h₀ * g) hbij (fun x _ => rfl)
  simp_rw [hFmul] at key
  rw [← mul_finsum_mem] at key
  have hc' : ((ξ c : ℂˣ) : ℂ) ≠ 1 := by
    intro h
    exact hc (Units.ext h)
  have : (((ξ c : ℂˣ) : ℂ) - 1) * ∑ᶠ g ∈ S, F g = 0 := by
    rw [sub_mul, key, one_mul, sub_self]
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hc'
  · exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumOrbitsCountingPrincipleFiniteFibres
section
open Polynomial

namespace GlobalTheory.OrbitCounting

theorem stabilizer_smul_eq {G X : Type} [CommGroup G] [MulAction G X] (g : G) (x : X) :
    MulAction.stabilizer G (g • x) = MulAction.stabilizer G x := by
  ext h
  simp only [MulAction.mem_stabilizer_iff]
  rw [← mul_smul, mul_comm, mul_smul, smul_left_cancel_iff]

theorem ncard_fibre_inter_orbit {G X Y : Type} [CommGroup G] [MulAction G X] [MulAction G Y]
    (π : X → Y) (hπ : ∀ (g : G) (x : X), π (g • x) = g • π x) (x0 : X) :
    {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0}.ncard =
      (MulAction.stabilizer G x0).relIndex (MulAction.stabilizer G (π x0)) := by
  have hset : {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0} =
      MulAction.orbit (MulAction.stabilizer G (π x0)) x0 := by
    ext x; constructor
    · rintro ⟨hx, g, rfl⟩
      refine ⟨⟨g, ?_⟩, rfl⟩
      rw [MulAction.mem_stabilizer_iff, ← hπ]; exact hx
    · rintro ⟨⟨g, hg⟩, rfl⟩
      refine ⟨?_, ⟨g, rfl⟩⟩
      show π (g • x0) = π x0
      rw [hπ]; exact hg
  rw [hset, Subgroup.relIndex, ← MulAction.index_stabilizer]
  congr 1

theorem counting_principle : ∀ (G X Y : Type) [CommGroup G] [MulAction G X] [MulAction G Y] (Gc : Subgroup G) (π : X → Y), (∀ (g : G) (x : X), π (g • x) = g • π x) → (∀ y, (π ⁻¹' {y}).Finite) → (∀ y : Y, MulAction.stabilizer G y ≤ Gc ∧ (MulAction.stabilizer G y).relIndex Gc ≠ 0) → Finite (MulAction.orbitRel.Quotient G Y) → ∀ w : Y → ℚ, (∀ (g : G) (y : Y), w (g • y) = w y) → ∑ᶠ o : MulAction.orbitRel.Quotient G X, w (π (Quotient.out o)) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) = ∑ᶠ o : MulAction.orbitRel.Quotient G Y, w (Quotient.out o) * ((π ⁻¹' {(Quotient.out o)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out o)).relIndex Gc : ℚ) := by
  intro G X Y _ _ _ Gc π hπ hfin hstab hY w hw
  classical
  have hmem : ∀ a b : X, a ∈ MulAction.orbit G b → π a ∈ MulAction.orbit G (π b) := by
    rintro a b ⟨g, rfl⟩; exact ⟨g, (hπ g b).symm⟩
  let q : MulAction.orbitRel.Quotient G X → MulAction.orbitRel.Quotient G Y :=
    Quotient.map π (fun a b h => MulAction.orbitRel_apply.2 (hmem a b (MulAction.orbitRel_apply.1 h)))
  have hq : ∀ x : X, q (Quotient.mk _ x) = Quotient.mk _ (π x) := fun x => rfl

  have hrep : ∀ (oX : MulAction.orbitRel.Quotient G X) (y : Y), q oX = Quotient.mk _ y →
      ∃ x0, π x0 = y ∧ Quotient.mk _ x0 = oX := by
    intro oX y h
    have h1 : q oX = Quotient.mk _ (π (Quotient.out oX)) := by
      rw [← hq, Quotient.out_eq]
    rw [h1] at h
    have h2 : y ∈ MulAction.orbit G (π (Quotient.out oX)) :=
      MulAction.orbitRel_apply.1 (Quotient.exact h.symm)
    obtain ⟨g, hg⟩ := h2
    refine ⟨g • Quotient.out oX, by rw [hπ]; exact hg, ?_⟩
    rw [← Quotient.out_eq oX]
    exact Quotient.sound (MulAction.orbitRel_apply.2 ⟨g, by rw [Quotient.out_eq]⟩)

  let F : X → ℚ := fun x => w (π x) * ((MulAction.stabilizer G x).relIndex Gc : ℚ)
  let H : Y → ℚ := fun y => w y * ((π ⁻¹' {y}).ncard : ℚ) * ((MulAction.stabilizer G y).relIndex Gc : ℚ)
  have hF : ∀ x x' : X, x' ∈ MulAction.orbit G x → F x' = F x := by
    rintro x x' ⟨g, rfl⟩
    simp only [F, hπ, hw, stabilizer_smul_eq]

  haveI : ∀ oY : MulAction.orbitRel.Quotient G Y, Finite ↥(π ⁻¹' {Quotient.out oY}) :=
    fun oY => (hfin _).to_subtype
  haveI hXf : Finite (MulAction.orbitRel.Quotient G X) := by
    refine Finite.of_surjective
      (fun p : (Σ oY : MulAction.orbitRel.Quotient G Y, ↥(π ⁻¹' {Quotient.out oY})) =>
        (Quotient.mk _ (p.2 : X) : MulAction.orbitRel.Quotient G X)) ?_
    intro oX
    obtain ⟨x0, hx0, hx0'⟩ := hrep oX (Quotient.out (q oX)) (Quotient.out_eq _).symm
    exact ⟨⟨q oX, ⟨x0, hx0⟩⟩, hx0'⟩
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient G X)
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient G Y)
  have hL : ∀ oX : MulAction.orbitRel.Quotient G X,
      w (π (Quotient.out oX)) * ((MulAction.stabilizer G (Quotient.out oX)).relIndex Gc : ℚ) = F (Quotient.out oX) := fun _ => rfl
  have hR : ∀ oY : MulAction.orbitRel.Quotient G Y,
      w (Quotient.out oY) * ((π ⁻¹' {(Quotient.out oY)}).ncard : ℚ) * ((MulAction.stabilizer G (Quotient.out oY)).relIndex Gc : ℚ) = H (Quotient.out oY) := fun _ => rfl
  simp only [hL, hR]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_fiberwise Finset.univ q]
  refine Finset.sum_congr rfl (fun oY _ => ?_)
  set y := Quotient.out oY with hy
  have hyo : Quotient.mk _ y = oY := Quotient.out_eq oY
  set S := (hfin y).toFinset with hS
  have hcard : (π ⁻¹' {y}).ncard = S.card := Set.ncard_eq_toFinset_card _ (hfin y)
  have hmaps : (S : Set X).MapsTo (fun x => (Quotient.mk _ x : MulAction.orbitRel.Quotient G X))
      (Finset.univ.filter (fun oX => q oX = oY) : Finset _) := by
    intro x hx
    simp only [hS, Set.Finite.coe_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp [hq, hx, hyo]
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  show _ = w y * ((π ⁻¹' {y}).ncard : ℚ) * ((MulAction.stabilizer G y).relIndex Gc : ℚ)
  rw [hcard, hsum]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun oX hoX => ?_)
  have hqo : q oX = Quotient.mk _ y := by
    rw [hyo]; simpa using hoX
  obtain ⟨x0, hx0, hx0'⟩ := hrep oX y hqo
  have hout : Quotient.out oX ∈ MulAction.orbit G x0 := by
    apply MulAction.orbitRel_apply.1
    apply Quotient.exact
    rw [Quotient.out_eq, hx0']
  rw [hF x0 _ hout]
  have hfilt : ((S.filter (fun x => (Quotient.mk _ x : MulAction.orbitRel.Quotient G X) = oX) : Finset X) : Set X)
      = {x | π x = π x0 ∧ x ∈ MulAction.orbit G x0} := by
    ext x
    simp only [hS, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_preimage,
      Set.mem_singleton_iff, Set.mem_setOf_eq, hx0]
    rw [← hx0']
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, MulAction.orbitRel_apply.1 (Quotient.exact h2)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, Quotient.sound (MulAction.orbitRel_apply.2 h2)⟩
  rw [← Set.ncard_coe_finset, hfilt, ncard_fibre_inter_orbit π hπ x0]
  have hle1 : MulAction.stabilizer G x0 ≤ MulAction.stabilizer G (π x0) := by
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    rw [← hπ, hg]
  rw [hx0] at hle1
  have hle2 : MulAction.stabilizer G y ≤ Gc := (hstab y).1
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle1 hle2
  simp only [F, hx0]
  rw [← hmul]
  push_cast
  ring

end GlobalTheory.OrbitCounting
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FractionalIdealExistsIntNotMemOfCountEqZero
section
open IsDedekindDomain

namespace GlobalTheory

theorem fractionalIdeal_exists_int_not_mem_of_count_eq_zero
    {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (I : FractionalIdeal (nonZeroDivisors R) K) :
    I ≠ 0 → FractionalIdeal.count K v I = 0 → ∃ s : R, s ∉ v.asIdeal ∧ algebraMap R K s ∈ I := by
  intro hI hc
  classical
  obtain ⟨a, J, ha, haJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ : J ≠ 0 := by
    rintro rfl
    apply hI
    rw [haJ]
    simp
  have hv : Irreducible (Associates.mk v.asIdeal) := v.associates_irreducible
  rw [FractionalIdeal.count_well_defined K v hI haJ, sub_eq_zero, Nat.cast_inj] at hc
  set n := (Associates.mk v.asIdeal).count (Associates.mk J).factors with hn
  have hJne : Associates.mk J ≠ 0 := Associates.mk_ne_zero.mpr hJ
  have haspan : Ideal.span {a} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ha
  have haNe : Associates.mk (Ideal.span {a}) ≠ 0 := Associates.mk_ne_zero.mpr haspan
  have hdJ : v.asIdeal ^ n ∣ J := by
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
    exact (Associates.prime_pow_dvd_iff_le hJne hv).mpr le_rfl
  have hda : v.asIdeal ^ n ∣ Ideal.span {a} := by
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
    exact (Associates.prime_pow_dvd_iff_le haNe hv).mpr hc.le
  obtain ⟨J1, hJ1⟩ := hdJ
  have hnot : ¬ v.asIdeal ∣ J1 := by
    intro h
    have h2 : v.asIdeal ^ (n + 1) ∣ J := by
      rw [hJ1, pow_succ]
      exact mul_dvd_mul_left _ h
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow,
      Associates.prime_pow_dvd_iff_le hJne hv] at h2
    omega
  rw [Ideal.dvd_iff_le, SetLike.not_le_iff_exists] at hnot
  obtain ⟨s, hsJ1, hsv⟩ := hnot
  refine ⟨s, hsv, ?_⟩
  have hsa : s * a ∈ J := by
    rw [hJ1, mul_comm s a]
    exact Ideal.mul_mem_mul (Ideal.dvd_iff_le.mp hda (Ideal.mem_span_singleton_self a)) hsJ1
  rw [haJ, FractionalIdeal.mem_singleton_mul]
  refine ⟨algebraMap R K (s * a), FractionalIdeal.mem_coeIdeal_of_mem _ hsa, ?_⟩
  have ha' : algebraMap R K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha
  rw [map_mul]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameTranslateLatticeCosetSubset
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
namespace GlobalTheory.ParahoricTranslate

theorem isUnit_det_one_add_nonunit_smul {O : Type} [CommRing O] [IsLocalRing O] {r : ℕ} (ϖ : O)
    (hϖ : ¬ IsUnit ϖ) (Z : Matrix (Fin r) (Fin r) O) :
    IsUnit (1 + ϖ • Z).det := by
  rw [← IsLocalRing.notMem_maximalIdeal]
  intro h
  set f := Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)
  have h0 : f (1 + ϖ • Z).det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
  have hf : f ϖ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hϖ))
  have h1 : f.mapMatrix (1 + ϖ • Z) = 1 := by
    rw [map_add (f := _), map_one]
    ext i j
    simp [hf]
  rw [RingHom.map_det, h1, Matrix.det_one] at h0
  exact one_ne_zero h0

theorem toRows_left_mul_matrix_eq {K : Type} [CommRing K] {r t : ℕ}
    (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : Matrix (Fin r) (Fin r) K) :
    Matrix.toRows₁ (x * g) = Matrix.toRows₁ x * g := by
  ext i j; simp [Matrix.toRows₁, Matrix.mul_apply]

theorem translate_lattice_coset_subset : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g g' : GL (Fin r) K) (z z' : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K) → x * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z').map (algebraMap O K) → ∀ (y : Matrix (Fin r ⊕ Fin t) (Fin r) K) (w : Matrix (Fin r ⊕ Fin t) (Fin r) O), y * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w).map (algebraMap O K) → ∃ w' : Matrix (Fin r ⊕ Fin t) (Fin r) O, y * (g' : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • w').map (algebraMap O K) := by
  intro O K _ _ _ _ _ _ _ r t ϖ hirr x g g' z z' hx hx' y w hy
  set φ := algebraMap O K
  set e := Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)
  set Z := Matrix.toRows₁ z
  set Z' := Matrix.toRows₁ z'
  set P : Matrix (Fin r) (Fin r) O := 1 + ϖ • Z
  set P' : Matrix (Fin r) (Fin r) O := 1 + ϖ • Z'
  set A := Matrix.toRows₁ x
  have hP : IsUnit P.det := isUnit_det_one_add_nonunit_smul ϖ hirr.not_isUnit Z
  have hA : A * (g : Matrix (Fin r) (Fin r) K) = φ.mapMatrix P := by
    have := congrArg Matrix.toRows₁ hx
    rw [toRows_left_mul_matrix_eq] at this
    rw [this, RingHom.mapMatrix_apply]
    show (Matrix.toRows₁ (e + ϖ • z)).map φ = (1 + ϖ • Z).map φ
    congr 1
  have hA' : A * (g' : Matrix (Fin r) (Fin r) K) = φ.mapMatrix P' := by
    have := congrArg Matrix.toRows₁ hx'
    rw [toRows_left_mul_matrix_eq] at this
    rw [this, RingHom.mapMatrix_apply]
    show (Matrix.toRows₁ (e + ϖ • z')).map φ = (1 + ϖ • Z').map φ
    congr 1
  have hPK : IsUnit (φ.mapMatrix P).det := by
    rw [← RingHom.map_det]; exact hP.map φ
  have hAu : IsUnit A.det := by
    rw [← hA, Matrix.det_mul] at hPK
    exact isUnit_of_mul_isUnit_left hPK
  set c : Matrix (Fin r) (Fin r) O := P⁻¹ * P'
  have hgc : (g' : Matrix (Fin r) (Fin r) K) = (g : Matrix (Fin r) (Fin r) K) * φ.mapMatrix c := by
    have h2 : A * (g' : Matrix (Fin r) (Fin r) K) = A * ((g : Matrix (Fin r) (Fin r) K) * φ.mapMatrix c) := by
      rw [hA', ← Matrix.mul_assoc, hA, map_mul, ← Matrix.mul_assoc, ← map_mul,
        Matrix.mul_nonsing_inv _ hP, map_one, Matrix.one_mul]
    have h3 := congrArg (fun M => A⁻¹ * M) h2
    simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hAu] using h3
  refine ⟨Matrix.fromRows (P⁻¹ * (Z' - Z)) (0 : Matrix (Fin t) (Fin r) O) + w * c, ?_⟩
  have hc : c = 1 + ϖ • (P⁻¹ * (Z' - Z)) := by
    have : P' = P + ϖ • (Z' - Z) := by
      simp only [P, P', smul_sub]; abel
    simp only [c, this, Matrix.mul_add, Matrix.mul_smul, Matrix.nonsing_inv_mul _ hP]
  have key : (e + ϖ • w) * c = e + ϖ • (Matrix.fromRows (P⁻¹ * (Z' - Z)) (0 : Matrix (Fin t) (Fin r) O) + w * c) := by
    rw [Matrix.add_mul, Matrix.smul_mul]
    have he : e * c = Matrix.fromRows c (0 : Matrix (Fin t) (Fin r) O) := by
      simp [e, Matrix.fromRows_mul]
    rw [he]
    nth_rewrite 1 [hc]
    ext (i | i) j <;> simp [e, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr, smul_add, add_assoc]
  rw [hgc, ← Matrix.mul_assoc, hy, RingHom.mapMatrix_apply, ← Matrix.map_mul, key]

end GlobalTheory.ParahoricTranslate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FreeModuleAdicCompleteSeparated
section
namespace GlobalTheory

theorem freeModule_adicComplete_separated : ∀ {R : Type} [CommRing R] (ϖ : R), (∀ x : ℕ → R, ∃ a : R, ∀ n : ℕ, ∃ b : R, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) → (∀ a : R, (∀ n : ℕ, ∃ b : R, a = ϖ ^ n * b) → a = 0) → ∀ (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M], (∀ x : ℕ → M, ∃ y : M, ∀ n : ℕ, ∃ z : M, y - ∑ j ∈ Finset.range n, ϖ ^ j • x j = ϖ ^ n • z) ∧ (∀ m : M, (∀ n : ℕ, ∃ z : M, m = ϖ ^ n • z) → m = 0) := by
  intro R _ ϖ hc hs M _ _ _ _
  classical
  let b := Module.Free.chooseBasis R M
  haveI : Fintype (Module.Free.ChooseBasisIndex R M) := Module.Free.ChooseBasisIndex.fintype R M
  constructor
  · intro x
    choose a ha using fun i => hc (fun j => b.equivFun (x j) i)
    refine ⟨b.equivFun.symm a, fun n => ?_⟩
    choose c hc' using fun i => ha i n
    refine ⟨b.equivFun.symm c, ?_⟩
    apply b.equivFun.injective
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smul, LinearEquiv.apply_symm_apply, Pi.sub_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact hc' i
  · intro m hm
    apply b.equivFun.injective
    funext i
    show b.equivFun m i = b.equivFun 0 i
    rw [map_zero]
    show b.equivFun m i = 0
    apply hs
    intro n
    obtain ⟨z, hz⟩ := hm n
    refine ⟨b.equivFun z i, ?_⟩
    rw [hz, map_smul]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixComatrixDivisible
section
open Matrix

namespace GlobalTheory

theorem frobenius_matrix_comatrix_divisible {R : Type} [CommRing R] [IsDomain R] (d N N₀ q : ℕ) (p : Fin d → ℕ) (ξ : R)
    (A A' B B' c c' V₀ V₀' : Matrix (Fin d) (Fin d) R) (hξ : ξ ≠ 0) (hB : B * B' = 1) (hc : c * c' = 1)
    (hV : V₀ * V₀' = 1) (hA : A * A' = ξ ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) R))
    (hid : ξ ^ q • (A * B * c) = ξ ^ N • (V₀ * Matrix.diagonal (fun j => ξ ^ p j)))
    (hN : N₀ ≤ N) (hp : ∀ i, |(p i : ℤ) - q| ≤ N₀) :
    (∀ i j, ξ ^ (N - N₀) ∣ A i j) ∧ ∀ i j, ξ ^ (N - N₀) ∣ A' i j := by
  have hp1 : ∀ k, q ≤ p k + N₀ := fun k => by
    have := (abs_le.mp (hp k)).1; omega
  have hp2 : ∀ k, p k ≤ q + N₀ := fun k => by
    have := (abs_le.mp (hp k)).2; omega
  have hq0 : ξ ^ q ≠ 0 := pow_ne_zero _ hξ
  have cancel : ∀ (s : R), s ≠ 0 → ∀ M M' : Matrix (Fin d) (Fin d) R, s • M = s • M' → M = M' := by
    intro s hs M M' h
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hs this
  have hA1 : ξ ^ q • A = ξ ^ N • (V₀ * Matrix.diagonal (fun j => ξ ^ p j) * (c' * B')) := by
    have : A = A * B * c * (c' * B') := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc (A * B) c c', hc, Matrix.mul_one, Matrix.mul_assoc, hB,
        Matrix.mul_one]
    conv_lhs => rw [this]
    rw [← Matrix.smul_mul, hid, Matrix.smul_mul]
  constructor
  · intro i j
    have e := congrFun (congrFun hA1 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    rw [Matrix.mul_apply] at e
    simp only [Matrix.mul_diagonal] at e
    have hdiv : ξ ^ q * ξ ^ (N - N₀) ∣ ξ ^ q * A i j := by
      rw [e, Finset.mul_sum]
      apply Finset.dvd_sum
      intro k _
      have h1 : ξ ^ q * ξ ^ (N - N₀) ∣ ξ ^ N * ξ ^ p k := by
        rw [← pow_add, ← pow_add]; exact pow_dvd_pow _ (by have := hp1 k; omega)
      exact h1.trans ⟨V₀ i k * (c' * B') k j, by ring⟩
    exact (mul_dvd_mul_iff_left hq0).mp hdiv
  · set D' : Matrix (Fin d) (Fin d) R := Matrix.diagonal (fun k => ξ ^ (N₀ + q - p k)) with hD'
    have hDD : Matrix.diagonal (fun j => ξ ^ p j) * D' = ξ ^ (N₀ + q) • (1 : Matrix (Fin d) (Fin d) R) := by
      rw [hD', Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
        rw [← pow_add]; congr 1; have := hp2 i; omega
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    set Z := B * c * D' * V₀' with hZ
    have hAZ : ξ ^ q • (A * Z) = ξ ^ (N + (N₀ + q)) • (1 : Matrix (Fin d) (Fin d) R) := by
      have : A * Z = A * B * c * D' * V₀' := by simp only [hZ, Matrix.mul_assoc]
      rw [this, Matrix.mul_assoc (A * B * c), ← Matrix.smul_mul, hid, Matrix.smul_mul,
        Matrix.mul_assoc V₀, ← Matrix.mul_assoc _ D', hDD, Matrix.smul_mul, Matrix.one_mul,
        Matrix.mul_smul, hV, smul_smul, ← pow_add]
    have hAZ2 : A * (ξ ^ (N - N₀) • Z) = A * A' := by
      apply cancel _ hq0
      rw [Matrix.mul_smul, smul_comm, hAZ, smul_smul, hA, smul_smul, ← pow_add, ← pow_add]
      congr 2; omega
    have hdetA : A.det ≠ 0 := by
      intro h0
      have := congrArg Matrix.det hA
      rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
      exact pow_ne_zero _ (pow_ne_zero _ hξ) this.symm
    have hA' : A' = ξ ^ (N - N₀) • Z := by
      apply cancel _ hdetA
      rw [← Matrix.one_mul A', ← Matrix.one_mul (ξ ^ (N - N₀) • Z), ← Matrix.smul_mul, ← Matrix.smul_mul,
        ← Matrix.adjugate_mul, Matrix.mul_assoc, Matrix.mul_assoc, hAZ2]
    intro i j
    rw [hA', Matrix.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulDiagOfTriangular
section
namespace GlobalTheory.TriangularDiagonal

theorem mul_diag_of_triangular :
    ∀ {p : ℕ} {κ : Fin p → ℤ}, Function.Injective κ → ∀ {M N : Matrix (Fin p) (Fin p) ℂ},
      (∀ (a b : Fin p), κ a < κ b → M a b = (0 : ℂ)) →
      (∀ (a b : Fin p), κ a < κ b → N a b = (0 : ℂ)) →
      ∀ (i : Fin p), (M * N) i i = M i i * N i i := by
  intro p κ hκ M N hM hN i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i ?_ ?_
  · intro k _ hk
    rcases lt_trichotomy (κ i) (κ k) with h | h | h
    · rw [hM i k h, zero_mul]
    · exact absurd (hκ h).symm hk
    · rw [hN k i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

end GlobalTheory.TriangularDiagonal
end

