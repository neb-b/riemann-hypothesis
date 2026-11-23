module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemRegAtOfCodimOne
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_point_of_prime {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (h : IsCptGen ξ) (p : Cpt ξ) (P : Ideal (regAt ξ p)) (hP : P.IsPrime) :
    ∃ q : Cpt ξ, q.1 ⤳ p.1 ∧ ringKrullDim (X.presheaf.stalk q.1) = (P.height : WithBot ℕ∞) ∧
      ∀ a ∈ regAt ξ q, ∃ s t : regAt ξ p, s ∉ P ∧ a * s = t := by
  obtain ⟨U, hU, hp, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := p.1) (U := ⊤) trivial
  have hg : genPt ξ ∈ U := p.2.mem_open U.2 hp
  let e := RegAtRing.stalkEquiv h p
  let P' : Ideal (X.presheaf.stalk p.1) := P.comap (e : X.presheaf.stalk p.1 →+* regAt ξ p)
  have hP' : P'.IsPrime := Ideal.comap_isPrime _ _
  letI algP := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨p.1, hp⟩ : U)
  have localization₂ := hU.isLocalization_stalk ⟨p.1, hp⟩
  let 𝔮 : Ideal Γ(X, U) := P'.comap (algebraMap Γ(X, U) (X.presheaf.stalk p.1))
  have h𝔮 : 𝔮.IsPrime := Ideal.comap_isPrime _ _
  let y : PrimeSpectrum Γ(X, U) := ⟨𝔮, h𝔮⟩
  have hyU : hU.fromSpec y ∈ U := by
    have : hU.fromSpec y ∈ Set.range hU.fromSpec := ⟨y, rfl⟩
    rwa [hU.range_fromSpec] at this

  have hsp : hU.fromSpec y ⤳ p.1 := by
    have hle : y ≤ hU.primeIdealOf ⟨p.1, hp⟩ := by
      change 𝔮 ≤ (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal
      rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk p.1)
        (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal]
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hP'.ne_top)
    have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf] at this

  have hgy : genPt ξ ⤳ hU.fromSpec y := by
    have hle : hU.primeIdealOf ⟨genPt ξ, hg⟩ ≤ y := by
      change (hU.primeIdealOf ⟨genPt ξ, hg⟩).asIdeal ≤ 𝔮
      intro r hr
      letI algG := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨genPt ξ, hg⟩ : U)
      have locG := hU.isLocalization_stalk ⟨genPt ξ, hg⟩
      have hnu : ¬ IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk (genPt ξ)) r) := by
        rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk (genPt ξ))
          (hU.primeIdealOf ⟨genPt ξ, hg⟩).asIdeal] at hr
        exact (IsLocalRing.mem_maximalIdeal _).1 hr
      have hz : (Scheme.stalkClosedPointTo ξ).hom
          (X.presheaf.germ U (genPt ξ) hg r) = 0 := by
        by_contra hne
        obtain ⟨w, hw⟩ := h.bij.2 ((Scheme.stalkClosedPointTo ξ).hom
          (X.presheaf.germ U (genPt ξ) hg r))⁻¹
        apply hnu
        refine IsUnit.of_mul_eq_one w (h.bij.1 ?_)
        erw [map_mul, hw, map_one]
        exact mul_inv_cancel₀ hne
      have hz' : X.presheaf.germ U p.1 hp r = 0 := by
        apply h.inj p
        rw [RegAtRing.genMap_germ p U hp hg, hz, map_zero]
      change algebraMap Γ(X, U) (X.presheaf.stalk p.1) r ∈ P'
      erw [hz']
      exact P'.zero_mem
    have := ((PrimeSpectrum.le_iff_specializes _ _).1 hle).map hU.fromSpec.continuous
    rwa [hU.fromSpec_primeIdealOf] at this
  letI algY : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec y)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hU.fromSpec y, hyU⟩ : U)
  have locY : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) y.asIdeal :=
    hU.isLocalization_stalk' y hyU
  have locY' : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) 𝔮 := locY
  refine ⟨⟨hU.fromSpec y, hgy⟩, hsp, ?_, ?_⟩
  · have h1 : ringKrullDim (X.presheaf.stalk (hU.fromSpec y)) = (𝔮.height : WithBot ℕ∞) :=
      IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮 (X.presheaf.stalk (hU.fromSpec y))
    have h2 : 𝔮.height = P'.height :=
      IsLocalization.height_under (hU.primeIdealOf ⟨p.1, hp⟩).asIdeal.primeCompl P'
    have h3 : P'.height = P.height := RingEquiv.height_comap e P
    change ringKrullDim (X.presheaf.stalk (hU.fromSpec y)) = _
    rw [h1, h2, h3]
  · rintro _ ⟨x, rfl⟩
    obtain ⟨⟨r, t⟩, he⟩ := IsLocalization.surj y.asIdeal.primeCompl
      (S := X.presheaf.stalk (hU.fromSpec y)) x
    have he' : x * (X.presheaf.germ U (hU.fromSpec y) hyU).hom t.1 =
        (X.presheaf.germ U (hU.fromSpec y) hyU).hom r := he
    have hgt := RegAtMono.genMap_germ_eq ξ p ⟨hU.fromSpec y, hgy⟩ hsp U hp hyU
    refine ⟨e ((X.presheaf.germ U p.1 hp).hom t.1), e ((X.presheaf.germ U p.1 hp).hom r), ?_, ?_⟩
    · exact t.2
    · change genMap ξ ⟨hU.fromSpec y, hgy⟩ x * genMap ξ p ((X.presheaf.germ U p.1 hp).hom t.1) =
        genMap ξ p ((X.presheaf.germ U p.1 hp).hom r)
      rw [← hgt, ← hgt, ← map_mul]
      exact congrArg _ he'

theorem mem_regAt_of_codim_one : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    [IsLocallyNoetherian X], IsCptGen ξ → NormalCpt ξ → ∀ (p : Cpt ξ) (a : Ω),
    (∀ q : Cpt ξ, q.1 ⤳ p.1 → ringKrullDim (X.presheaf.stalk q.1) = 1 → a ∈ regAt ξ q) →
    a ∈ regAt ξ p := by
  intro X Ω _ ξ _ h hn p a ha
  obtain ⟨hfr, hno, -⟩ := RegAtRing.regAt_ring X Ω ξ h p
  have : IsFractionRing (regAt ξ p) Ω := hfr
  have : IsNoetherianRing (regAt ξ p) := hno inferInstance
  have : IsIntegrallyClosed (regAt ξ p) := by
    rw [isIntegrallyClosed_iff Ω]
    intro x hx
    exact ⟨⟨x, hn p x hx⟩, rfl⟩
  obtain ⟨t, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := regAt ξ p) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hd1 : algebraMap (regAt ξ p) Ω d ≠ 0 := by
    simpa using hd0
  obtain ⟨b, hb⟩ := mem_range_of_integral_at_heightOne_over (regAt ξ p) Ω d
    (algebraMap (regAt ξ p) Ω t / algebraMap (regAt ξ p) Ω d) hd0
    ⟨1, t, by field_simp⟩
    (fun P hP h1 _ => by
      obtain ⟨q, hq, hdim, hiff⟩ := exists_point_of_prime h p P hP
      have hmem := ha q hq (by rw [hdim]; simp [h1])
      obtain ⟨s, u, hs, hsu⟩ := hiff _ hmem
      exact ⟨u, s, hs, by rw [mul_comm]; exact hsu.symm⟩)
  rw [← hb]
  exact b.2

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MinorRatioRegularOfInvertible
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

theorem mul_inv_apply_eq_det_div {K : Type} [Field K] {n r m : ℕ} (F : Matrix (Fin n) (Fin r) K)
    (J : Fin m → Fin n) (c : Fin m → Fin r) (j : Fin n) (l : Fin m) :
    ((F.submatrix id c) * (F.submatrix J c)⁻¹) j l =
      (F.submatrix (Function.update J l j) c).det / (F.submatrix J c).det := by
  have hrow : F.submatrix (Function.update J l j) c =
      (F.submatrix J c).updateRow l (fun k => F j (c k)) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.updateRow_apply, Function.update_apply]
    split_ifs <;> rfl
  have key : (F.submatrix (Function.update J l j) c).det =
      ∑ k, F j (c k) * (F.submatrix J c).adjugate k l := by
    rw [hrow, ← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
      ← Matrix.adjugate_transpose]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [key, Matrix.mul_apply, Matrix.inv_def, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.submatrix_apply, id_eq, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  ring

theorem split_of_regular_ratios (K : Type) [Field K] (R : Subring K) (n r : ℕ) (A : Matrix (Fin n) (Fin r) K)
    (B : Matrix (Fin r) (Fin n) K) (G : Matrix (Fin r) (Fin r) K) (a : K) (k : Fin r)
    (J : Fin ((k : ℕ) + 1) → Fin n) (hA : ∀ j l, A j l ∈ R) (hB : ∀ l j, B l j ∈ R) (hBA : B * A = 1)
    (_ha : a ≠ 0) (hdet : ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ≠ 0)
    (hR : ∀ l j, ((a • (A * G)).submatrix (Function.update J l j) (Fin.castLE k.2)).det /
      ((a • (A * G)).submatrix J (Fin.castLE k.2)).det ∈ R) :
    ∃ D Ee : Fin ((k : ℕ) + 1) → Fin r → K, (∀ l i, D l i ∈ R) ∧ (∀ l i, Ee l i ∈ R) ∧
      (∀ l l', ∑ i, Ee l i * D l' i = if l = l' then 1 else 0) ∧
      ∀ l, D l ∈ flagStep K (fun c i => G i c) ((k : ℕ) + 1) := by
  have hN' : (a • (A * G)).submatrix id (Fin.castLE k.2) = A * (a • G.submatrix id (Fin.castLE k.2)) := by
    ext i l
    simp only [Matrix.submatrix_apply, Matrix.smul_apply, Matrix.mul_apply, id_eq, smul_eq_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin r) (Fin ((k : ℕ) + 1)) K,
      Q = (a • G.submatrix id (Fin.castLE k.2)) * ((a • (A * G)).submatrix J (Fin.castLE k.2))⁻¹ :=
    ⟨_, rfl⟩
  have hAQ : A * Q = (a • (A * G)).submatrix id (Fin.castLE k.2) *
      ((a • (A * G)).submatrix J (Fin.castLE k.2))⁻¹ := by
    rw [hQ, ← Matrix.mul_assoc, ← hN']
  have hBQ : Q = B * (A * Q) := by rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  have hPR : ∀ j l, (A * Q) j l ∈ R := by
    intro j l
    rw [hAQ, mul_inv_apply_eq_det_div]
    exact hR l j
  refine ⟨fun l i => Q i l, fun l i => A (J l) i, ?_, ?_, ?_, ?_⟩
  · intro l i
    show Q i l ∈ R
    rw [hBQ, Matrix.mul_apply]
    exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hB i j) (hPR j l)
  · intro l i
    exact hA (J l) i
  · intro l l'
    change (A * Q) (J l) l' = _
    rw [hAQ]
    change (((a • (A * G)).submatrix J (Fin.castLE k.2)) *
      ((a • (A * G)).submatrix J (Fin.castLE k.2))⁻¹) l l' = _
    rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_apply]
  · intro l
    have hD : (fun i => Q i l) = ∑ c : Fin ((k : ℕ) + 1),
        (a * ((a • (A * G)).submatrix J (Fin.castLE k.2))⁻¹ c l) • (fun i => G i (Fin.castLE k.2 c)) := by
      funext i
      rw [hQ]
      simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.submatrix_apply, id_eq, smul_eq_mul,
        Finset.sum_apply, Pi.smul_apply]
      exact Finset.sum_congr rfl fun c _ => by ring
    show (fun i => Q i l) ∈ flagStep K (fun c i => G i c) ((k : ℕ) + 1)
    rw [hD]
    refine Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span
      (Set.mem_image_of_mem (fun c i => G i c)
        (show (Fin.castLE k.2 c : Fin r) ∈ {c' : Fin r | (c' : ℕ) < (k : ℕ) + 1} from c.2)))

end GlobalTheory.CompanionTheory.Ar.FlagBun
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

open AlgebraicGeometry CategoryTheory

def locSub {F : Type} [Field F] (R : Subring F) (a : F) : Subring F :=
  Subring.closure ((R : Set F) ∪ {a⁻¹})

theorem le_locSub {F : Type} [Field F] (R : Subring F) (a : F) : R ≤ locSub R a :=
  fun _ h => Subring.subset_closure (Or.inl h)

theorem inv_mem_locSub {F : Type} [Field F] (R : Subring F) (a : F) : a⁻¹ ∈ locSub R a :=
  Subring.subset_closure (Or.inr rfl)

theorem mem_locSub_iff {F : Type} [Field F] {R : Subring F} {a : F} (ha : a ∈ R) (h0 : a ≠ 0) (b : F) :
    b ∈ locSub R a ↔ ∃ k : ℕ, a ^ k * b ∈ R := by
  constructor
  · intro hb
    induction hb using Subring.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact ⟨0, by simpa using hx⟩
      · rw [Set.mem_singleton_iff.1 hx]
        exact ⟨1, by simpa [h0] using R.one_mem⟩
    | zero => exact ⟨0, by simp⟩
    | one => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨k, hk⟩ := hx
      obtain ⟨l, hl⟩ := hy
      refine ⟨k + l, ?_⟩
      have e : a ^ (k + l) * (x + y) = a ^ l * (a ^ k * x) + a ^ k * (a ^ l * y) := by ring
      rw [e]
      exact R.add_mem (R.mul_mem (R.pow_mem ha _) hk) (R.mul_mem (R.pow_mem ha _) hl)
    | neg x _ hx =>
      obtain ⟨k, hk⟩ := hx
      exact ⟨k, by simpa using R.neg_mem hk⟩
    | mul x y _ _ hx hy =>
      obtain ⟨k, hk⟩ := hx
      obtain ⟨l, hl⟩ := hy
      refine ⟨k + l, ?_⟩
      have e : a ^ (k + l) * (x * y) = (a ^ k * x) * (a ^ l * y) := by ring
      rw [e]
      exact R.mul_mem hk hl
  · rintro ⟨k, hk⟩
    have e : b = (a⁻¹) ^ k * (a ^ k * b) := by
      rw [inv_pow, ← _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ h0), _root_.one_mul]
    rw [e]
    exact (locSub R a).mul_mem ((locSub R a).pow_mem (inv_mem_locSub R a) _) (le_locSub R a hk)

structure IsPiece {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens)
    (R : Subring Ω) : Prop where
  affine : IsAffineOpen U
  spec : ∀ q : X, q ∈ U → genPt ξ ⤳ q
  ring : ∀ a : Ω, a ∈ R ↔ ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q

def stepMinor {F : Type} [CommRing F] {n r : ℕ} (A : Matrix (Fin n) (Fin r) F) (i : Fin r)
    (J : Fin ((i : ℕ) + 1) → Fin n) : F :=
  (A.submatrix J (Fin.castLE i.2)).det

variable {Ω : Type} [Field Ω] {S : Type} {r n : S → ℕ}

def flagB (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (s : S) :
    Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) :=
  (M s * T s).map (algebraMap Ω (GenField Ω r)) * genU Ω r s

def ratioRing (R : Subring Ω) (B : ∀ s, Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r))
    (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) : Subring (GenField Ω r) :=
  Subring.closure (((R.map (algebraMap Ω (GenField Ω r)) : Subring _) : Set (GenField Ω r)) ∪
    {a | ∃ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      a = stepMinor (B q.1) q.2 J' / stepMinor (B q.1) q.2 (J q)})

def chartSub {F : Type} [Field F] {κ : Type} (x : κ → F) (c : κ) : Subring F :=
  (Algebra.adjoin ℤ (Set.range fun j => x j / x c)).toSubring

theorem stepMinor_smul {F : Type} [CommRing F] {n r : ℕ} (b : F) (A : Matrix (Fin n) (Fin r) F) (i : Fin r)
    (J : Fin ((i : ℕ) + 1) → Fin n) : stepMinor (b • A) i J = b ^ ((i : ℕ) + 1) * stepMinor A i J := by
  unfold stepMinor
  rw [Matrix.submatrix_smul]
  simp [Matrix.det_smul]

theorem flagMat_eq {E : Type} [AddCommGroup E] [Module Ω E] {m : S → ℕ}
    {φ : ∀ s, Fin (n s) → Module.Dual Ω E} {cc : ∀ s, Fin (r s) → E}
    {M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω} {T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω} {a : Ω}
    (h : ∀ s j l, φ s j (cc s l) = a ^ m s * (M s * T s) j l) (s : S) :
    flagMat φ cc s = (algebraMap Ω (GenField Ω r) a ^ m s) • flagB M T s := by
  unfold flagMat flagB
  rw [← Matrix.smul_mul]
  congr 1
  ext j l
  simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.map_apply, h, map_mul, map_pow, smul_eq_mul]

theorem flagCoord_eq [Fintype S] {E : Type} [AddCommGroup E] [Module Ω E] {κ : Type} (x : κ → Ω) {m : S → ℕ}
    {φ : ∀ s, Fin (n s) → Module.Dual Ω E} {cc : ∀ s, Fin (r s) → E}
    {M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω} {T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω} {a : Ω}
    (h : ∀ s j l, φ s j (cc s l) = a ^ m s * (M s * T s) j l) (k : κ)
    (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) :
    flagCoord κ x φ cc (k, J) = algebraMap Ω (GenField Ω r) (x k) *
      ∏ q : (Σ s, Fin (r s)), ((algebraMap Ω (GenField Ω r) a ^ m q.1) ^ ((q.2 : ℕ) + 1) *
        stepMinor (flagB M T q.1) q.2 (J q)) := by
  unfold flagCoord
  congr 1
  refine Finset.prod_congr rfl fun q _ => ?_
  have := stepMinor_smul (algebraMap Ω (GenField Ω r) a ^ m q.1) (flagB M T q.1) q.2 (J q)
  rw [← this, ← flagMat_eq h q.1]
  rfl

theorem prod_update_div {ι : Type} [Fintype ι] [DecidableEq ι] {β : ι → Type} {F : Type} [Field F]
    (f : ∀ q, β q → F) (J : ∀ q, β q) (h : ∀ q, f q (J q) ≠ 0) (q : ι) (b : β q) :
    (∏ q', f q' (Function.update J q b q')) / (∏ q', f q' (J q')) = f q b / f q (J q) := by
  have h1 : ∏ q', f q' (Function.update J q b q') =
      f q b * ∏ q' ∈ Finset.univ.erase q, f q' (J q') := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q)]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun q' hq' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hq')]
  have h2 : ∏ q', f q' (J q') = f q (J q) * ∏ q' ∈ Finset.univ.erase q, f q' (J q') :=
    (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ q)).symm
  have h3 : ∏ q' ∈ Finset.univ.erase q, f q' (J q') ≠ 0 := Finset.prod_ne_zero_iff.2 fun q' _ => h q'
  rw [h1, h2]
  field_simp [h q, h3]

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularAtBaseChangeStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_at_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ.RegularAt f (F g') → Γ'.RegularAt (fun t => κ (f t)) g' := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF κ hκ f g' ⟨U, hU, s, hs⟩
  refine ⟨F ⁻¹ᵁ U, hU, (F.app U).hom s, fun t h => ?_⟩
  have e := genericPoint_baseChange R T Γ R' Γ' F hF κ hκ t
  let x := (Γ.pt t).left
  let φ := Spec.map (CommRingCat.ofHom κ)
  have hcomp : ⊤ ≤ ((Γ'.pt t).left ≫ F) ⁻¹ᵁ U := h
  have hmap : ⊤ ≤ (φ ≫ x) ⁻¹ᵁ U := e ▸ hcomp
  have hx : ⊤ ≤ x ⁻¹ᵁ U := fun z _ => by
    have hz : z = φ (IsLocalRing.closedPoint (FractionRing R')) :=
      Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    rw [hz]
    exact hmap (by trivial)
  have valAt_eq {y y' : Spec (CommRingCat.of (FractionRing R')) ⟶ Γ.G.left}
      (hy : ⊤ ≤ y ⁻¹ᵁ U) (hy' : ⊤ ≤ y' ⁻¹ᵁ U) (eq : y = y') :
      valAt y U hy s = valAt y' U hy' s := by
    subst y'
    rfl
  have happ : (φ ≫ x).appLE U ⊤ hmap = x.appLE U ⊤ hx ≫ φ.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE φ x U ⊤ ⊤ hx le_top]
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE φ]
    rfl
  calc
    _ = valAt ((Γ'.pt t).left ≫ F) U hcomp s := by
      simp only [valAt, Scheme.Hom.comp_appLE]
      rfl
    _ = valAt (φ ≫ x) U hmap s := valAt_eq hcomp hmap e
    _ = κ (valAt x U hx s) := by
      simp only [valAt, happ]
      exact congrArg (fun z => z.hom ((x.appLE U ⊤ hx).hom s))
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom κ))
    _ = κ (f t) := congrArg κ (hs t hx)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLocalRingFractionField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStalk

theorem exists_germ_frac {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X)
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) {y : X}
    (hs : ξ (IsLocalRing.closedPoint Ω) ⤳ y) (a : Ω) :
    ∃ f g : X.presheaf.stalk y,
      (X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo ξ).hom g ≠ 0 ∧
      a * (X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo ξ).hom g =
        (X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo ξ).hom f := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := y) (U := ⊤) trivial
  have hzU : ξ (IsLocalRing.closedPoint Ω) ∈ U := hs.mem_open U.isOpen hyU
  let z : U := ⟨_, hzU⟩
  letI := X.presheaf.algebra_section_stalk z
  have hl := hU.isLocalization_stalk z
  obtain ⟨s, rfl⟩ := hb.2 a
  obtain ⟨⟨f, g⟩, e⟩ := IsLocalization.surj (S := X.presheaf.stalk z.1)
    (hU.primeIdealOf z).asIdeal.primeCompl s
  have hgerm : ∀ r : Γ(X, U), (X.presheaf.stalkSpecializes hs).hom (X.presheaf.germ U y hyU r) =
      X.presheaf.germ U _ hzU r := fun r =>
    ConcreteCategory.congr_hom (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hyU hs) r
  refine ⟨X.presheaf.germ U y hyU f, X.presheaf.germ U y hyU g.1, ?_, ?_⟩
  · have hu : IsUnit (X.presheaf.germ U _ hzU g.1) :=
      IsLocalization.map_units (X.presheaf.stalk z.1) g
    have := hu.map (Scheme.stalkClosedPointTo ξ).hom
    simpa [hgerm] using this.ne_zero
  · have e' : s * X.presheaf.germ U _ hzU g.1 = X.presheaf.germ U _ hzU f := e
    have := congrArg (Scheme.stalkClosedPointTo ξ).hom e'
    simpa [hgerm] using this

theorem isFractionRing_regAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ →
    ∀ p : Cpt ξ, IsFractionRing (regAt ξ p) Ω := by
  intro X Ω _ ξ h p
  refine IsFractionRing.of_field (regAt ξ p) Ω fun a => ?_
  obtain ⟨f, g, hg, e⟩ := exists_germ_frac ξ h.bij (y := p.1) p.2 a
  refine ⟨⟨genMap ξ p f, f, rfl⟩, ⟨genMap ξ p g, g, rfl⟩, ?_⟩
  exact eq_div_of_mul_eq hg e

end GlobalTheory.CompanionTheory.Ar.LieStalk
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSurjectiveOpenImmersion
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem stalkMap_comp_surjective_of_open_part :
    ∀ (S X₀ Xg X' : Scheme.{0}) (e : Xg ⟶ X₀) (f : X' ⟶ Xg) (W' : X'.Opens)
      (jW : W'.toScheme ⟶ S) (jQ : S ⟶ Xg), IsPreimmersion e → IsOpenImmersion jQ → IsIso jW →
      jW ≫ jQ = W'.ι ≫ f → ∀ x ∈ W', Function.Surjective ((f ≫ e).stalkMap x).hom := by
  intro S X₀ Xg X' e f W' jW jQ he hjQ hjW hcomm x hx
  have := he
  have hO : IsOpenImmersion (W'.ι ≫ f) := by
    rw [← hcomm]
    infer_instance
  obtain ⟨y, rfl⟩ : ∃ y : W'.toScheme, W'.ι y = x := ⟨⟨x, hx⟩, rfl⟩
  have h1 : Function.Surjective ((W'.ι ≫ f).stalkMap y) :=
    Scheme.Hom.stalkMap_surjective (W'.ι ≫ f) y
  have := (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion W'.ι)).2 y
  have hι : Function.Bijective (W'.ι.stalkMap y) := ConcreteCategory.bijective_of_isIso _
  have key : Function.Surjective (f.stalkMap (W'.ι y)) := by
    intro t
    obtain ⟨s, hs⟩ := h1 (W'.ι.stalkMap y t)
    refine ⟨s, hι.1 ?_⟩
    rw [Scheme.Hom.stalkMap_comp] at hs
    exact hs
  rw [Scheme.Hom.stalkMap_comp]
  exact key.comp (Scheme.Hom.stalkMap_surjective e (f (W'.ι y)))

end GlobalTheory.CompanionTheory.Ar.Flat
end

