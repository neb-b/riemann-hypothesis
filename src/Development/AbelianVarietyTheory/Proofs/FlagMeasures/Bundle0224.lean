module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularLatticeFundamentalSetVolume
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0179
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDualVectorsLocalHermitianFrame
section
noncomputable section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.LocDual

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

private lemma h_add_right (H : HermSp M V) (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm y x, ← H.h_herm y' x]

private lemma h_smul_right (H : HermSp M V) (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

private lemma h_neg_left (H : HermSp M V) (x y : V) : H.h (-x) y = - H.h x y := by
  have := H.h_smul_left (-1) x y
  simpa using this

private lemma h_sub_left (H : HermSp M V) (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [sub_eq_add_neg, H.h_add_left, h_neg_left, ← sub_eq_add_neg]

private lemma h_sub_right (H : HermSp M V) (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [H.h_herm (y - y') x, h_sub_left, map_sub, ← H.h_herm y x, ← H.h_herm y' x]

private lemma h_sum_left (H : HermSp M V) {ι : Type} (s : Finset ι) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, v i) y = ∑ i ∈ s, H.h (v i) y := by
  let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x y) (fun a b => H.h_add_left a b y)
  exact map_sum φ v s

private lemma h_sum_right (H : HermSp M V) {ι : Type} (s : Finset ι) (v : ι → V) (x : V) :
    H.h x (∑ i ∈ s, v i) = ∑ i ∈ s, H.h x (v i) := by
  let φ : V →+ E := AddMonoidHom.mk' (fun y => H.h x y) (fun a b => h_add_right H x a b)
  exact map_sum φ v s

end GlobalTheory.LocDual


open GlobalTheory.LocDual in
theorem GlobalTheory.LocDual.frameD_exists : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (f : Fin (r + 1) → V) (T : F), T ≠ 0 → (∀ a b : Fin (r + 1), (a ≠ Fin.last r ∨ b ≠ Fin.last r) → H.h (f a) (f b) = 0) → H.h (f (Fin.last r)) (f (Fin.last r)) = -(algebraMap F E T) → (∃ y : Fin r → V, ∀ i j : Fin r, H.h (f i.castSucc) (y j) = if i = j then 1 else 0) → ∃ Fr : FrameD H r, Fr.f = f ∧ Fr.T = T := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r f T hT hiso hzz hy
  obtain ⟨y, hy⟩ := hy
  haveI := hM.char0
  set z := f (Fin.last r) with hz
  set e : Fin r → V := fun i => f i.castSucc with he
  have hez : ∀ k, H.h (e k) z = 0 := fun k => hiso _ _ (Or.inl (Fin.castSucc_ne_last k))
  have hze : ∀ k, H.h z (e k) = 0 := fun k => hiso _ _ (Or.inr (Fin.castSucc_ne_last k))
  have hee : ∀ k l, H.h (e k) (e l) = 0 := fun k l => hiso _ _ (Or.inl (Fin.castSucc_ne_last k))
  let y' : Fin r → V := fun j => y j + (H.h (y j) z * algebraMap F E T⁻¹) • z
  have hy'z : ∀ j, H.h (y' j) z = 0 := by
    intro j
    simp only [y', H.h_add_left, H.h_smul_left, hzz]
    rw [show H.h (y j) z * algebraMap F E T⁻¹ * -algebraMap F E T
        = - (H.h (y j) z * algebraMap F E (T⁻¹ * T)) by rw [map_mul]; ring]
    rw [inv_mul_cancel₀ hT, map_one, mul_one, add_neg_cancel]
  have hey' : ∀ k j, H.h (e k) (y' j) = if k = j then 1 else 0 := by
    intro k j
    simp only [y', h_add_right, h_smul_right, hez, mul_zero, add_zero, e]
    exact hy k j
  let half : E := algebraMap F E (1 / 2)
  have hhalf : M.L.cj half = half := M.L.cj.commutes _
  have hhalf2 : half + half = 1 := by
    simp only [half, ← map_add (f := _), add_halves, map_one]
  let b : Fin r → Fin r → E := fun j k => half * H.h (y' j) (y' k)
  let es : Fin r → V := fun j => y' j - ∑ k, b j k • e k
  have hesL : ∀ i v, H.h (es i) v = H.h (y' i) v - ∑ k, b i k * H.h (e k) v := by
    intro i v
    simp only [es, h_sub_left, h_sum_left, H.h_smul_left]
  have hesR : ∀ v j, H.h v (es j) = H.h v (y' j) - ∑ k, M.L.cj (b j k) * H.h v (e k) := by
    intro v j
    simp only [es, h_sub_right, h_sum_right, h_smul_right]
  have hy'e : ∀ i k, H.h (y' i) (e k) = if k = i then 1 else 0 := by
    intro i k
    rw [H.h_herm, hey' k i]
    split_ifs <;> simp
  refine ⟨⟨f, es, T, hiso, hzz, ?_, ?_, ?_⟩, rfl, rfl⟩
  · intro i j
    rw [hesR]
    simp only [hesL, hey', hy'e, hee, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [b, map_mul, hhalf]
    rw [← H.h_herm (y' j) (y' i)]
    linear_combination (-H.h (y' i) (y' j)) * hhalf2
  · intro i j
    show H.h (e i) (es j) = _
    rw [hesR]
    simp only [hey', hee, mul_zero, Finset.sum_const_zero, sub_zero]
  · intro i
    show H.h (es i) z = 0
    rw [hesL]
    simp only [hy'z, hez, mul_zero, Finset.sum_const_zero, sub_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalSetRowsMiddleSpace
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

noncomputable section

namespace GlobalTheory.DegVol.RefCov

theorem hermPk_eq_Hb {k r : ℕ} (u w : Fin (2 * r + k + 1) → ℂ) (hu : inWb k r u) (hw : inWb k r w) :
    herm (Hpk k r) u w = herm (Hb k) (fun l => u (wI k r l)) (fun l => w (wI k r l)) := by
  have ue : ∀ a : Fin r, u (eI k r a) = 0 := fun a => hu _ (Or.inl (by simp [eI]))
  have us : ∀ b : Fin r, u (esI k r b) = 0 := fun b => hu _ (Or.inr (by have := b.2; simp [esI]; omega))
  have we : ∀ a : Fin r, w (eI k r a) = 0 := fun a => hw _ (Or.inl (by simp [eI]))
  have ws : ∀ b : Fin r, w (esI k r b) = 0 := fun b => hw _ (Or.inr (by have := b.2; simp [esI]; omega))
  have inner : ∀ l, (Hpk k r *ᵥ u) (wI k r l) = Rad.sg k l * u (wI k r l) := by
    intro l
    rw [Matrix.mulVec, dotProduct, Rad.sum3 (fun j => Hpk k r (wI k r l) j * u j)]
    simp only [ue, us, mul_zero, Finset.sum_const_zero, add_zero, zero_add, Rad.H_ww]
    rw [Finset.sum_eq_single l] <;> simp +contextual [eq_comm]
  rw [Rad.herm_Hb, herm, dotProduct, Rad.sum3 (fun i => star w i * (Hpk k r *ᵥ u) i)]
  simp only [Pi.star_apply, we, ws, star_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, inner]

theorem mem_smul_inf_rs {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (S : Submodule K V) (A : Submodule (𝓞 K) K)
    (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ A • (L ⊓ rs (𝓞 K) S) ↔ ∃ y : S, y ∈ A • L.comap (S.subtype.restrictScalars (𝓞 K)) ∧ (y : V) = x := by
  set f : S →ₗ[𝓞 K] V := S.subtype.restrictScalars (𝓞 K)
  have h1 : L ⊓ rs (𝓞 K) S = (L.comap f).map f := by
    ext z
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_map, Submodule.mem_comap]
    constructor
    · rintro ⟨hz, hs⟩; exact ⟨⟨z, hs⟩, hz, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨hy, y.2⟩
  have h2 : A • (L.comap f).map f = (A • L.comap f).map f := by
    apply le_antisymm
    · rw [Submodule.smul_le]
      rintro c hc _ ⟨y, hy, rfl⟩
      exact ⟨c • y, Submodule.smul_mem_smul hc hy, rfl⟩
    · rw [Submodule.map_le_iff_le_comap, Submodule.smul_le]
      intro c hc y hy
      rw [Submodule.mem_comap]
      change ((c • y : S) : V) ∈ A • Submodule.map f (Submodule.comap f L)
      rw [Submodule.coe_smul_of_tower]
      exact Submodule.smul_mem_smul hc ⟨y, hy, rfl⟩
  rw [h1, h2, Submodule.mem_map]
  rfl

end GlobalTheory.DegVol.RefCov

theorem _root_.GlobalTheory.DegVol.RefCov.rowsFund : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (S : Submodule K V) (HW : HermSpace K S) (k r : ℕ) (ι : Type) [Fintype ι] (σ : ι → (K →+* ℂ)) (Φ : ι → V → Fin (2 * r + k + 1) → ℂ), (∀ x y : S, HW.B x y = H.B x y) → IsPlaces σ → Module.finrank K S = k + 1 → (∀ v, IsReal H k r (σ v) (Φ v)) → (∀ v, ∀ w ∈ S, inWb k r (Φ v w)) → ∀ (L : Submodule (𝓞 K) V) (𝔡 : Ideal (𝓞 K)) (n : ℤ) (ρ : ℝ), GlobalTheory.HermLat.IsUnimod HW (L.comap (S.subtype.restrictScalars (𝓞 K))) → 𝔡 ≠ ⊥ → 0 < ρ → ∃ F : Set (ι → Fin (k + 1) → ℂ), MeasurableSet F ∧ (∀ a : ι → Fin (k + 1) → ℂ, ∃! x : V, x ∈ ipow 𝔡 n • (L ⊓ rs (𝓞 K) S) ∧ ((fun v => (ρ : ℂ) • fun l => Φ v x (wI k r l)) + a) ∈ F) ∧ volume F = ENNReal.ofReal ((Formalism.HermitianLatticesTheory.vInv K ^ Fintype.card ι * (Ideal.absNorm 𝔡 : ℝ) ^ n * ρ ^ (2 * Fintype.card ι)) ^ (k + 1)) := by
  intro K V _ _ _ _ _ _ _ _ H hK S HW k r ι _ σ Φ hHW hσ hk hΦ hWb L 𝔡 n ρ hL h𝔡 hρ
  obtain ⟨F, hF, hU, hvol⟩ := _root_.GlobalTheory.UnimodCov.unimod_fund K S HW hK k ι σ (fun v x l => Φ v (x : V) (wI k r l)) hσ hk
    (fun v x y => by funext l; simp [(hΦ v).1 (x : V) y])
    (fun v c x => by funext l; simp [(hΦ v).2.1 c (x : V)])
    (fun v x y => by
      rw [← GlobalTheory.DegVol.RefCov.hermPk_eq_Hb _ _ (hWb v x x.2) (hWb v y y.2), (hΦ v).2.2.1, hHW])
    (L.comap (S.subtype.restrictScalars (𝓞 K))) 𝔡 n ρ hL h𝔡 hρ
  refine ⟨F, hF, fun a => ?_, hvol⟩
  obtain ⟨y, ⟨hy, hyF⟩, hyu⟩ := hU a
  refine ⟨(y : V), ⟨(GlobalTheory.DegVol.RefCov.mem_smul_inf_rs S _ L _).2 ⟨y, hy, rfl⟩, hyF⟩, ?_⟩
  rintro x ⟨hx, hxF⟩
  obtain ⟨y', hy', rfl⟩ := (GlobalTheory.DegVol.RefCov.mem_smul_inf_rs S _ L _).1 hx
  rw [hyu y' ⟨hy', hxF⟩]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameOfIsotropicBlocks
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open Formalism.REAL (Jm UJ Jm_mul_self Jm_conjTranspose)

noncomputable section

namespace GlobalTheory.FrameCompletion

theorem resolution {n n₀ : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] (hn : n = n₀ + 2 * Fintype.card κ)
    (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin n₀) (Fin n₀) ℂ) (hJ : Jᴴ = J) (hJJ : J * J = 1)
    (hJ₀ : J₀ * J₀ = 1) (P : Matrix (Fin n) κ ℂ) (C : Matrix (Fin n) (Fin n₀) ℂ)
    (h1 : Pᴴ * P = 1) (h2 : Pᴴ * J * P = 0) (h3 : Pᴴ * C = 0) (h4 : Pᴴ * J * C = 0) (h5 : Cᴴ * J * C = J₀) :
    P * Pᴴ + J * (P * Pᴴ) * J + C * J₀ * Cᴴ * J = 1 := by

  have a2 : Pᴴ * (J * P) = 0 := by rw [← Matrix.mul_assoc]; exact h2
  have a4 : Pᴴ * (J * (J * P)) = 1 := by rw [← Matrix.mul_assoc J, hJJ, Matrix.one_mul, h1]
  have a6 : Pᴴ * (J * C) = 0 := by rw [← Matrix.mul_assoc]; exact h4
  have hCP : Cᴴ * P = 0 := by
    have := congrArg conjTranspose h3
    simpa [conjTranspose_mul] using this
  have hCJP : Cᴴ * (J * P) = 0 := by
    have := congrArg conjTranspose h4
    simpa [conjTranspose_mul, hJ, Matrix.mul_assoc] using this
  have a7 : J₀ * (Cᴴ * (J * P)) = 0 := by rw [hCJP, Matrix.mul_zero]
  have a8 : J₀ * (Cᴴ * (J * (J * P))) = 0 := by
    rw [← Matrix.mul_assoc J J, hJJ, Matrix.one_mul, hCP, Matrix.mul_zero]
  have a9 : J₀ * (Cᴴ * (J * C)) = 1 := by rw [← Matrix.mul_assoc Cᴴ, h5, hJ₀]
  have hLM : fromRows (fromRows Pᴴ (Pᴴ * J)) (J₀ * Cᴴ * J) * fromCols (fromCols P (J * P)) C = 1 := by
    rw [fromRows_mul_fromCols, fromRows_mul_fromCols, fromRows_mul, mul_fromCols]
    simp only [Matrix.mul_assoc]
    rw [h1, a2, a4, h3, a6, a7, a8, a9, fromRows_zero, fromCols_zero, fromBlocks_one, fromBlocks_one]
  have hcard : Fintype.card ((κ ⊕ κ) ⊕ Fin n₀) = Fintype.card (Fin n) := by
    simp only [Fintype.card_sum, Fintype.card_fin, hn]
    ring
  have hML := (mul_eq_one_comm_of_card_eq ((κ ⊕ κ) ⊕ Fin n₀) (Fin n) ℂ hcard).mp hLM
  rw [← hML]
  simp only [fromCols_mul_fromRows, Matrix.mul_assoc]

theorem exists_square {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℂ) :
    ∃ D : Matrix (Fin m) (Fin m) ℂ, Dᴴ * D = Cᴴ * C := by
  open ComplexOrder MatrixOrder in
  have h0 : (0 : Matrix (Fin m) (Fin m) ℂ) ≤ Cᴴ * C := (posSemidef_conjTranspose_mul_self C).nonneg
  open ComplexOrder MatrixOrder in
  refine ⟨CFC.sqrt (Cᴴ * C), ?_⟩
  open ComplexOrder MatrixOrder in
  rw [← star_eq_conjTranspose, (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (Cᴴ * C))).star_eq]
  open ComplexOrder MatrixOrder in
  exact CFC.sqrt_mul_sqrt_self (Cᴴ * C) h0

theorem exists_isFrame : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (A₀ : Matrix (Fin n) (Fin n₀) ℂ), n = n₀ + 2 * ∑ i, j i → (∀ i, (B i)ᴴ * B i = 1) → (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) → (∀ i k, (B i)ᴴ * Formalism.REAL.Jm ε * B k = 0) → (∀ i, (B i)ᴴ * Formalism.REAL.Jm ε * A₀ = 0) → A₀ᴴ * Formalism.REAL.Jm ε * A₀ = Formalism.REAL.Jm ε₀ → ∃ (B₀ : Matrix (Fin n) (Fin n₀) ℂ) (s : Formalism.REAL.UJ ε₀) (d : ∀ k, Matrix (Fin (j k)) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ ∧ A₀ = B₀ * uMat s + ∑ k, B k * d k := by
  intro n n₀ a j ε ε₀ B A₀ hn h1 h2 h3 h4 h5
  classical
  have hJJ : Jm ε * Jm ε = 1 := Jm_mul_self ε
  have hJh : (Jm ε)ᴴ = Jm ε := Jm_conjTranspose ε
  have hJ₀J₀ : Jm ε₀ * Jm ε₀ = 1 := Jm_mul_self ε₀
  have hJ₀h : (Jm ε₀)ᴴ = Jm ε₀ := Jm_conjTranspose ε₀
  have hJJX : ∀ {m : Type} [Fintype m] (X : Matrix (Fin n) m ℂ), Jm ε * (Jm ε * X) = X := by
    intro m _ X
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]

  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Σ i, Fin (j i)) ℂ, P = Matrix.of fun r x => B x.1 r x.2 := ⟨_, rfl⟩
  have hPe : ∀ {m : Type} [Fintype m] (X : Matrix (Fin n) m ℂ) (x : Σ i, Fin (j i)) (d : m),
      (Pᴴ * X) x d = ((B x.1)ᴴ * X) x.2 d := by
    intro m _ X x d
    simp [hP, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hPc : ∀ {m : Type} [Fintype m] (X : Matrix m (Fin n) ℂ) (c : m) (x : Σ i, Fin (j i)),
      (X * P) c x = (X * B x.1) c x.2 := by
    intro m _ X c x
    simp [hP, Matrix.mul_apply]
  have hPPX : ∀ {m : Type} [Fintype m] (X : Matrix (Fin n) m ℂ),
      P * (Pᴴ * X) = ∑ i, B i * ((B i)ᴴ * X) := by
    intro m _ X
    ext r d
    simp only [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_sigma, hP, Matrix.of_apply,
      Matrix.conjTranspose_apply]
  have hPP : Pᴴ * P = 1 := by
    ext ⟨i, c⟩ ⟨k, d⟩
    rw [hPc, hPe]
    by_cases hik : i = k
    · subst hik
      simp [h1, Matrix.one_apply]
    · simp [h2 i k hik, hik]
  have hPJP : Pᴴ * Jm ε * P = 0 := by
    ext ⟨i, c⟩ ⟨k, d⟩
    rw [hPc, Matrix.mul_assoc, hPe, ← Matrix.mul_assoc]
    simp [h3 i k]
  have hPJA : Pᴴ * (Jm ε * A₀) = 0 := by
    ext ⟨i, c⟩ d
    rw [hPe, ← Matrix.mul_assoc]
    simp [h4 i]

  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin n) (Fin n₀) ℂ, C = A₀ - P * (Pᴴ * A₀) := ⟨_, rfl⟩
  have hPC : Pᴴ * C = 0 := by
    rw [hC, Matrix.mul_sub, ← Matrix.mul_assoc Pᴴ P, hPP, Matrix.one_mul, sub_self]
  have hJC0 : Jm ε * C = Jm ε * A₀ - Jm ε * P * (Pᴴ * A₀) := by
    rw [hC, Matrix.mul_sub, Matrix.mul_assoc]
  have hPJC : Pᴴ * (Jm ε * C) = 0 := by
    have hPJP' : Pᴴ * (Jm ε * P) = 0 := by rw [← Matrix.mul_assoc]; exact hPJP
    rw [hJC0, Matrix.mul_sub, hPJA, ← Matrix.mul_assoc Pᴴ, hPJP', Matrix.zero_mul, sub_zero]
  have hCJP : Cᴴ * (Jm ε * P) = 0 := by
    have := congrArg conjTranspose hPJC
    simpa [conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have hAJP : A₀ᴴ * (Jm ε * P) = 0 := by
    have := congrArg conjTranspose hPJA
    simpa [conjTranspose_mul, hJh, Matrix.mul_assoc] using this
  have hCJC : Cᴴ * (Jm ε * C) = Jm ε₀ := by
    rw [hJC0, Matrix.mul_sub, ← Matrix.mul_assoc Cᴴ (Jm ε * P), hCJP, Matrix.zero_mul, sub_zero, hC,
      conjTranspose_sub, Matrix.sub_mul, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      Matrix.mul_assoc, Matrix.mul_assoc, hPJA, Matrix.mul_zero, Matrix.mul_zero, sub_zero,
      ← Matrix.mul_assoc, h5]
  have hcard : n = n₀ + 2 * Fintype.card (Σ i, Fin (j i)) := by
    simp [Fintype.card_sigma, hn]
  have hres := resolution hcard (Jm ε) (Jm ε₀) hJh hJJ hJ₀J₀ P C hPP hPJP hPC
    (by rw [Matrix.mul_assoc]; exact hPJC) (by rw [Matrix.mul_assoc]; exact hCJC)

  have hJC : Jm ε * C = C * (Jm ε₀ * (Cᴴ * C)) := by
    calc Jm ε * C
        = (P * Pᴴ + Jm ε * (P * Pᴴ) * Jm ε + C * Jm ε₀ * Cᴴ * Jm ε) * (Jm ε * C) := by
          rw [hres, Matrix.one_mul]
      _ = P * (Pᴴ * (Jm ε * C)) + Jm ε * (P * (Pᴴ * (Jm ε * (Jm ε * C))))
          + C * (Jm ε₀ * (Cᴴ * (Jm ε * (Jm ε * C)))) := by
          simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = C * (Jm ε₀ * (Cᴴ * C)) := by
          rw [hPJC, hJJX, hPC]
          simp
  have hCJ : Cᴴ * Jm ε = Cᴴ * (C * (Jm ε₀ * Cᴴ)) := by
    have := congrArg conjTranspose hJC
    simpa [conjTranspose_mul, hJh, hJ₀h, Matrix.mul_assoc] using this
  have hHJH : (Cᴴ * C) * Jm ε₀ * (Cᴴ * C) = Jm ε₀ := by
    calc (Cᴴ * C) * Jm ε₀ * (Cᴴ * C) = Cᴴ * (C * (Jm ε₀ * (Cᴴ * C))) := by simp only [Matrix.mul_assoc]
      _ = Cᴴ * (Jm ε * C) := by rw [hJC]
      _ = Jm ε₀ := hCJC
  obtain ⟨D, hD⟩ := exists_square C
  have hdetJ₀ : (Jm ε₀).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hJ₀J₀
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hdet : D.det ≠ 0 := by
    intro h0
    have hH : (Cᴴ * C).det = 0 := by rw [← hD, Matrix.det_mul, h0, mul_zero]
    have := congrArg Matrix.det hHJH
    rw [Matrix.det_mul, Matrix.det_mul, hH, zero_mul, zero_mul] at this
    exact hdetJ₀ this.symm
  obtain ⟨s, hsh, hss⟩ := GlobalTheory.T.exists_hermitian_sqrt_in_signedUnitaryGroup n₀ ε₀ D hdet (by rw [hD]; exact hHJH)
  rw [hD] at hss
  obtain ⟨S, hS⟩ : ∃ S, S = uMat s := ⟨_, rfl⟩
  obtain ⟨S', hS'⟩ : ∃ S' : Matrix (Fin n₀) (Fin n₀) ℂ,
      S' = (((s : (Matrix (Fin n₀) (Fin n₀) ℂ)ˣ)⁻¹ : (Matrix (Fin n₀) (Fin n₀) ℂ)ˣ) : Matrix (Fin n₀) (Fin n₀) ℂ) :=
    ⟨_, rfl⟩
  have hSS' : S * S' = 1 := by rw [hS, hS']; exact Units.mul_inv _
  have hS'S : S' * S = 1 := by rw [hS, hS']; exact Units.inv_mul _
  rw [← hS] at hsh hss
  have hsJ : Sᴴ * Jm ε₀ * S = Jm ε₀ := by rw [hS]; exact s.2
  rw [hsh] at hsJ
  have hSS'h : S * S'ᴴ = 1 := by
    have := congrArg conjTranspose hS'S
    simpa [conjTranspose_mul, hsh] using this
  have hS'h : S'ᴴ = S' := by
    calc S'ᴴ = S' * S * S'ᴴ := by rw [hS'S, Matrix.one_mul]
      _ = S' := by rw [Matrix.mul_assoc, hSS'h, Matrix.mul_one]
  have hJ₀S : Jm ε₀ * S = S' * Jm ε₀ := by
    calc Jm ε₀ * S = S' * S * Jm ε₀ * S := by rw [hS'S, Matrix.one_mul]
      _ = S' * (S * Jm ε₀ * S) := by simp only [Matrix.mul_assoc]
      _ = S' * Jm ε₀ := by rw [hsJ]
  have hBC : ∀ i, (B i)ᴴ * C = 0 := by
    intro i
    ext c d
    have := congrFun (congrFun hPC ⟨i, c⟩) d
    rw [hPe] at this
    simpa using this
  refine ⟨C * S', s, fun k => (B k)ᴴ * A₀, ?_, ?_⟩
  · refine ⟨h1, h2, h3, ?_, ?_, ?_, ?_⟩
    · intro i
      rw [← Matrix.mul_assoc, hBC i, Matrix.zero_mul]
    · calc (C * S')ᴴ * (C * S') = S'ᴴ * ((Cᴴ * C) * S') := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = 1 := by
            rw [hS'h, ← hss, Matrix.mul_assoc, hSS', Matrix.mul_one, hS'S]
    · calc Jm ε * (C * S') = C * (Jm ε₀ * (Cᴴ * C)) * S' := by
            rw [← Matrix.mul_assoc, hJC]
        _ = C * (Jm ε₀ * S) * (S * S') := by
            rw [← hss]; simp only [Matrix.mul_assoc]
        _ = C * S' * Jm ε₀ := by
            rw [hSS', Matrix.mul_one, hJ₀S, Matrix.mul_assoc]
    · have hsum : ∑ i, B i * (B i)ᴴ = P * Pᴴ := by
        have := hPPX (1 : Matrix (Fin n) (Fin n) ℂ)
        simpa using this.symm
      have hsumJ : ∑ i, Jm ε * B i * (B i)ᴴ * Jm ε = Jm ε * (P * Pᴴ) * Jm ε := by
        rw [← hsum, Finset.mul_sum, Finset.sum_mul]
        simp only [Matrix.mul_assoc]
      have hlast : C * S' * (C * S')ᴴ = C * Jm ε₀ * Cᴴ * Jm ε := by
        calc C * S' * (C * S')ᴴ = C * (S' * S') * Cᴴ := by
              simp only [conjTranspose_mul, hS'h, Matrix.mul_assoc]
          _ = C * (Jm ε₀ * (S * (S * Jm ε₀))) * Cᴴ := by
              congr 2
              symm
              rw [← Matrix.mul_assoc (Jm ε₀) S, hJ₀S, Matrix.mul_assoc S', ← Matrix.mul_assoc (Jm ε₀) S, hJ₀S,
                Matrix.mul_assoc S', hJ₀J₀, Matrix.mul_one]
          _ = C * Jm ε₀ * Cᴴ * Jm ε := by
              rw [Matrix.mul_assoc (C * Jm ε₀), hCJ, ← Matrix.mul_assoc Cᴴ C, ← hss]
              simp only [Matrix.mul_assoc]
      rw [hsum, hsumJ, hlast]
      exact hres
  · have hsum : ∑ k, B k * ((B k)ᴴ * A₀) = P * (Pᴴ * A₀) := (hPPX A₀).symm
    simp only [hsum, Matrix.mul_assoc]
    rw [← hS, hS'S, Matrix.mul_one, hC, sub_add_cancel]

end GlobalTheory.FrameCompletion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSigmaFiniteQuot
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegVol.StabQuot

theorem sigmaFinite_quot {k r : ℕ} {μG μS ν : Measure (Mt k r)} [SigmaFinite μG] [SFinite μS]
    (hS : μS ≠ 0) (hq : IsQuotMeas μG μS ν) : SigmaFinite ν := by
  obtain ⟨f, hf0, hfm, hfi⟩ := exists_pos_lintegral_lt_of_sigmaFinite μG (ε := 1) one_ne_zero
  have hm : Measurable fun x => (f x : ℝ≥0∞) := hfm.coe_nnreal_ennreal
  have hact : Measurable fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 :=
    (GlobalTheory.Amp.CutQuot.continuous_act k r).measurable
  have hm2 : Measurable fun p : Mt k r × Mt k r => (f (lmulM (Matrix.of p.2) p.1) : ℝ≥0∞) :=
    hm.comp (hact.comp measurable_swap)
  set F : Mt k r → ℝ≥0∞ := fun x => ∫⁻ s, (f (lmulM (Matrix.of s) x) : ℝ≥0∞) ∂μS with hF
  have hFm : Measurable F := hm2.lintegral_prod_right'
  have hFi : ∫⁻ x, F x ∂ν < 1 := (hq _ hm).symm.trans_lt hfi
  have hFpos : ∀ x, 0 < F x := fun x => by
    have hx : Measurable fun s => (f (lmulM (Matrix.of s) x) : ℝ≥0∞) :=
      hm.comp (continuous_rmulM (k := k) (r := r) (Matrix.of x)).measurable
    rw [hF, lintegral_pos_iff_support hx]
    have : Function.support (fun s => (f (lmulM (Matrix.of s) x) : ℝ≥0∞)) = Set.univ := by
      ext s; simp [(hf0 _).ne']
    rw [this]
    exact Measure.measure_univ_pos.mpr hS
  refine Measure.sigmaFinite_of_countable (S := Set.range fun n : ℕ => {x | ((n : ℝ≥0∞))⁻¹ ≤ F x})
    (Set.countable_range _) ?_ ?_
  · rintro _ ⟨n, rfl⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have e : {x | (((0 : ℕ) : ℝ≥0∞))⁻¹ ≤ F x} = {x | F x = ∞} := by ext x; simp
      show ν {x | (((0 : ℕ) : ℝ≥0∞))⁻¹ ≤ F x} < ∞
      rw [e, measure_eq_top_of_lintegral_ne_top hFm.aemeasurable (hFi.trans ENNReal.one_lt_top).ne]
      simp
    · exact (meas_ge_le_lintegral_div hFm.aemeasurable (by simp) (by simpa using hn.ne')).trans_lt
        (ENNReal.div_lt_top (hFi.trans ENNReal.one_lt_top).ne (by simp))
  · rw [Set.sUnion_range, Set.eq_univ_iff_forall]
    intro x
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (hFpos x).ne'
    exact Set.mem_iUnion.mpr ⟨n, hn.le⟩

theorem exists_sigmaFinite_quot : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) (μG μ : Measure (Mt k r)), IsHaarOn (UH (Hpk k r)) μG → IsNormalFormStabilizerMeasure k r hj z' z γ⁻¹ 1 μ → γ ∈ UH (Hpk k r) → SigmaFinite μ ∧ IsHaarOn (Rset k r γ⁻¹) μ ∧ IsNormalFormStabilizerMeasure k r hj z z' γ 1 (μ.map (conjM γ⁻¹)) ∧ ∃ ν : Measure (Mt k r), SigmaFinite ν ∧ ν {x | Matrix.of x ∉ UH (Hpk k r)} = 0 ∧ IsQuotMeas μG (μ.map (conjM γ⁻¹)) ν := by
  intro k r j hj z z' γ μG μ hG hN hγ
  obtain ⟨-, -, a3, -, a5, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z' z γ⁻¹ 1 μ one_pos hN
  rw [Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_GG hγ)] at a5
  obtain ⟨-, b2, b3, b4, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z z' γ 1 _ one_pos a5
  obtain ⟨ν, hν⟩ := GlobalTheory.SgQuot.exists_isQuotMeas k r _ μG _ b2 hG b3 b4
  haveI := hG.1
  haveI := b3.1
  exact ⟨a3.1, a3, a5, ν, sigmaFinite_quot b3.2.1 hν,
    (GlobalTheory.Amp.CutQuot.cut_quotient k r _ μG _ ν b2 hG b3 b4 hν).1, hν⟩

end GlobalTheory.DegVol.StabQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisTail
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.OrthoMass

theorem main : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∃ ms : ℕ → ℝ, (∀ n, 0 < ms n) ∧ ∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (h : W →ₗ⋆[K] W →ₗ[K] K) (I : Submodule (𝓞 K) W), h.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h I n → Formalism.HermitianLatticesTheory.mass h I = ms n := by
  intro K _ _ _ hK
  refine ⟨fun n => Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm K n) (Formalism.MainNotions.StandardLattice.stdLat K n), fun n => ?_, ?_⟩
  · show 0 < Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm K n) (Formalism.MainNotions.StandardLattice.stdLat K n)
    rw [Formalism.MainNotions.StandardLattice.standard_form_eq_telescope_form, Formalism.MainNotions.StandardLattice.standard_lattice_eq_telescope_lattice]
    exact Formalism.HermitianLatticesTheory.massTelescope_std_pos K hK n
  · intro n W _ _ _ _ h I _ ho
    exact Formalism.MainNotions.StandardLattice.mass_ortho K hK n W h I ho

end GlobalTheory.OrthoMass
end

