module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0243
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.Bundle0001
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowCharacterIdAddQSmulLatticePreservingEqOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.LamRowCong

open GlobalTheory.TopStep

section Gen

variable {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem unitV_det_eq_one (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {t : ℕ} (A : Matrix (Fin t) (Fin t) E)
    (hA : ∀ s s', IntAt P (A s s')) (h1 : A.map (redP P) = 1) : LocE.unitV χ A.det = 1 := by
  have hd : redP P A.det = 1 := by rw [(det_int hA).2, h1, Matrix.det_one]
  have hu : IsUnit (redP P A.det) := hd ▸ isUnit_one
  unfold LocE.unitV
  rw [dite_eq_left hu]
  have : hu.unit = 1 := Units.ext (by simp [hd])
  rw [this, map_one, Units.val_one]

theorem sum_red_zero (M : ℕ → ℕ → E) {B : ℕ}
    (hM : ∀ p p', p < B → p' < B → IntAt P (M p p') ∧ redP P (M p p') = if p = p' then 1 else 0)
    (a b : ℕ → ℕ) (n : ℕ) (hab : ∀ i < n, a i < B ∧ b i < B ∧ a i ≠ b i) :
    IntAt P (∑ i ∈ Finset.range n, M (a i) (b i)) ∧ redP P (∑ i ∈ Finset.range n, M (a i) (b i)) = 0 := by
  have hI : ∀ i ∈ Finset.range n, IntAt P (M (a i) (b i)) := fun i hi => by
    have h := hab i (Finset.mem_range.1 hi)
    exact (hM _ _ h.1 h.2.1).1
  refine ⟨intAt_sum _ hI, ?_⟩
  rw [reduction_sum₂ _ hI]
  refine Finset.sum_eq_zero fun i hi => ?_
  have h := hab i (Finset.mem_range.1 hi)
  rw [(hM _ _ h.1 h.2.1).2, if_neg h.2.2]

theorem prod_blocks_eq_one (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (M : ℕ → ℕ → E) {B r t j : ℕ}
    (hM : ∀ p p', p < B → p' < B → IntAt P (M p p') ∧ redP P (M p p') = if p = p' then 1 else 0)
    (hrj : r + j * t ≤ B) :
    ∏ i ∈ Finset.range j, LocE.unitV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1))) = 1 := by
  refine Finset.prod_eq_one fun i hi => ?_
  have hij : i + 1 ≤ j := Finset.mem_range.1 hi
  have h2 : i * t + t ≤ j * t := by
    have := Nat.mul_le_mul_right t hij
    rwa [Nat.add_mul, one_mul] at this
  have hb : ∀ s : Fin t, r + i * t + s.1 < B := fun s => by
    have := s.2
    omega
  refine unitV_det_eq_one _ _ (fun s s' => (hM _ _ (hb s) (hb s')).1) ?_
  ext s s'
  rw [Matrix.map_apply, Matrix.of_apply, (hM _ _ (hb s) (hb s')).2, Matrix.one_apply]
  by_cases h : s = s'
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun h' => h (Fin.ext (by omega)))]

theorem lamGv_eq_one (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (M : ℕ → ℕ → E)
    {B r t j : ℕ} (hM : ∀ p p', p < B → p' < B → IntAt P (M p p') ∧ redP P (M p p') = if p = p' then 1 else 0)
    (hr : r ≤ B) (hrj : r + j * t ≤ B) : LocE.lamGv ψ₀ χ r t j M = 1 := by
  unfold LocE.lamGv
  rw [(sum_red_zero M hM (fun i => i) (fun i => i + 1) (r - 1) fun i hi => ⟨by omega, by omega, by omega⟩).2,
    AddChar.map_zero_eq_one, one_mul]
  exact prod_blocks_eq_one χ M hM hrj

theorem lamGvS_eq_one (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (M : ℕ → ℕ → E)
    {B k₀ r t j : ℕ} (hM : ∀ p p', p < B → p' < B → IntAt P (M p p') ∧ redP P (M p p') = if p = p' then 1 else 0)
    (hk : k₀ ≤ r) (hr : r ≤ B) (hrj : r + j * t ≤ B) : LocE.lamGvS ψ₀ χ k₀ r t j M = 1 := by
  unfold LocE.lamGvS
  have h1 := sum_red_zero M hM (fun i => i) (fun i => i + 1) (k₀ - 1) fun i hi => ⟨by omega, by omega, by omega⟩
  have h2 := sum_red_zero M hM (fun i => k₀ + i) (fun i => k₀ + i + 1) (r - k₀ - 1)
    fun i hi => ⟨by omega, by omega, by omega⟩
  rw [reduction_add h1.1 h2.1, h1.2, h2.2, add_zero, AddChar.map_zero_eq_one, one_mul]
  exact prod_blocks_eq_one χ M hM hrj

end Gen

section Ent

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem fIdx_lt {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : LocE.fIdx k₀ c n p < n + c := by
  unfold LocE.fIdx
  split_ifs <;> omega

theorem fIdx_inj {k₀ c n p p' : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) (hp' : p' < n + c)
    (h : LocE.fIdx k₀ c n p = LocE.fIdx k₀ c n p') : p = p' := by
  unfold LocE.fIdx at h
  split_ifs at h <;> omega

theorem entB_one_add_q {k₀ n c : ℕ} (hk : k₀ ≤ n) (ex : ℕ → ℕ) (y : HomE E (n + c) (n + c))
    (hy : ∀ x ∈ LocE.lamY P (qOf P) n c ex, y x ∈ LocE.lamY P (qOf P) n c ex) {p p' : ℕ}
    (hp : p < n + c) (hp' : p' < n + c) :
    IntAt P (LocE.entB (qOf P) k₀ c n c n ex ex (LinearMap.id + ((qOf P : ℕ) : E) • y) p p') ∧
      redP P (LocE.entB (qOf P) k₀ c n c n ex ex (LinearMap.id + ((qOf P : ℕ) : E) • y) p p') =
        if p = p' then 1 else 0 := by
  have hQ0 : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have hfl : LocE.fIdx k₀ c n p < n + c := fIdx_lt hk hp
  have hfl' : LocE.fIdx k₀ c n p' < n + c := fIdx_lt hk hp'
  have hb : IntAt P ((((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p))⁻¹ *
      (((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p') *
        y (Loc.eN E (n + c) (LocE.fIdx k₀ c n p')) ⟨_, hfl⟩)) := by
    have h1 := hy _ (GlobalTheory.CongLevel.bvec_mem P (qOf P) hQ0 (n + c) (LocE.scE n ex) (LocE.fIdx k₀ c n p'))
    have h2 := (GlobalTheory.CongLevel.mem_sclLat P (qOf P) (n + c) _ _).1 h1 ⟨_, hfl⟩
    rw [map_smul, Pi.smul_apply, smul_eq_mul] at h2
    exact h2
  have key : LocE.entB (qOf P) k₀ c n c n ex ex (LinearMap.id + ((qOf P : ℕ) : E) • y) p p' =
      (if p = p' then 1 else 0) + ((qOf P : ℕ) : E) * ((((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p))⁻¹ *
      (((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p') *
        y (Loc.eN E (n + c) (LocE.fIdx k₀ c n p')) ⟨_, hfl⟩)) := by
    unfold LocE.entB Loc.atN
    rw [dite_eq_left hfl, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    by_cases hpp : p = p'
    · subst hpp
      have : Loc.eN E (n + c) (LocE.fIdx k₀ c n p) ⟨_, hfl⟩ = 1 := by simp [Loc.eN]
      rw [this, if_pos rfl, sub_self, zpow_zero, mul_one]
      have h0 := zpow_ne_zero (LocE.scE n ex (LocE.fIdx k₀ c n p)) hQ0
      field_simp
    · have hff : LocE.fIdx k₀ c n p ≠ LocE.fIdx k₀ c n p' := fun h => hpp (fIdx_inj hk hp hp' h)
      have : Loc.eN E (n + c) (LocE.fIdx k₀ c n p') ⟨_, hfl⟩ = 0 := by simp [Loc.eN, hff]
      rw [this, if_neg hpp, zero_add, zero_add, zpow_sub₀ hQ0]
      have h0 := zpow_ne_zero (LocE.scE n ex (LocE.fIdx k₀ c n p)) hQ0
      field_simp
  have hd : IntAt P (if p = p' then (1 : E) else 0) := by
    split_ifs
    · exact intAt_one
    · exact intAt_zero
  have hqb := (intAt_nat (P := P) (qOf P)).mul hb
  rw [key]
  refine ⟨hd.add hqb, ?_⟩
  rw [reduction_add hd hqb, reduction_mul (intAt_nat _) hb, reduction_absNorm_eq_zero, zero_mul, add_zero]
  split_ifs
  · exact reduction_one₂
  · exact reduction_zero

end Ent

theorem lamRow_one_add_q : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∈ Pr.vGs → ∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, y x ∈ lamYat (Pr := Pr) (R := R) j P) → lamRow Ch mu sharp j P (LinearMap.id + (qOf P : X.E) • y) = 1 := by
  intro X Pr R Ch S mu sharp j P hP y hy
  have hm := R.two_le_m
  have hk : R.k ≤ R.N j := by unfold Ranks.N; omega
  have hkr : R.k ≤ R.r := by unfold Ranks.r; omega
  have hNj : R.N j = R.k + j * R.t + j := by unfold Ranks.N; ring
  have hr : R.r ≤ R.N j + cOf R j := by
    rw [hNj]
    unfold Ranks.r cOf
    generalize j * R.t = u
    omega
  have hrj : R.r + j * R.t ≤ R.N j + cOf R j := by
    rw [hNj]
    unfold Ranks.r cOf
    generalize j * R.t = u
    omega
  have hy' : ∀ x ∈ LocE.lamY P (qOf P) (R.N j) (cOf R j) (fun i => i + 1),
      y x ∈ LocE.lamY P (qOf P) (R.N j) (cOf R j) (fun i => i + 1) := by
    intro x hx
    have h := hy x (by unfold lamYat; rw [if_pos hP]; exact hx)
    unfold lamYat at h
    rw [if_pos hP] at h
    exact h
  have hM := fun p p' (hp : p < R.N j + cOf R j) (hp' : p' < R.N j + cOf R j) =>
    entB_one_add_q (k₀ := R.k) hk (fun i => i + 1) y hy' hp hp'
  unfold lamRow
  rw [if_pos hP]
  cases sharp
  · simp only [Bool.false_eq_true, if_false]
    unfold LocE.lamGB
    exact lamGv_eq_one _ _ _ hM hr hrj
  · simp only [if_true]
    unfold LocE.lamGBS
    exact lamGvS_eq_one _ _ _ hM hkr hr hrj

end GlobalTheory.LamRowCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ToMatrixCoMulSymm
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc.Emat

open Matrix

theorem gram_of_orth {E : Type} [Field E] [StarRing E] (σ : E →+* E) (hσ : ∀ x, σ x = star x) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (co : (Fin N → E) ≃ₗ[E] (Fin N → E)) (hCo : IsOrthCo σ J co) :
    star (LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E))) * LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) = J := by
  ext i k
  have h := hCo (Pi.single i 1) (Pi.single k 1)
  rw [Matrix.mul_apply]
  have hl : ∀ a, (star (LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)))) i a * LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) a k =
      σ (co (Pi.single i 1) a) * co (Pi.single k 1) a := by
    intro a
    rw [Matrix.star_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, hσ]
    rfl
  rw [Finset.sum_congr rfl fun a _ => hl a, h]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hh
    exact absurd (Finset.mem_univ _) hh
  · intro b _ hb
    refine Finset.sum_eq_zero fun b' _ => ?_
    simp [Pi.single_apply, hb]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

theorem toMatrix_toLE {E : Type} [Field E] {N : ℕ} (γ : GL (Fin N) E) :
    LinearMap.toMatrix' ((toLE γ : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) = γ := by
  ext i j
  simp [toLE, LinearMap.toMatrix'_apply, Matrix.GeneralLinearGroup.toLin, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem unit_mat' {n N : ℕ} (hk : n = N) {E' : Type} [Field E'] [StarRing E'] (co coi γ J : Matrix (Fin N) (Fin N) E')
    (h1 : star co * co = J) (h2 : star γ * J * γ = J) (h3 : co * coi = 1) :
    (co * γ * coi).submatrix (finCongr hk) (finCongr hk) * star ((co * γ * coi).submatrix (finCongr hk) (finCongr hk)) = 1 := by
  subst hk
  have e2 : ∀ A : Matrix (Fin n) (Fin n) E', A.submatrix (finCongr rfl) (finCongr rfl) = A := fun A => by ext x y; rfl
  rw [e2, mul_eq_one_comm]
  calc star (co * γ * coi) * (co * γ * coi) = star coi * (star γ * (star co * co) * γ) * coi := by
        simp only [star_mul, Matrix.mul_assoc]
    _ = star coi * (star co * co) * coi := by rw [h1, h2]
    _ = star (co * coi) * (co * coi) := by simp only [star_mul, Matrix.mul_assoc]
    _ = 1 := by rw [h3, star_one, Matrix.one_mul]

theorem star_eq_cT {E : Type} [Field E] [StarRing E] (σ : E →+* E) (hσ : ∀ x, σ x = star x) {N : ℕ} (M : Matrix (Fin N) (Fin N) E) :
    star M = cT σ M := by
  ext i k
  simp [cT, Matrix.star_apply, hσ]

theorem orth_of_gram {E : Type} [Field E] (σ : E →+* E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (co : (Fin N → E) ≃ₗ[E] (Fin N → E))
    (hM : cT σ (LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E))) * LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) = J) :
    IsOrthCo σ J co := by
  intro x y
  set M := LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) with hMdef
  have hx : ∀ z, co z = M *ᵥ z := fun z => by rw [hMdef, LinearMap.toMatrix'_mulVec]; rfl
  rw [← hM]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hx, Matrix.mulVec, dotProduct, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem toMatrix_stdG {E : Type} [Field E] {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (γ : GL (Fin N) E) :
    LinearMap.toMatrix' ((stdG σ J γ : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) =
      LinearMap.toMatrix' ((stdCo σ J : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) * (γ : Matrix (Fin N) (Fin N) E) *
        LinearMap.toMatrix' (((stdCo σ J).symm : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) := by
  rw [← toMatrix_toLE γ, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  rfl

theorem toMatrix_co_mul_symm {E : Type} [Field E] {N : ℕ} (co : (Fin N → E) ≃ₗ[E] (Fin N → E)) :
    LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) * LinearMap.toMatrix' ((co.symm : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) = 1 := by
  rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]

end GlobalTheory.TwV.Xc.Emat

end


open GlobalTheory.TwV.Xc.Emat in
theorem GlobalTheory.TwV.Xc.eMat_unitary_det : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (σ : E →+* E), (∀ x, σ x = star x) → ∀ (a N : ℕ) (hr : a = N) (J : Matrix (Fin N) (Fin N) E) (crd : GL (Fin N) E), cT σ crd.1 * crd.1 = J → IsOrthCo σ J (stdCo σ J) ∧ ∀ g ∈ UJ σ J, eMat hr σ J g * star (eMat hr σ J g) = 1 ∧ (eMat hr σ J g).det = g.1.det := by
  intro E _ _ _ σ hσ a N hr J crd hcrd
  subst hr
  have hco : IsOrthCo σ J (stdCo σ J) := by
    refine Classical.epsilon_spec (p := IsOrthCo σ J) ⟨toLE crd, ?_⟩
    refine orth_of_gram σ J _ ?_
    rw [toMatrix_toLE]
    exact hcrd
  refine ⟨hco, fun g hg => ?_⟩
  have hg' : star (g : Matrix (Fin a) (Fin a) E) * J * (g : Matrix (Fin a) (Fin a) E) = J := by
    rw [star_eq_cT σ hσ]
    exact hg
  unfold eMat
  rw [toMatrix_stdG]
  refine ⟨unit_mat' rfl _ _ _ J (gram_of_orth σ hσ J _ hco) hg' (toMatrix_co_mul_symm _), ?_⟩
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, toMatrix_co_mul_symm,
    Matrix.det_one, one_mul]
end

