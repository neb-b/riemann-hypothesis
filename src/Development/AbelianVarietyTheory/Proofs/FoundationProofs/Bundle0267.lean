module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0256
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.WittIndexParallel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0714
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleDiagonalDataOfSelfDualNeighbourTriple
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TriangleRows

def cv (D : D7) {n : ℕ} (y : Fin n → D.host.E) : Fin n → D.host.E := fun j => D.host.conj (y j)

def IC (D : D7) (cc : Ideal (𝓞 D.host.K)) {n : ℕ} (L : Lat D n) : Lat D n :=
  Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • fun j => D.host.conj (y j)}

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ}

theorem cv_add (x y : Fin n → D.host.E) : cv D (x + y) = cv D x + cv D y := by
  funext j; simp only [cv, Pi.add_apply, map_add (f := _)]

theorem cv_smul (a : 𝓞 D.host.E) (x : Fin n → D.host.E) :
    cv D (a • x) = ((sgO D a : 𝓞 D.host.E) : D.host.E) • cv D x := by
  funext j
  rw [← algebraMap_smul D.host.E a x]
  simp only [cv, Pi.smul_apply, smul_eq_mul, map_mul, sgO_coe]

theorem smul_cv_mem {L : Lat D n} {t : D.host.E} (ht : t ∈ Iid D cc) {y : Fin n → D.host.E} (hy : y ∈ L) :
    t • cv D y ∈ IC D cc L := Submodule.subset_span ⟨t, ht, y, hy, rfl⟩

theorem IC_mono {L L' : Lat D n} (h : L ≤ L') : IC D cc L ≤ IC D cc L' :=
  Submodule.span_mono fun _ ⟨t, ht, y, hy, e⟩ => ⟨t, ht, y, h hy, e⟩

theorem mul_int {t e : D.host.E} (ht : t ∈ Iid D cc) (he : IntE D e) : t * e ∈ Iid D cc := by
  obtain ⟨a, rfl⟩ := he
  rw [mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ ht

theorem int_hE {L : Lat D n} (hL : SD D L) {x y : Fin n → D.host.E} (hx : x ∈ L) (hy : y ∈ L) :
    IntE D (hE D x y) := (((sd_iff D L).1 hL).2.2 x).1 hx y hy

theorem pair_cv (t : D.host.E) (y w : Fin n → D.host.E) : ∑ j, (t • cv D y) j * w j = t * hE D w y := by
  simp only [cv, hE, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem pair_mem {L : Lat D n} (hL : SD D L) {r w : Fin n → D.host.E} (hr : r ∈ IC D cc L) (hw : w ∈ L) :
    ∑ j, r j * w j ∈ Iid D cc := by
  induction hr using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hv
    change ∑ j, (t • cv D y) j * w j ∈ _
    rw [pair_cv]
    exact mul_int ht (int_hE hL hw hy)
  | zero => simp
  | add u v _ _ hu hv =>
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact add_mem hu hv
  | smul a v _ hv =>
    simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum]
    exact Submodule.smul_mem _ _ hv

theorem P_smul_cv {M : Lat D n} {P : Ideal (𝓞 D.host.E)} (hσ : ∀ a ∈ P, sgO D a ∈ P) {b : Fin n → D.host.E}
    (hb : ∀ p ∈ P, p • b ∈ M) {p : 𝓞 D.host.E} (hp : p ∈ P) {t : D.host.E} (ht : t ∈ Iid D cc) :
    (p • t) • cv D b ∈ IC D cc M := by
  have h := smul_cv_mem ht (hb _ (hσ p hp))
  rw [cv_smul, sgO_sgO, smul_smul, mul_comm] at h
  rw [Algebra.smul_def]
  exact h

theorem decomp {M : Lat D n} {P : Ideal (𝓞 D.host.E)} (hσ : ∀ a ∈ P, sgO D a ∈ P) {b : Fin n → D.host.E}
    (hb : ∀ p ∈ P, p • b ∈ M) {t₀ : D.host.E}
    (hg : ∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) {r : Fin n → D.host.E}
    (hr : r ∈ IC D cc (M ⊔ Submodule.span (𝓞 D.host.E) {b})) :
    ∃ a : 𝓞 D.host.E, r - (a • t₀) • cv D b ∈ IC D cc M := by
  induction hr using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hv
    obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hw
    obtain ⟨a, ha⟩ := hg (sgO D o • t) (Submodule.smul_mem _ _ ht)
    refine ⟨a, ?_⟩
    have h1 : (sgO D o • t - a • t₀) • cv D b ∈ IC D cc M := by
      refine Submodule.smul_induction_on (p := fun s => s • cv D b ∈ IC D cc M) ha ?_ ?_
      · intro p hp s hs; exact P_smul_cv hσ hb hp hs
      · intro u v hu hv; rw [add_smul]; exact add_mem hu hv
    have h2 := add_mem (smul_cv_mem ht hm) h1
    convert h2 using 1
    change t • cv D (m + o • b) - _ = _
    rw [cv_add, cv_smul, smul_add, smul_smul, sub_smul, Algebra.smul_def (sgO D o) t, mul_comm t, add_sub_assoc]
  | zero => exact ⟨0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨a', ha'⟩ := hv
    refine ⟨a + a', ?_⟩
    convert add_mem ha ha' using 1
    rw [add_smul, add_smul]; abel
  | smul c v _ hv =>
    obtain ⟨a, ha⟩ := hv
    refine ⟨c * a, ?_⟩
    convert Submodule.smul_mem _ c ha using 1
    rw [smul_sub, mul_smul, smul_assoc]

def Pt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) : (Fin N' → Fin N → D.host.E) →+ VC D N N' where
  toFun z := pt D (tor0 D cc δ) δ (Matrix.of z)
  map_zero' := by funext τ i j; simp [pt, embV, tor0]
  map_add' z w := by funext τ i j; simp [pt, embV, tor0, mul_add]

theorem Pt_apply (δ : ℂ) {N N' : ℕ} (z : Fin N' → Fin N → D.host.E) (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    Pt D cc δ N N' z τ i j = δ * embT D τ (z i j) := rfl

def Row (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N : ℕ} (N' : ℕ) (t₀ : D.host.E) (b : Fin N → D.host.E)
    (i : Fin N') : 𝓞 D.host.E →+ VC D N N' where
  toFun a := Pt D cc δ N N' (Pi.single i ((a • t₀) • cv D b))
  map_zero' := by simp
  map_add' a a' := by rw [add_smul, add_smul, Pi.single_add, map_add (f := _)]

theorem Row_apply (δ : ℂ) {N N' : ℕ} (t₀ : D.host.E) (b : Fin N → D.host.E) (i : Fin N') (a : 𝓞 D.host.E) :
    Row D cc δ N' t₀ b i a = Pt D cc δ N N' (Pi.single i ((a • t₀) • cv D b)) := rfl

theorem sum_Row (δ : ℂ) {N N' : ℕ} (t₀ : D.host.E) (b : Fin N → D.host.E) (a : Fin N' → 𝓞 D.host.E) :
    ∑ i, Row D cc δ N' t₀ b i (a i) = Pt D cc δ N N' (fun i => (a i • t₀) • cv D b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Row_apply, ← map_sum]
  rw [Finset.univ_sum_single (fun i => (a i • t₀) • cv D b)]

theorem Hf_zero_left (T : Tor D) {N N' : ℕ} (y : VC D N N') : Hf D T 0 y = 0 := by simp [Hf]

theorem Hf_Row (δ : ℂ) {N N' : ℕ} (t₀ : D.host.E) (b x : Fin N → D.host.E) (i j : Fin N') (a a' : 𝓞 D.host.E) :
    Hf D (tor0 D cc δ) (Row D cc δ N' t₀ x i a') (Row D cc δ N' t₀ b j a) =
      if i = j then Hf D (tor0 D cc δ) (Row D cc δ N' t₀ x i (a' * sgO D a)) (Row D cc δ N' t₀ b i 1) else 0 := by
  split_ifs with h
  · subst h
    simp only [Hf, Row_apply, Pt_apply]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases hk : k = i
    · subst hk
      have e : embT D τ (algebraMap (𝓞 D.host.E) D.host.E (sgO D a)) =
          (starRingEnd ℂ) (embT D τ (algebraMap (𝓞 D.host.E) D.host.E a)) := embT_conj D τ a
      simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul, map_one, e]
      ring
    · simp [Pi.single_eq_of_ne hk]
  · simp only [Hf, Row_apply, Pt_apply]
    rw [Finset.sum_eq_zero, zero_div]
    refine fun τ _ => Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    by_cases hk : k = i
    · subst hk
      simp [Pi.single_eq_of_ne h]
    · simp [Pi.single_eq_of_ne hk]

theorem Pt_mem {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} {L : Lat D N} (hL : SD D L) (z : Fin N' → Fin N → D.host.E) :
    Pt D cc δ N N' z ∈ La D (tor0 D cc δ) L (stdL D N') ↔ ∀ i, z i ∈ IC D cc L := by
  obtain ⟨h1, h2, -, h4⟩ := _root_.GlobalTheory.ThetaLatImage.theta_lattice_image D cc δ hδ N N'
  rw [h2]
  constructor
  · rintro ⟨w, hw, e⟩
    have : Matrix.of z = w := h1 e
    subst this
    exact (h4 L hL _).1 hw
  · intro h
    exact ⟨Matrix.of z, (h4 L hL _).2 h, rfl⟩

theorem exists_Pt {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} {L : Lat D N} {v : VC D N N'}
    (hv : v ∈ La D (tor0 D cc δ) L (stdL D N')) : ∃ z, v = Pt D cc δ N N' z := by
  obtain ⟨w, -, e⟩ := ((_root_.GlobalTheory.ThetaLatImage.theta_lattice_image D cc δ hδ N N').2.1 L _ v).1 hv
  exact ⟨w, e⟩

theorem single_mem {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} {L : Lat D N} (hL : SD D L) (i : Fin N')
    {r : Fin N → D.host.E} (hr : r ∈ IC D cc L) :
    Pt D cc δ N N' (Pi.single i r) ∈ La D (tor0 D cc δ) L (stdL D N') := by
  refine (Pt_mem hδ hL _).2 fun k => ?_
  by_cases hk : k = i
  · subst hk; rwa [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hk]; exact zero_mem _

theorem reduce {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} {M L₁ L₂ : Lat D N} {P : Ideal (𝓞 D.host.E)}
    (hσ : ∀ a ∈ P, sgO D a ∈ P) {b : Fin N → D.host.E} (hb : ∀ p ∈ P, p • b ∈ M) {t₀ : D.host.E}
    (hg : ∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc)
    (hB : SD D (M ⊔ Submodule.span (𝓞 D.host.E) {b})) (h₁ : SD D L₁) (h₂ : SD D L₂) (m₁ : M ≤ L₁) (m₂ : M ≤ L₂) :
    ∀ z ∈ La D (tor0 D cc δ) (M ⊔ Submodule.span (𝓞 D.host.E) {b}) (stdL D N'), ∃ a : Fin N' → 𝓞 D.host.E,
      z - ∑ i, Row D cc δ N' t₀ b i (a i) ∈
        La D (tor0 D cc δ) L₁ (stdL D N') ⊓ La D (tor0 D cc δ) L₂ (stdL D N') := by
  intro z hz
  obtain ⟨w, rfl⟩ := exists_Pt hδ hz
  choose a ha using fun i => decomp hσ hb hg ((Pt_mem hδ hB w).1 hz i)
  refine ⟨a, ?_⟩
  rw [sum_Row, ← map_sub]
  exact ⟨(Pt_mem hδ h₁ _).2 fun i => IC_mono m₁ (ha i), (Pt_mem hδ h₂ _).2 fun i => IC_mono m₂ (ha i)⟩

theorem triDat_rows : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∀ (N N' : ℕ)
    (P : Ideal (𝓞 D.host.E)), P.IsMaximal → (∀ a ∈ P, sgO D a ∈ P) → ∀ A B C : Lat D N, Tri D P A B C →
    TriDat D (tor0 D cc δ) (La D (tor0 D cc δ) A (stdL D N')) (La D (tor0 D cc δ) B (stdL D N'))
      (La D (tor0 D cc δ) C (stdL D N')) P N' := by
  intro D cc δ hcc hδ N N' P hP hσ A B C ⟨hA, hB, hC, M, b, x, eA, eB, eC, hp, hθ⟩
  obtain ⟨t₀, ht₀, hg, hq⟩ := _root_.GlobalTheory.IdealGenerator.exists_generator_Iid D cc hcc P hP
  have mA : M ≤ A := eA ▸ le_sup_left
  have mB : M ≤ B := eB ▸ le_sup_left
  have mC : M ≤ C := eC ▸ le_sup_left
  have bA : b + x ∈ A := eA ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have bB : b ∈ B := eB ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have bC : x ∈ C := eC ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hat : ∀ a : 𝓞 D.host.E, a • t₀ ∈ Iid D cc := fun a => Submodule.smul_mem _ _ ht₀
  have hsm : ∀ (p : 𝓞 D.host.E) (u v : Fin N → D.host.E), p • hE D u v = hE D (p • u) v := fun p u v => by
    rw [← algebraMap_smul D.host.E p u, hE_smul_left, Algebra.smul_def]
  refine ⟨Row D cc δ N' t₀ b, Row D cc δ N' t₀ x, fun i =>
    { toFun := fun s => Hf D (tor0 D cc δ) (Row D cc δ N' t₀ x i s) (Row D cc δ N' t₀ b i 1)
      map_zero' := by rw [map_zero, Hf_zero_left]
      map_add' := fun s s' => by rw [map_add (f := _), Hf_add_left] }, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j a a'
    exact Hf_Row δ t₀ b x i j a a'
  · intro i a
    refine ⟨single_mem hδ hB i (smul_cv_mem (hat a) bB), single_mem hδ hC i (smul_cv_mem (hat a) bC), ?_⟩
    rw [Row_apply, Row_apply, ← map_add (f := _), ← Pi.single_add, ← smul_add, ← cv_add]
    exact single_mem hδ hA i (smul_cv_mem (hat a) bA)
  · intro i p hpP
    have h1 := P_smul_cv hσ (fun p h => (hp p h).1) hpP ht₀
    have h2 := P_smul_cv hσ (fun p h => (hp p h).2) hpP ht₀
    exact ⟨⟨single_mem hδ hA i (IC_mono mA h1), single_mem hδ hC i (IC_mono mC h1)⟩,
      ⟨single_mem hδ hA i (IC_mono mA h2), single_mem hδ hB i (IC_mono mB h2)⟩⟩
  · subst eB
    exact reduce hδ hσ (fun p h => (hp p h).1) hg hB hA hC mA mC
  · subst eC
    exact reduce hδ hσ (fun p h => (hp p h).2) hg hC hA hB mA mB
  · intro a ha i
    rw [sum_Row] at ha
    have h1 := pair_mem hA ((Pt_mem hδ hA _).1 ha i) bA
    rw [pair_cv, hE_add_left, mul_add] at h1
    have h2 := sub_mem h1 (mul_int (hat (a i)) (int_hE hB bB bB))
    rw [add_sub_cancel_left, smul_mul_assoc] at h2
    refine hq (hE D x b) (fun h => hθ (conj_hE D x b ▸ h.conj)) (fun p hpP => ?_) _ h2
    rw [hsm]; exact int_hE hB (mB (hp p hpP).2) bB
  · intro a ha i
    rw [sum_Row] at ha
    have h1 := pair_mem hB ((Pt_mem hδ hB _).1 ha i) bB
    rw [pair_cv, smul_mul_assoc] at h1
    refine hq (hE D b x) hθ (fun p hpP => ?_) _ h1
    rw [hsm]; exact int_hE hC (mC (hp p hpP).1) bC

end GlobalTheory.TriangleRows
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeierstrassPFormalGroupLogUniformises
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.WpForm

open PowerSeries

theorem exists_subst_inverse {R : Type*} [CommRing R] (l : PowerSeries R)
    (h0 : constantCoeff l = 0) (h1 : coeff 1 l = 1) :
    ∃ ex : PowerSeries R, constantCoeff ex = 0 ∧
      subst ex l = (X : PowerSeries R) ∧ subst l ex = (X : PowerSeries R) := by
  have hA : GlobalTheory.FormalInv.linearPart (fun _ : Unit => (l : MvPowerSeries Unit R)) = 1 := by
    ext i j
    exact h1
  obtain ⟨v, hv, h, h'⟩ := (GlobalTheory.FormalInv.exists_substInv_iff
    (u := fun _ : Unit => (l : MvPowerSeries Unit R)) (fun _ => h0)).2 (hA ▸ isUnit_one)
  exact ⟨v (), hv (), h (), h' ()⟩

theorem subst_eq_of_equation {K : Type} [Field K] [CharZero K] {a b : K}
    {P m q M : PowerSeries K} (hP : IsWpSer a b P) (hm : constantCoeff m = 1)
    (hq : constantCoeff q = 1)
    (hd : X * PowerSeries.derivative q - 2 * q = PowerSeries.derivative (X * m) * M)
    (hM : M ^ 2 = 4 * q ^ 3 - C a * X ^ 4 * q - C b * X ^ 6) :
    (subst (X * m : PowerSeries K) P : PowerSeries K) = m ^ 2 * q := by
  set l : PowerSeries K := X * m with hl
  have h0 : constantCoeff l = 0 := by simp [hl]
  have h1 : coeff 1 l = 1 := by
    rw [hl, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul]; simpa using hm
  obtain ⟨ex, he0, he1, he2⟩ := exists_subst_inverse l h0 h1
  have sl : HasSubst l := HasSubst.of_constantCoeff_zero' h0
  have se : HasSubst ex := HasSubst.of_constantCoeff_zero' he0
  have hle : ∀ f : PowerSeries K, (subst l (subst ex f : PowerSeries K) : PowerSeries K) = f := by
    intro f
    rw [subst_comp_subst_apply se sl, he2]
    exact congrFun MvPowerSeries.subst_self f
  have hel : ∀ f : PowerSeries K, (subst ex (subst l f : PowerSeries K) : PowerSeries K) = f := by
    intro f
    rw [subst_comp_subst_apply sl se, he1]
    exact congrFun MvPowerSeries.subst_self f
  set Q : PowerSeries K := subst ex (m ^ 2 * q) with hQ
  have hQl : (subst l Q : PowerSeries K) = m ^ 2 * q := hle _
  have hw : PowerSeries.derivative l = m + X * PowerSeries.derivative m := by
    rw [hl, Derivation.leibniz]; simp [add_comm]
  have hw0 : PowerSeries.derivative l ≠ 0 := by
    intro h
    have := congrArg constantCoeff (hw.symm.trans h)
    simp [hm] at this
  have hch := derivative_subst (f := Q) sl
  rw [hQl, Derivation.leibniz, Derivation.leibniz_pow] at hch
  simp only [smul_eq_mul, nsmul_eq_mul] at hch
  have key : l * (subst l (PowerSeries.derivative Q) : PowerSeries K) - 2 * (m ^ 2 * q) = m ^ 3 * M := by
    apply mul_right_cancel₀ hw0
    have hch' : m ^ 2 * PowerSeries.derivative q + q * (2 * (m * PowerSeries.derivative m)) =
        (subst l (PowerSeries.derivative Q) : PowerSeries K) * PowerSeries.derivative l := by simpa using hch
    linear_combination -l * hch' + m ^ 3 * hd - 2 * m ^ 2 * q * hw +
      (m ^ 2 * PowerSeries.derivative q + q * (2 * (m * PowerSeries.derivative m))) * hl
  have hQW : IsWpSer a b Q := by
    constructor
    · have h2 : ∀ f : PowerSeries K, constantCoeff (subst ex f : PowerSeries K) = constantCoeff f := by
        intro f
        have hf := eq_X_mul_shift_add_const f
        conv_lhs => rw [hf]
        rw [← coe_substAlgHom se, map_add (f := _), map_mul, substAlgHom_X, map_add (f := _), map_mul, he0,
          C_eq_algebraMap, AlgHom.commutes]
        simp
      rw [hQ, h2]; simp [hm, hq]
    · rw [← hel (_ ^ 2), ← hel (_ - C b * X ^ 6)]
      congr 1
      change subst l ((X * PowerSeries.derivative Q - 2 * Q) ^ 2) = _
      rw [← coe_substAlgHom sl]
      simp only [map_pow, map_sub, map_mul, map_ofNat, substAlgHom_X, C_eq_algebraMap,
        AlgHom.commutes]
      rw [coe_substAlgHom sl, hQl]
      simp only [C_eq_algebraMap] at hM
      change (l * _ - _) ^ 2 = _ - algebraMap K (PowerSeries K) a * l ^ 4 * _ -
        algebraMap K (PowerSeries K) b * l ^ 6
      rw [key, hl]
      linear_combination m ^ 6 * hM
  rw [(GlobalTheory.WpSeries.existsUnique_isWpSer K a b).unique hP hQW, hQl]

theorem dX_eq_derivative {K : Type*} [CommRing K] (f : PowerSeries K) : dX f = PowerSeries.derivative f := by
  ext n
  simp [dX, coeff_derivative, mul_comm]

theorem derivative_flog {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve ℂ_[p])
    (wq : PowerSeries ℂ_[p]) : PowerSeries.derivative (flog W wq) = omegaW W wq := by
  ext n
  have : ((n : ℂ_[p]) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp [flog, coeff_derivative, this]

theorem wp_flog : ∀ (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve ℂ_[p]) (wq P : PowerSeries ℂ_[p]), IsWq W wq → IsWpSer (W.c₄ / 12) (W.c₆ / 216) P → PowerSeries.X ^ 2 * (PowerSeries.subst (flog W wq) P : PowerSeries ℂ_[p]) = flog W wq ^ 2 * lineSer wq⁻¹ (-(W.b₂ / 12)) := by
  intro p _ W wq P hwq hP
  have hw1 := GlobalTheory.GenusOneDatum.constantCoeff_of_isWq hwq
  obtain ⟨m, hm⟩ := X_dvd_iff.2 (GlobalTheory.GenusOneDatum.constantCoeff_flog W wq)
  have hm1 : constantCoeff m = 1 := by
    have := GlobalTheory.GenusOneDatum.coeff_one_flog hwq
    rw [hm, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul] at this
    simpa using this
  have he : wq * wq⁻¹ = 1 := PowerSeries.mul_inv_cancel wq (by rw [hw1]; exact one_ne_zero)
  have he1 : constantCoeff wq⁻¹ = 1 := by simp [PowerSeries.constantCoeff_inv, hw1]
  set e := wq⁻¹ with hedef
  set N : PowerSeries ℂ_[p] := C W.a₁ * X + C W.a₃ * X ^ 3 * wq - 2 with hN
  have h2 : constantCoeff (2 : PowerSeries ℂ_[p]) = 2 := map_ofNat _ 2
  have hω : omegaW W wq * (wq * N) = -2 * wq - X * PowerSeries.derivative wq := by
    have hu : (wq * N)⁻¹ * (wq * N) = 1 :=
      PowerSeries.inv_mul_cancel _ (by simp [hN, hw1, h2])
    have : omegaW W wq = (-2 * wq - X * PowerSeries.derivative wq) * (wq * N)⁻¹ := by
      rw [← dX_eq_derivative]; rfl
    rw [this, mul_assoc, hu, mul_one]
  have hde : wq * PowerSeries.derivative e + e * PowerSeries.derivative wq = 0 := by
    have := congrArg (PowerSeries.derivative (R := ℂ_[p])) he
    rw [Derivation.leibniz] at this
    simpa using this
  set r := W.b₂ / 12 with hr
  have hq : lineSer e (-r) = e + C r * X ^ 2 := by simp [lineSer]
  have hdq : PowerSeries.derivative (e + C r * X ^ 2) = PowerSeries.derivative e + C r * (2 * X) := by
    rw [map_add (f := _), Derivation.leibniz, Derivation.leibniz_pow]; simp
  have hW : wq = 1 + C W.a₁ * X * wq + C W.a₂ * X ^ 2 * wq + C W.a₃ * X ^ 3 * wq ^ 2 +
    C W.a₄ * X ^ 4 * wq ^ 2 + C W.a₆ * X ^ 6 * wq ^ 3 := hwq
  have hW' : e ^ 2 = e ^ 3 + C W.a₁ * X * e ^ 2 + C W.a₂ * X ^ 2 * e ^ 2 + C W.a₃ * X ^ 3 * e +
      C W.a₄ * X ^ 4 * e + C W.a₆ * X ^ 6 := by
    linear_combination e ^ 3 * hW + (-e ^ 2 + C W.a₁ * X * e ^ 2 + C W.a₂ * X ^ 2 * e ^ 2 +
      (C W.a₃ * X ^ 3 + C W.a₄ * X ^ 4) * e * (wq * e + 1) +
      C W.a₆ * X ^ 6 * ((wq * e) ^ 2 + wq * e + 1)) * he
  have hNe : N * e = C W.a₁ * X * e + C W.a₃ * X ^ 3 - 2 * e := by
    rw [hN]; linear_combination C W.a₃ * X ^ 3 * he
  have c2 : (12 : PowerSeries ℂ_[p]) * C r = C W.a₁ ^ 2 + 4 * C W.a₂ := by
    have : 12 * r = W.a₁ ^ 2 + 4 * W.a₂ := by rw [hr, WeierstrassCurve.b₂]; ring
    simpa only [map_mul, map_add (f := _), map_pow, map_ofNat] using congrArg (C (R := ℂ_[p])) this
  have c4 : (C (W.c₄ / 12) : PowerSeries ℂ_[p]) =
      12 * C r ^ 2 - 2 * (2 * C W.a₄ + C W.a₁ * C W.a₃) := by
    have : W.c₄ / 12 = 12 * r ^ 2 - 2 * (2 * W.a₄ + W.a₁ * W.a₃) := by
      rw [hr, WeierstrassCurve.c₄, WeierstrassCurve.b₄]; ring
    rw [this]; simp only [map_mul, map_add (f := _), map_sub, map_pow, map_ofNat]
  have c6 : (C (W.c₆ / 216) : PowerSeries ℂ_[p]) =
      2 * C r * (2 * C W.a₄ + C W.a₁ * C W.a₃) - 8 * C r ^ 3 - (C W.a₃ ^ 2 + 4 * C W.a₆) := by
    have : W.c₆ / 216 = 2 * r * (2 * W.a₄ + W.a₁ * W.a₃) - 8 * r ^ 3 - (W.a₃ ^ 2 + 4 * W.a₆) := by
      rw [hr, WeierstrassCurve.c₆, WeierstrassCurve.b₄, WeierstrassCurve.b₆]; ring
    rw [this]; simp only [map_mul, map_add (f := _), map_sub, map_pow, map_ofNat]
  have main := subst_eq_of_equation (m := m) (q := e + C r * X ^ 2) (M := N * e) hP hm1
    (by simp [he1])
    (by
      rw [← hm, derivative_flog, hdq]
      linear_combination -e ^ 2 * hω + X * e * hde +
        (omegaW W wq * N * e + 2 * e - X * PowerSeries.derivative e) * he)
    (by
      rw [hNe, c4, c6]
      linear_combination 4 * hW' - X ^ 2 * e ^ 2 * c2)
  rw [hq, hm, main]
  ring

end GlobalTheory.WpForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WittIdxOfParallelSig
section
noncomputable section

open NumberField Matrix Formalism.BasicNotions Formalism.BasicNotions.TH

namespace GlobalTheory.ParallelWitt

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem embedding_star (τ : E →+* ℂ) (a : E) : τ (star a) = star (τ a) :=
  IsCMField.complexEmbedding_complexConj E τ a

theorem form_eq {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) (x y : Fin S.rank → E) :
    S.hT (S.frame.equivFun.symm x) (S.frame.equivFun.symm y) = star x ⬝ᵥ (S.gram *ᵥ y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Module.Basis.equivFun_symm_apply, map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, RingHom.id_apply, starRingEnd_apply, dotProduct, mulVec, HSpace.gram, Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem finrank_le (S : HSpace E) {p q : ℕ} (τ : E →+* ℂ) (hs : Formalism.UG.HasSignature (S.gram.map τ) p q)
    (U : Submodule E S.V) (hU : ∀ x ∈ U, ∀ y ∈ U, S.hT x y = 0) : Module.finrank E U ≤ q := by
  let b := Module.finBasis E U
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective U.subtype U.ker_subtype
  let M := LinearMap.toMatrix b S.frame U.subtype
  let L := LinearMap.toMatrix S.frame b g
  have hL : L * M = 1 := by
    rw [← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
  have hb : ∀ i, (b i : S.V) = ∑ a, M a i • S.frame a := by
    intro i
    simp only [M, LinearMap.toMatrix_apply, Submodule.subtype_apply]
    exact (S.frame.sum_repr _).symm
  have h : Mᴴ * S.gram * M = 0 := by
    ext i j
    have h0 := hU _ (b i).2 _ (b j).2
    rw [hb i, hb j] at h0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      starRingEnd_apply] at h0
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, HSpace.gram, Matrix.zero_apply]
    rw [← h0]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  refine (GlobalTheory.WittSignature.le_of_isotropic_signature _ hs (M.map τ) (L.map τ) ?_ ?_).2
  · rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero τ) (map_one τ)]
  · have : (M.map τ)ᴴ = (Mᴴ).map τ := by
      ext i j
      simp [Matrix.conjTranspose_apply, embedding_star]
    rw [this, ← Matrix.map_mul, ← Matrix.map_mul, h, Matrix.map_zero _ (map_zero τ)]

end CM

open GlobalTheory.IndefiniteRowSideFullHecke.WittIndexParallel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.ParallelWitt

end
end

