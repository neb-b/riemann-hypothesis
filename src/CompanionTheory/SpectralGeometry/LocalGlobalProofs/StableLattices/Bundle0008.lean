module

public import Mathlib
public import Formalism.FormalDegreeBessel.StatementDS
public import GroundTheory.AutomorphicForms.Cartan
public import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
public import Mathlib.Data.Fin.Tuple.Sort

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CapelliPolynomialPermutationMatch
section
noncomputable section

namespace GlobalTheory.CompanionTheory.CharOfLowK

theorem roots_prod_X_sub_C {n : ℕ} (k : Fin n → ℂ) :
    (∏ a, (Polynomial.X - Polynomial.C (k a))).roots = Multiset.map k Finset.univ.val := by
  have hprod : (∏ a, (Polynomial.X - Polynomial.C (k a))) =
      ((Multiset.map k Finset.univ.val).map fun x => Polynomial.X - Polynomial.C x).prod := by
    rw [Multiset.map_map]
    rfl
  rw [hprod, Polynomial.roots_multiset_prod_X_sub_C]

theorem exists_perm_of_capelliPolynomial_eq {n : ℕ} (f g : Fin n → ℂ)
    (h : ∀ Y, Formalism.QuantumDeterminants.capP f Y = Formalism.QuantumDeterminants.capP g Y) :
    ∃ τ : Equiv.Perm (Fin n), ∀ a, f a = g (τ a) := by
  classical
  have hp : (∏ a, (Polynomial.X - Polynomial.C (-f a))) = ∏ a, (Polynomial.X - Polynomial.C (-g a)) := by
    apply Polynomial.funext
    intro Y
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_neg_eq_add]
    exact h Y
  have hmap : Multiset.map (fun a => -f a) Finset.univ.val = Multiset.map (fun a => -g a) Finset.univ.val := by
    rw [← roots_prod_X_sub_C (fun a => -f a), ← roots_prod_X_sub_C (fun a => -g a)]
    exact congrArg Polynomial.roots hp
  have hcard : ∀ c : ℂ, Fintype.card {a // -f a = c} = Fintype.card {a // -g a = c} := by
    intro c
    have hc := congrArg (Multiset.count c) hmap
    rw [Multiset.count_map, Multiset.count_map] at hc
    rw [Fintype.card_subtype, Fintype.card_subtype, Finset.card, Finset.card, Finset.filter_val,
      Finset.filter_val]
    convert hc using 3 <;> simp [eq_comm]
  let e : ∀ c, {a // -f a = c} ≃ {a // -g a = c} := fun c => Fintype.equivOfCardEq (hcard c)
  let τ : Equiv.Perm (Fin n) :=
    ((Equiv.sigmaFiberEquiv (fun a => -f a)).symm.trans (Equiv.sigmaCongrRight e)).trans
      (Equiv.sigmaFiberEquiv (fun a => -g a))
  refine ⟨τ, fun a => ?_⟩
  have key : -g (τ a) = -f a := (e (-f a) ⟨a, rfl⟩).2
  exact neg_inj.mp key.symm

end GlobalTheory.CompanionTheory.CharOfLowK

namespace GlobalTheory.CompanionTheory.RgCOBlock

open Finset Polynomial

theorem exists_linear_factors_indexed {ι : Type} [DecidableEq ι] (F : Finset ι) :
    ∀ P : ℂ[X], P.Monic → P.natDegree = F.card → ∃ r : ι → ℂ, P = ∏ a ∈ F, (X - C (r a)) := by
  induction F using Finset.induction_on with
  | empty =>
    intro P hm hd
    refine ⟨fun _ => 0, ?_⟩
    simpa using eq_one_of_monic_natDegree_zero hm (by simpa using hd)
  | insert a F ha ih =>
    intro P hm hd
    rw [Finset.card_insert_of_notMem ha] at hd
    have hdeg : P.degree ≠ 0 := by
      intro h
      have : P.natDegree = 0 := natDegree_eq_zero_iff_degree_le_zero.mpr h.le
      omega
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root P hdeg
    obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr hz
    have hmQ : Q.Monic := by
      have h := hm
      rw [hQ] at h
      exact (monic_X_sub_C z).of_mul_monic_left h
    have hdQ : Q.natDegree = F.card := by
      have h := congrArg natDegree hQ
      rw [(monic_X_sub_C z).natDegree_mul hmQ, natDegree_X_sub_C] at h
      omega
    obtain ⟨r, hr⟩ := ih Q hmQ hdQ
    refine ⟨Function.update r a z, ?_⟩
    rw [Finset.prod_insert ha, Function.update_self, hQ, hr]
    congr 1
    refine Finset.prod_congr rfl fun b hb => ?_
    rw [Function.update_of_ne (fun h : b = a => ha (h ▸ hb))]

theorem exists_perm_of_monic_factors (n M : ℕ) (lev : Fin n → ℕ) (χ : Fin n → ℂ) (P : Fin M → ℂ[X]) (s : Fin M → ℂ)
    (hlev : ∀ a, lev a < M)
    (hP : ∀ i, (P i).Monic ∧ (P i).natDegree = (univ.filter fun a => lev a = (i : ℕ)).card)
    (hcap : ∀ Y : ℂ, ∏ i, (P i).eval (Y + s i) = Formalism.QuantumDeterminants.capP χ Y) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin M,
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), χ (σ a) =
        (P i).nextCoeff + ((univ.filter fun a => lev a = (i : ℕ)).card : ℂ) * s i := by
  choose r hr using fun i => exists_linear_factors_indexed _ (P i) (hP i).1 (hP i).2
  let lv : Fin n → Fin M := fun a => ⟨lev a, hlev a⟩
  let g : Fin n → ℂ := fun a => s (lv a) - r (lv a) a
  have hfil : ∀ i : Fin M, (univ.filter fun a => lev a = (i : ℕ)) = univ.filter fun a => lv a = i := by
    intro i
    ext a
    simp [lv, Fin.ext_iff]
  have hg : ∀ i : Fin M, ∀ a ∈ univ.filter (fun a => lev a = (i : ℕ)), g a = s i - r i a := by
    intro i a ha
    have : lv a = i := by
      rw [hfil] at ha
      exact (Finset.mem_filter.mp ha).2
    simp only [g, this]
  have hpoly : ∀ Y, Formalism.QuantumDeterminants.capP g Y = Formalism.QuantumDeterminants.capP χ Y := by
    intro Y
    rw [← hcap Y]
    unfold Formalism.QuantumDeterminants.capP
    rw [← Finset.prod_fiberwise univ lv]
    refine Finset.prod_congr rfl fun i _ => ?_
    conv_rhs => rw [hr i, eval_prod]
    rw [hfil i]
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [← hfil i] at ha
    rw [hg i a ha]
    simp only [eval_sub, eval_X, eval_C]
    ring
  obtain ⟨σ, hσ⟩ := GlobalTheory.CompanionTheory.CharOfLowK.exists_perm_of_capelliPolynomial_eq g χ hpoly
  refine ⟨σ, fun i => ?_⟩
  have h1 : ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), χ (σ a) =
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), (s i - r i a) :=
    Finset.sum_congr rfl fun a ha => by rw [← hσ a, hg i a ha]
  rw [h1, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  conv_rhs => rw [hr i, prod_X_sub_C_nextCoeff]
  ring

end GlobalTheory.CompanionTheory.RgCOBlock
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanExists
section
namespace GlobalTheory.CompanionTheory.Dblock.CartanDVR

open Matrix

theorem cartan_exists : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
    [Algebra R K] [IsFractionRing R K] (n : ℕ) (ϖ : R), Irreducible ϖ →
    ∀ g : Matrix (Fin n) (Fin n) K, IsUnit g.det →
      ∃ (u v : Matrix (Fin n) (Fin n) R) (a : Fin n → ℤ), IsUnit u.det ∧ IsUnit v.det ∧ Antitone a ∧
        g = u.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (a i)) *
          v.map (algebraMap R K) := by
  intro R K _ _ _ _ _ _ n ϖ hϖ g hg
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : Fin n × Fin n => g p.1 p.2)
  have hb0 : (b : R) ≠ 0 := nonZeroDivisors.ne_zero b.2
  choose A' hA' using hb
  let A : Matrix (Fin n) (Fin n) R := Matrix.of fun i j => A' (i, j)
  have hAg : A.map (algebraMap R K) = algebraMap R K (b : R) • g := by
    ext i j
    simpa [A, Algebra.smul_def] using hA' (i, j)
  have hbK : algebraMap R K (b : R) ≠ 0 := fun h => hb0 (hinj (by simpa using h))
  have hA : A.det ≠ 0 := by
    intro h
    have h1 : (A.map (algebraMap R K)).det = 0 := by
      have := RingHom.map_det (algebraMap R K) A
      rw [h, map_zero] at this
      simpa using this.symm
    rw [hAg, Matrix.det_smul] at h1
    exact (mul_ne_zero (pow_ne_zero _ hbK) hg.ne_zero) h1
  obtain ⟨P, Q, e, he, hPQ⟩ := GroundTheory.Automorphic.Cartan.exists_eq_mul_diagonal_pow_mul hϖ A hA
  obtain ⟨c, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  have hϖK : algebraMap R K ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (by simpa using h))
  have hwK : algebraMap R K (w : R) ≠ 0 := fun h => w.ne_zero (hinj (by simpa using h))
  have hPd : IsUnit (P : Matrix (Fin n) (Fin n) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 P.isUnit
  have hQd : IsUnit (Q : Matrix (Fin n) (Fin n) R).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 Q.isUnit
  refine ⟨((w⁻¹ : Rˣ) : R) • (P : Matrix (Fin n) (Fin n) R), Q, fun i => (e i : ℤ) - c, ?_, hQd, ?_, ?_⟩
  · rw [Matrix.det_smul]
    exact ((Units.isUnit _).pow _).mul hPd
  · intro i j hij
    have := he hij
    simp only
    omega
  · have hwinv : algebraMap R K ((w⁻¹ : Rˣ) : R) = (algebraMap R K (w : R))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul]
      simp
    have hdiag : Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ ((e i : ℤ) - c)) =
        ((algebraMap R K ϖ) ^ c)⁻¹ • (Matrix.diagonal (fun i => ϖ ^ e i)).map (algebraMap R K) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [zpow_sub₀ hϖK, div_eq_mul_inv, mul_comm]
      · simp [Matrix.diagonal_apply_ne _ hij]
    have hmap : A.map (algebraMap R K) = (P : Matrix (Fin n) (Fin n) R).map (algebraMap R K) *
        (Matrix.diagonal (fun i => ϖ ^ e i)).map (algebraMap R K) *
        (Q : Matrix (Fin n) (Fin n) R).map (algebraMap R K) := by
      rw [hPQ]
      simp only [Matrix.map_mul]
    have hsm : (((w⁻¹ : Rˣ) : R) • (P : Matrix (Fin n) (Fin n) R)).map (algebraMap R K) =
        (algebraMap R K (w : R))⁻¹ • (P : Matrix (Fin n) (Fin n) R).map (algebraMap R K) := by
      ext i j
      simp [hwinv]
    rw [hsm, hdiag, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, smul_smul, ← hmap, hAg,
      smul_smul, hw]
    have : (algebraMap R K (w : R))⁻¹ * ((algebraMap R K ϖ) ^ c)⁻¹ *
        algebraMap R K ((w : R) * ϖ ^ c) = 1 := by
      rw [map_mul, map_pow]
      field_simp
    rw [this, one_smul]

end GlobalTheory.CompanionTheory.Dblock.CartanDVR
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
section
noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

def IsUnif (p : Lˣ) : Prop := ‖(p : L)‖ < 1 ∧ ∀ x : L, x ≠ 0 → ∃ a : ℤ, ‖x‖ = ‖(p : L)‖ ^ a

theorem entry_mul {A B : Matrix (Fin n) (Fin n) L} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, ‖A i j‖ ≤ a) (hB : ∀ i j, ‖B i j‖ ≤ b) (i j : Fin n) : ‖(A * B) i j‖ ≤ a * b := by
  rw [Matrix.mul_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb) fun l _ => ?_
  rw [norm_mul]
  exact mul_le_mul (hA i l) (hB l j) (norm_nonneg _) ha

theorem entry_mul_sub_one {A B : Matrix (Fin n) (Fin n) L} {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1)
    (hA : ∀ i j, ‖(A - 1) i j‖ ≤ r) (hB : ∀ i j, ‖(B - 1) i j‖ ≤ r) (i j : Fin n) :
    ‖(A * B - 1) i j‖ ≤ r := by
  have e : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
  rw [e, Matrix.add_apply, Matrix.add_apply]
  have h := entry_mul h0 h0 hA hB i j
  have h2 : r * r ≤ r := by nlinarith
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hB i j))
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h.trans h2) (hA i j))


variable (L n) in
def congK (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) : Subgroup (GL (Fin n) L) where
  carrier := {k | ∀ i j, ‖((k : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r ∧
    ‖(((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r}
  mul_mem' := by
    intro a b ha hb i j
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact entry_mul_sub_one h0 h1 (fun i j => (ha i j).1) (fun i j => (hb i j).1) i j
    · rw [_root_.mul_inv_rev, Units.val_mul]
      exact entry_mul_sub_one h0 h1 (fun i j => (hb i j).2) (fun i j => (ha i j).2) i j
  one_mem' := by
    intro i j
    simp [h0]
  inv_mem' := by
    intro a ha i j
    simpa [and_comm] using ha i j

theorem mem_congK {r : ℝ} {h0 : 0 ≤ r} {h1 : r ≤ 1} {k : GL (Fin n) L} :
    k ∈ congK L n r h0 h1 ↔ ∀ i j, ‖((k : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r ∧
      ‖(((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := Iff.rfl

def dPow (p : Lˣ) (a : Fin n → ℤ) : GL (Fin n) L where
  val := diagonal fun i => ((p ^ a i : Lˣ) : L)
  inv := diagonal fun i => ((p ^ (-a i) : Lˣ) : L)
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← Units.val_mul, _root_.zpow_neg, mul_inv_cancel, Units.val_one]
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← Units.val_mul, _root_.zpow_neg, inv_mul_cancel, Units.val_one]

theorem dPow_val (p : Lˣ) (a : Fin n → ℤ) :
    ((dPow p a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = diagonal fun i => ((p ^ a i : Lˣ) : L) := rfl

theorem dPow_add (p : Lˣ) (a b : Fin n → ℤ) : (dPow p (a + b) : GL (Fin n) L) = dPow p a * dPow p b := by
  apply Units.ext
  rw [Units.val_mul, dPow_val, dPow_val, dPow_val, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [Pi.add_apply, _root_.zpow_add, Units.val_mul]

theorem dPow_zero (p : Lˣ) : (dPow p (0 : Fin n → ℤ) : GL (Fin n) L) = 1 := by
  apply Units.ext
  simp [dPow_val]

def tExp (n : ℕ) (i : Fin (n + 2)) : Fin n → ℤ :=
  fun j => if (i : ℕ) = n + 1 then -1 else if (j : ℕ) < i then 1 else 0

def tGen (p : Lˣ) (i : Fin (n + 2)) : GL (Fin n) L := dPow p (tExp n i)

end GlobalTheory.CompanionTheory.CartGL
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniqueParam
section
open Finset

namespace CompanionTheory.RgExh.Fin

def ArrCount : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (χ χ' : Fin n → ℂ), Function.Injective χ → Function.Injective χ' →
    (∀ a, (χ a).im = 0 ∧ ∃ m : ℤ, (χ a).re - ((n : ℝ) - 1) / 2 = m) →
    (∀ a, (χ' a).im = 0 ∧ ∃ m : ℤ, (χ' a).re - ((n : ℝ) - 1) / 2 = m) →
    ∃ (A : Finset (Equiv.Perm (Fin n) × (Fin n → ℝ))) (A' : Finset (Equiv.Perm (Fin n) × (Fin n → ℝ))),
      A.card = A'.card ∧
      (∀ d, d ∈ A ↔ (Formalism.QuantumDeterminants.IsHCParam d.2 ∧ (∀ a b, a < b → ε (d.1 a) = ε (d.1 b) → d.1 a < d.1 b) ∧
        ∃ τ : Equiv.Perm (Fin n), ∀ a, ((d.2 a : ℝ) : ℂ) = χ (τ a))) ∧
      (∀ d, d ∈ A' ↔ (Formalism.QuantumDeterminants.IsHCParam d.2 ∧ (∀ a b, a < b → ε (d.1 a) = ε (d.1 b) → d.1 a < d.1 b) ∧
        ∃ τ : Equiv.Perm (Fin n), ∀ a, ((d.2 a : ℝ) : ℂ) = χ' (τ a)))

end CompanionTheory.RgExh.Fin

namespace GlobalTheory.CompanionTheory.ArrCount

theorem exists_unique_param {n : ℕ} (χ : Fin n → ℂ) (hχ : Function.Injective χ)
    (h : ∀ a, (χ a).im = 0 ∧ ∃ m : ℤ, (χ a).re - ((n : ℝ) - 1) / 2 = m) :
    ∃ μ : Fin n → ℝ, ∀ m : Fin n → ℝ,
      (Formalism.QuantumDeterminants.IsHCParam m ∧ ∃ τ : Equiv.Perm (Fin n), ∀ a, ((m a : ℝ) : ℂ) = χ (τ a)) ↔ m = μ := by
  have hval : ∀ a, (((χ a).re : ℝ) : ℂ) = χ a := fun a => Complex.ext (by simp) (by simp [(h a).1])
  let r : Fin n → ℝ := fun a => (χ a).re
  have hr : Function.Injective r := fun a b hab => hχ (by
    rw [← hval a, ← hval b]; exact congrArg _ hab)
  let τ₀ : Equiv.Perm (Fin n) := Tuple.sortDesc r
  have hanti : StrictAnti (r ∘ τ₀) :=
    (Tuple.antitone_sortDesc r).strictAnti_of_injective (hr.comp τ₀.injective)
  refine ⟨r ∘ τ₀, fun m => ⟨?_, ?_⟩⟩
  · rintro ⟨⟨hm, -⟩, τ, hτ⟩
    have hmr : m = r ∘ τ := by
      funext a
      change m a = (χ (τ a)).re
      simpa only [Complex.ofReal_re] using congrArg Complex.re (hτ a)
    rw [hmr] at hm ⊢
    exact Tuple.unique_antitone hm.antitone hanti.antitone
  · rintro rfl
    exact ⟨⟨hanti, fun a => (h _).2⟩, τ₀, fun a => hval _⟩

theorem arrCount : CompanionTheory.RgExh.Fin.ArrCount := by
  classical
  intro n ε χ χ' hχ hχ' h h'
  obtain ⟨μ, hμ⟩ := exists_unique_param χ hχ h
  obtain ⟨μ', hμ'⟩ := exists_unique_param χ' hχ' h'
  let P : Finset (Equiv.Perm (Fin n)) :=
    univ.filter fun s => ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b
  have key : ∀ (ψ : Fin n → ℂ) (ν : Fin n → ℝ),
      (∀ m : Fin n → ℝ, (Formalism.QuantumDeterminants.IsHCParam m ∧
        ∃ τ : Equiv.Perm (Fin n), ∀ a, ((m a : ℝ) : ℂ) = ψ (τ a)) ↔ m = ν) →
      ∀ d : Equiv.Perm (Fin n) × (Fin n → ℝ), d ∈ P.image (fun s => (s, ν)) ↔
        (Formalism.QuantumDeterminants.IsHCParam d.2 ∧ (∀ a b, a < b → ε (d.1 a) = ε (d.1 b) → d.1 a < d.1 b) ∧
          ∃ τ : Equiv.Perm (Fin n), ∀ a, ((d.2 a : ℝ) : ℂ) = ψ (τ a)) := by
    rintro ψ ν hν ⟨s, m⟩
    constructor
    · intro hd
      obtain ⟨t, ht, e⟩ := mem_image.1 hd
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      obtain ⟨h1, h2⟩ := (hν _).2 rfl
      exact ⟨h1, (mem_filter.1 ht).2, h2⟩
    · rintro ⟨h1, h2, h3⟩
      have e : m = ν := (hν m).1 ⟨h1, h3⟩
      exact mem_image.2 ⟨s, mem_filter.2 ⟨mem_univ _, h2⟩, by simp [e]⟩
  have hinj : ∀ ν : Fin n → ℝ, Function.Injective
      (fun s : Equiv.Perm (Fin n) => (s, ν)) := fun ν a b e => (Prod.mk.inj e).1
  refine ⟨P.image fun s => (s, μ), P.image fun s => (s, μ'), ?_, key χ μ hμ, key χ' μ' hμ'⟩
  rw [card_image_of_injective _ (hinj μ), card_image_of_injective _ (hinj μ')]

end GlobalTheory.CompanionTheory.ArrCount
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FixedVectorStatement
section
open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.RgFl

theorem exists_least_norm_unique {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {C : Set E} (hne : C.Nonempty) (hcl : IsClosed C) (hconv : Convex ℝ C) :
    ∃ u ∈ C, ∀ w ∈ C, ‖u‖ ≤ ‖w‖ ∧ (‖w‖ ≤ ‖u‖ → w = u) := by
  obtain ⟨u, hu, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hconv (0 : E)
  have hin := (norm_eq_iInf_iff_real_inner_le_zero hconv hu).1 hmin
  refine ⟨u, hu, fun w hw => ?_⟩
  have h1 := hin w hw
  have h3 : inner ℝ (0 - u) (w - u) = ‖u‖ ^ 2 - inner ℝ w u := by
    rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq,
      real_inner_comm w u]
    ring
  have h2 : ‖w - u‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w u + ‖u‖ ^ 2 := norm_sub_sq_real w u
  have h4 : inner ℝ w u ≤ ‖w‖ * ‖u‖ := real_inner_le_norm w u
  have h5 : ‖u‖ ^ 2 ≤ ‖w‖ * ‖u‖ := by linarith
  constructor
  · rcases (norm_nonneg u).eq_or_lt with h0 | h0
    · rw [← h0]; exact norm_nonneg w
    · nlinarith
  · intro hle
    have h6 : ‖w‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      have := norm_nonneg w
      nlinarith
    have h7 : ‖w - u‖ ^ 2 ≤ 0 := by nlinarith
    have h8 : ‖w - u‖ = 0 := by
      have := norm_nonneg (w - u)
      nlinarith
    exact sub_eq_zero.1 (norm_eq_zero.1 h8)

theorem stFixVec : StFixVec := by
  intro G H _ _ _ _ _ _ _ σ hiso hcont
  obtain ⟨x, hx⟩ := exists_ne (0 : H)
  obtain ⟨v, hv⟩ : ∃ v : H, ‖v‖ = 1 :=
    ⟨((‖x‖ : ℂ)⁻¹) • x, by
      have : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
      simp [norm_smul, this]⟩
  have hopen : IsOpen {g : G | ‖σ g v - v‖ < 1 / 2} :=
    isOpen_lt (((hcont v).sub continuous_const).norm) continuous_const
  have hone : (1 : G) ∈ {g : G | ‖σ g v - v‖ < 1 / 2} := by simp
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean _ (hopen.mem_nhds hone)
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  set A : Set H := Set.range (fun k : V => σ (k : G) v) with hA
  set C : Set H := closure (convexHull ℝ A) with hC
  have hvA : v ∈ A := ⟨1, by simp⟩
  have hCne : C.Nonempty := ⟨v, subset_closure (subset_convexHull ℝ A hvA)⟩
  have hCconv : Convex ℝ C := (convex_convexHull ℝ A).closure
  have hCball : C ⊆ Metric.closedBall v (1 / 2) := by
    refine closure_minimal (convexHull_min ?_ (convex_closedBall _ _)) Metric.isClosed_closedBall
    rintro _ ⟨k, rfl⟩
    have := hV k.2
    simp only [Set.mem_setOf_eq] at this
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact this.le
  have hstable : ∀ k : V, ∀ y ∈ C, σ (k : G) y ∈ C := by
    intro k y hy
    have hmaps : Set.MapsTo (σ (k : G)) (convexHull ℝ A) (convexHull ℝ A) := by
      have hconvpre : Convex ℝ ((σ (k : G)).toLinearMap.restrictScalars ℝ ⁻¹' convexHull ℝ A) :=
        (convex_convexHull ℝ A).linear_preimage _
      have hsub : A ⊆ (σ (k : G)).toLinearMap.restrictScalars ℝ ⁻¹' convexHull ℝ A := by
        rintro _ ⟨l, rfl⟩
        refine subset_convexHull ℝ A ⟨k * l, ?_⟩
        simp
      exact fun z hz => convexHull_min hsub hconvpre hz
    exact map_mem_closure (σ (k : G)).continuous hy hmaps
  obtain ⟨u, huC, hu⟩ := exists_least_norm_unique hCne isClosed_closure hCconv
  refine ⟨V.toSubgroup, u, V.isOpen, ?_, ?_⟩
  · rintro rfl
    have := hCball huC
    rw [Metric.mem_closedBall, dist_eq_norm, zero_sub, norm_neg, hv] at this
    norm_num at this
  · intro k hk
    exact (hu _ (hstable ⟨k, hk⟩ u huC)).2 (hiso k u).le

end GlobalTheory.CompanionTheory.RgFl
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PairingStatement
section
open CompanionTheory.Rg.Fl

namespace GlobalTheory.CompanionTheory.HeckePair

theorem stPair : StPair := by
  intro G _ _ _ K hKo hKc g
  have : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKo
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hcont : Continuous fun k : K => (((k : G) * g : G) : G ⧸ K) :=
    (QuotientGroup.continuous_mk (N := K)).comp (continuous_subtype_val.mul continuous_const)
  have hfin : (Set.range fun k : K => (((k : G) * g : G) : G ⧸ K)).Finite :=
    (isCompact_range hcont).finite_of_discrete
  refine hfin.subset ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨k, rfl⟩

end GlobalTheory.CompanionTheory.HeckePair
end

