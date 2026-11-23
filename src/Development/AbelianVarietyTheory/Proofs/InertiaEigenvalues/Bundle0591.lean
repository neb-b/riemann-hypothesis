module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightZeroPotentiallySemistableOfSenTheorem
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.PMon

theorem fr_zero_apply (l : ℕ) [Fact l.Prime] (c : ↥(MaximalUnramifiedExtension l)) : fr l 0 c = c := by
  unfold fr
  rw [pow_zero]
  rfl

theorem senStep : SenStep := by
  intro l _ P AI T n _ _ K r ρ hρ hF
  classical
  obtain ⟨ρ₀, p, hc₀, hp, hρ₀⟩ := _root_.GlobalTheory.PMon.weilRes l n K r ρ hρ
  obtain ⟨S, θ, hS, -, -, hθΩ, hθg⟩ := _root_.GlobalTheory.PMon.exists_theta_deRhamFilZero_surjective_alt l P AI T
  choose U hU hUg using hF
  have hΩ : ∀ y : Om l, algebraMap (Om l) P.R.BdR y ∈ S := fun y => (hθΩ y).1
  have hkd : ∀ c : ↥(MaximalUnramifiedExtension l), kd P c ∈ S := fun c => hΩ _
  let kS : ↥(MaximalUnramifiedExtension l) →+* ↥S := (kd P).codRestrict S hkd
  let Φ := (kd P).mapMatrix (m := n × Fin r)
  let ΦS := kS.mapMatrix (m := n × Fin r)
  let ιS := S.subtype.mapMatrix (m := n × Fin r)
  have hinj : Function.Injective ιS := Matrix.map_injective Subtype.val_injective
  have hιΦ : ∀ A, ιS (ΦS A) = Φ A := fun A => by ext i j; rfl
  have hpp : Φ (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * Φ ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hpp' : Φ ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * Φ (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]

  have hfix : ∀ g : ↥(GK K), (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR).mapMatrix (Φ p) = Φ p := by
    intro g
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Φ]
    have hK : ((((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l)) ∈ K.1 := hρ.le _ (hp i j)
    have hg := (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ hK
    show P.actQdR (g : GQ l) (algebraMap (Om l) P.R.BdR _) = algebraMap (Om l) P.R.BdR _
    rw [P.actQdR_Om]
    exact congrArg _ hg

  let Ut : Matrix (n × Fin r) (n × Fin r) P.R.BdR := Matrix.blockDiagonal fun m => (U m : Matrix n n P.R.BdR)
  let Ut' : Matrix (n × Fin r) (n × Fin r) P.R.BdR := Matrix.blockDiagonal fun m => ((U m)⁻¹ : GL n P.R.BdR)
  have hUU : Ut * Ut' = 1 := by
    simp only [Ut, Ut']
    rw [← Matrix.blockDiagonal_mul]
    have : (fun m => (U m : Matrix n n P.R.BdR) * ((U m)⁻¹ : GL n P.R.BdR)) = fun _ => 1 := by
      funext m; exact Units.mul_inv (U m)
    rw [this]
    exact Matrix.blockDiagonal_one
  let US : Fin r → Matrix n n ↥S := fun m => Matrix.of fun i j => ⟨(U m : Matrix n n P.R.BdR) i j, (hS _).2 ((hU m).1 i j)⟩
  let VS : Fin r → Matrix n n ↥S := fun m => Matrix.of fun i j =>
    ⟨((U m)⁻¹ : GL n P.R.BdR) i j, (hS _).2 ((hU m).2 i j)⟩
  let XS := ΦS ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * Matrix.blockDiagonal US
  let YS := Matrix.blockDiagonal VS * ΦS (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))
  have hX : ιS XS = Φ ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * Ut := by
    simp only [XS, map_mul, hιΦ]
    congr 1
    simp only [ιS, RingHom.mapMatrix_apply, Ut]
    rw [Matrix.blockDiagonal_map _ _ (by simp)]
    rfl
  have hY : ιS YS = Ut' * Φ (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) := by
    simp only [YS, map_mul, hιΦ]
    congr 1
    simp only [ιS, RingHom.mapMatrix_apply, Ut']
    rw [Matrix.blockDiagonal_map _ _ (by simp)]
    rfl
  have hXY : XS * YS = 1 := by
    apply hinj
    rw [map_mul, hX, hY, map_one, mul_assoc, ← mul_assoc Ut, hUU, one_mul, hpp']

  have hmain : ∀ g : ↥(GK K),
      Φ ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))) *
        (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR).mapMatrix (ιS XS) = ιS XS := by
    intro g
    set Ψ := (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR).mapMatrix (m := n × Fin r)
    set pk := Φ (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))
    set pki := Φ ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))
    set R₀ := Φ ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)))
    set Dk := Φ (Matrix.blockDiagonal fun m : Fin r => (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m))
    have hW : pk * R₀ = Dk * pk := by
      simp only [pk, R₀, Dk, ← map_mul, hρ₀ g]
    have hD : Dk * Ψ Ut = Ut := by
      have h1 : Dk = Matrix.blockDiagonal fun m : Fin r => matD P ρ m g := by
        simp only [Dk, Φ, RingHom.mapMatrix_apply]
        rw [Matrix.blockDiagonal_map _ _ (by simp)]
        rfl
      have h2 : Ψ Ut = Matrix.blockDiagonal fun m : Fin r => (U m : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) := by
        simp only [Ψ, Ut, RingHom.mapMatrix_apply]
        rw [Matrix.blockDiagonal_map _ _ (by simp)]
        rfl
      rw [h1, h2, ← Matrix.blockDiagonal_mul]
      congr 1
      funext m
      rw [hUg m g]
      simp
    have hΨpki : Ψ pki = pki := by
      have hΨp : Ψ pk = pk := hfix g
      calc Ψ pki = Ψ pki * (pk * pki) := by rw [hpp, mul_one]
        _ = Ψ (pki * pk) * pki := by rw [map_mul, hΨp, mul_assoc]
        _ = pki := by rw [hpp', map_one, one_mul]
    have hR : R₀ = pki * Dk * pk := by
      calc R₀ = pki * (pk * R₀) := by rw [← mul_assoc, hpp', one_mul]
        _ = pki * Dk * pk := by rw [hW, mul_assoc]
    rw [hX, map_mul, hΨpki, hR]
    calc pki * Dk * pk * (pki * Ψ Ut) = pki * (Dk * Ψ Ut) := by
          simp only [mul_assoc]
          rw [← mul_assoc pk pki, hpp, one_mul]
      _ = pki * Ut := by rw [hD]

  let actS : GQ l → ↥S → ↥S := fun g x => ⟨P.actQdR g x, (hθg g x).1⟩
  let qS : ℚ_[l] → ↥S := fun q => kS (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q)
  have hES : ∀ g : ↥(GK K), (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map qS * XS.map (actS (g : GQ l)) = XS := by
    intro g
    apply hinj
    have e1 : ιS ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map qS) =
        Φ ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))) := by ext i j; rfl
    have e2 : ιS (XS.map (actS (g : GQ l))) = (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR).mapMatrix (ιS XS) := by
      ext i j; rfl
    rw [map_mul, e1, e2]
    exact hmain g
  let Θ := θ.mapMatrix (m := n × Fin r)
  have hMM : Θ XS * Θ YS = 1 := by rw [← map_mul, hXY, map_one]
  let Mu : GL (n × Fin r) ℂ_[l] := ⟨Θ XS, Θ YS, hMM, (by first | exact mul_eq_one_comm.mp hMM | exact Matrix.mul_eq_one_comm.1 hMM)⟩
  have hSen : ∀ g : ↥(GK K), (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) *
      (Mu : Matrix (n × Fin r) (n × Fin r) ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = Mu := by
    intro g
    have h1 : (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ℂ_[l]) =
        Θ ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map qS) := by
      ext i j
      simp only [Θ, RingHom.mapMatrix_apply, Matrix.map_apply]
      have := (hθΩ (((algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) ((ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]) i j)) : ↥(MaximalUnramifiedExtension l)) : Om l)).2
      exact this.symm
    have h2 : (Mu : Matrix (n × Fin r) (n × Fin r) ℂ_[l]).map (Formalism.Per.σC (g : GQ l)) = Θ (XS.map (actS (g : GQ l))) := by
      ext i j
      simp only [Θ, RingHom.mapMatrix_apply, Matrix.map_apply]
      exact ((hθg (g : GQ l) (XS i j)).2).symm
    rw [h1, h2, ← map_mul, hES g]
  have hfin₀ := _root_.GlobalTheory.PMon.senFinite l (n × Fin r) K ρ₀ hc₀ Mu hSen

  have hr : 0 < r := hρ.pos
  let z : Fin r := ⟨0, hr⟩
  let F : GL (n × Fin r) ℚ_[l] → Matrix n n ↥(MaximalUnramifiedExtension l) := fun A => Matrix.of fun i j =>
    ((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * (A : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) *
      ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) (i, z) (j, z)
  have hFρ : ∀ g, F (ρ₀ g) = (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) := by
    intro g
    ext i j
    simp only [F, Matrix.of_apply]
    rw [hρ₀ g, mul_assoc, Units.mul_inv, mul_one, Matrix.blockDiagonal_apply_eq, Matrix.map_apply]
    exact congrArg Subtype.val (fr_zero_apply l ((ρ g : Matrix n n ↥(MaximalUnramifiedExtension l)) i j))
  have hfin : (ρ '' (IK K : Set ↥(GK K))).Finite := by
    have h1 : ((fun A : GL n ↥(MaximalUnramifiedExtension l) => (A : Matrix n n ↥(MaximalUnramifiedExtension l))) '' (ρ '' (IK K : Set ↥(GK K)))).Finite := by
      rw [Set.image_image]
      have : (fun g => (ρ g : Matrix n n ↥(MaximalUnramifiedExtension l))) '' (IK K : Set ↥(GK K)) = F '' (ρ₀ '' (IK K : Set ↥(GK K))) := by
        rw [Set.image_image]
        simp only [hFρ]
      rw [this]
      exact hfin₀.image F
    exact Set.Finite.of_finite_image h1 (fun a _ b _ h => Units.ext h)
  exact _root_.GlobalTheory.PMon.unrStep_holds l P AI T n K r ρ hρ hfin

end GlobalTheory.PMon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerLawUpperTriangularUnipotentAdelic
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

section Entries

variable {R : Type} [CommRing R] {a : ℕ}

theorem posM_block_entry {r m : ℕ} (x : UnipotentBlockColumnIndex a r m → R) (i j : Fin a) :
    posM (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) x i j =
      if h : (i : ℕ) < r ∧ r ≤ (j : ℕ) ∧ (j : ℕ) ≤ m then x ⟨(i, j), h⟩ else 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨(i, j), h⟩]
    · simp
    · intro t _ ht
      rw [if_neg]
      rintro ⟨e1, e2⟩
      exact ht (Subtype.ext (Prod.ext e1 e2))
    · simp
  · refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨e1, e2⟩
    apply h
    have := t.2
    rw [← e1, ← e2]
    exact this

theorem posM_col_mul {n : ℕ} (x : UnipotentBlockColumnIndex a n n → R) (M : Matrix (Fin a) (Fin a) R)
    (h : ∀ k : Fin a, (k : ℕ) = n → ∀ j, M k j = (1 : Matrix (Fin a) (Fin a) R) k j) :
    posM (Subtype.val : UnipotentBlockColumnIndex a n n → Fin a × Fin a) x * M = posM Subtype.val x := by
  simp only [posM, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht : ((t.1.2 : Fin a) : ℕ) = n := by have := t.2; omega
  ext i j
  by_cases hi : i = t.1.1
  · subst hi
    rw [Matrix.single_mul_apply_same, h _ ht, Matrix.one_apply, Matrix.single_apply]
    by_cases hj : t.1.2 = j <;> simp [hj]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hi, Matrix.single_apply, if_neg]
    rintro ⟨e1, _⟩
    exact hi e1.symm

theorem sum_posM_col {n : ℕ} (x : UnipotentBlockColumnIndex a n n → R) :
    (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, posM (Subtype.val : UnipotentBlockColumnIndex a n n → Fin a × Fin a) x p.1 p.2) =
      ∑ t : UnipotentBlockColumnIndex a n n, if (t.1.1 : ℕ) + 1 = n then x t else 0 := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  have ht : ((t.1.2 : Fin a) : ℕ) = n := by have := t.2; omega
  by_cases h : (t.1.1 : ℕ) + 1 = n
  · rw [if_pos h, Finset.sum_eq_single t.1]
    · simp
    · intro p _ hp
      rw [if_neg]
      rintro ⟨e1, e2⟩
      exact hp (Prod.ext e1.symm e2.symm)
    · intro hp
      exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ _, by omega⟩) hp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hp2 := (Finset.mem_filter.1 hp).2
    rw [if_neg]
    rintro ⟨e1, e2⟩
    apply h
    rw [e1, ← ht, e2]
    exact hp2.symm

end Entries

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem whittakerLaw_upperUnipotent_identityColumns (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ)
    (hf : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g) (n : ℕ) :
    ∀ u : GL (Fin a) (Ad E), (∀ i j : Fin a, j < i → u.val i j = 0) → (∀ j : Fin a, u.val j j = 1) →
      (∀ i j : Fin a, n ≤ (j : ℕ) → i ≠ j → u.val i j = 0) →
      ∀ g : GA E a, f (u * g) = ψ (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) * f g := by
  induction n with
  | zero =>
    intro u _ hd hc g
    have hu : u = 1 := by
      apply Units.ext
      ext i j
      by_cases h : i = j
      · subst h; simp [hd]
      · simp [hc i j (Nat.zero_le _) h, h]
    subst hu
    have hs : (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, (1 : GL (Fin a) (Ad E)).val p.1 p.2) = 0 := by
      refine Finset.sum_eq_zero fun p hp => ?_
      have hp2 := (Finset.mem_filter.1 hp).2
      have : p.1 ≠ p.2 := fun e => by rw [e] at hp2; omega
      simp [this]
    rw [hs, AddChar.map_zero_eq_one, one_mul, one_mul]
  | succ n ih =>
    intro u ht hd hc g
    by_cases hn : n = 0
    · subst hn
      refine ih u ht hd (fun i j _ hij => ?_) g
      rcases lt_or_gt_of_ne hij with h | h
      · exact hc i j (by have : (i : ℕ) < j := h; omega) hij
      · exact ht i j h
    set y : UnipotentBlockColumnIndex a n n → Ad E := fun t => u.val t.1.1 t.1.2 with hy
    have hrow : ∀ k : Fin a, (k : ℕ) = n → ∀ j, u.val k j = (1 : Matrix (Fin a) (Fin a) (Ad E)) k j := by
      intro k hk j
      by_cases h : k = j
      · subst h; simp [hd]
      · rw [Matrix.one_apply, if_neg h]
        rcases lt_or_gt_of_ne h with h' | h'
        · exact hc k j (by have : (k : ℕ) < j := h'; omega) h
        · exact ht k j h'
    have hval : ∀ i j, ((blkU y)⁻¹ * u).val i j = u.val i j - posM Subtype.val y i j := by
      intro i j
      have e : ((blkU y)⁻¹ * u).val = (1 - posM Subtype.val y) * u.val := rfl
      rw [e, sub_mul, one_mul, posM_col_mul y _ hrow, Matrix.sub_apply]
    have hz : ∀ i j : Fin a, ¬ ((i : ℕ) < n ∧ (j : ℕ) = n) → posM (Subtype.val : UnipotentBlockColumnIndex a n n → Fin a × Fin a) y i j = 0 := by
      intro i j h
      rw [posM_block_entry, dite_eq_right]
      rintro ⟨h1, h2, h3⟩
      exact h ⟨h1, by omega⟩
    have e1 := ih ((blkU y)⁻¹ * u) ?_ ?_ ?_ g
    · have e2 : u * g = blkU y * (((blkU y)⁻¹ * u) * g) := by group
      rw [e2, hf n (by omega), e1, ← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      simp only [hval, Finset.sum_sub_distrib, sum_posM_col, dot, eLast]
      have hd2 : (∑ t : UnipotentBlockColumnIndex a n n, algebraMap E (Ad E) (if (t.1.1 : ℕ) + 1 = n then 1 else 0) * y t) =
          ∑ t : UnipotentBlockColumnIndex a n n, if (t.1.1 : ℕ) + 1 = n then y t else 0 := by
        refine Finset.sum_congr rfl fun t _ => ?_
        split_ifs <;> simp
      rw [hd2, add_sub_cancel]
    · intro i j hji
      rw [hval, ht i j hji, hz i j, sub_zero]
      rintro ⟨h1, h2⟩
      have : (j : ℕ) < i := hji
      omega
    · intro j
      rw [hval, hd, hz j j, sub_zero]
      rintro ⟨h1, h2⟩
      omega
    · intro i j hj hij
      rw [hval]
      by_cases hjn : (j : ℕ) = n
      · by_cases hin : (i : ℕ) < n
        · rw [posM_block_entry, dite_eq_left ⟨hin, by omega, by omega⟩, sub_eq_zero]
        · rw [hz i j (fun h => hin h.1), sub_zero]
          exact ht i j (by
            have : (j : ℕ) < i := by
              have : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
              omega
            exact this)
      · rw [hc i j (by omega) hij, hz i j (fun h => hjn h.2), sub_zero]

theorem tri_law (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (f : GA E a → ℂ)
    (hf : ∀ k, 0 < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g)
    (u : GL (Fin a) (Ad E)) (ht : ∀ i j : Fin a, j < i → u.val i j = 0) (hd : ∀ j : Fin a, u.val j j = 1) (g : GA E a) :
    f (u * g) = ψ (∑ p : Fin a × Fin a with (p.2 : ℕ) = p.1 + 1, u.val p.1 p.2) * f g :=
  whittakerLaw_upperUnipotent_identityColumns ψ f hf a u ht hd (fun _ j h => absurd j.2 (by omega)) g

end GlobalTheory.CuspGeneric
end
end

