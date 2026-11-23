module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CoefficientExtensionPreservesConditionsAndDet
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem l_zero {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Finite K] (f : ℤ_[l] →+* K) : (l : K) = 0 := by
  by_contra hne
  have hp : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have hlp : ringChar K ≠ l := by
    intro h
    apply hne
    rw [← h]
    exact ringChar.Nat.cast_ringChar
  have hcop : l.Coprime (ringChar K) := (Nat.coprime_primes (Fact.out) hp).mpr hlp.symm
  have hu : IsUnit ((ringChar K : ℕ) : ℤ_[l]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcop)
  have hu' := hu.map f
  rw [map_natCast, ringChar.Nat.cast_ringChar] at hu'
  exact not_isUnit_zero hu'

private theorem hom_uniq {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (f f' : ℤ_[l] →+* R) (h : (l : R) = 0) :
    f = f' := by
  ext x
  have hx := PadicInt.sub_zmodRepr_mem x
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hx
  obtain ⟨y, hy⟩ := hx
  have hx' : x = (PadicInt.zmodRepr x : ℤ_[l]) + y * l := by rw [hy]; ring
  rw [hx', map_add (f := _), map_add (f := _), map_mul, map_mul, map_natCast, map_natCast, map_natCast, map_natCast, h]
  simp

private theorem localization_quotient_separated_dvd {A K L : Type} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] (g : A →+* L)
    (hi : Function.Injective g) (P : Polynomial A) (hs : (P.map (algebraMap A K)).Separable) :
    (P.map g).Separable := by
  have hP : P.map g = (P.map (algebraMap A K)).map (IsFractionRing.lift hi) := by
    rw [Polynomial.map_map]
    congr 1
    ext a
    simp [IsFractionRing.lift_algebraMap]
  rw [hP]
  exact hs.map

private theorem sep_map {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] (j : A →+* B)
    (hinj : Function.Injective j) (P : Polynomial A) (hs : (P.map (algebraMap A (FractionRing A))).Separable) :
    ((P.map j).map (algebraMap B (FractionRing B))).Separable := by
  rw [Polynomial.map_map]
  exact localization_quotient_separated_dvd (K := FractionRing A) ((algebraMap B (FractionRing B)).comp j)
    ((IsFractionRing.injective B (FractionRing B)).comp hinj) P hs

theorem UpperTheory.V.Pa.Det.coefficientExtension_preserves_conditions_and_det :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x x' : NP F n) (j : x.A →+* x'.A), x.Ext x' j → (∀ D : Subgroup F.G₀, x.N4 D → x'.N4 D) ∧ (x.N3 → x'.N3) ∧ GDet.ofRep (mat x'.ρ) = (GDet.ofRep (mat x.ρ)).map j := by
  intro l _ F n x x' j hE
  obtain ⟨hinj, hloc, hfin, hρ, ha, hψ⟩ := hE
  have hmat : ∀ g, mat x'.ρ g = (mat x.ρ g).map j := by
    intro g
    rw [hρ]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro Dg h4 Z hZ
    obtain ⟨m, b, p, hm, hsum, hlin, hdual, -, -⟩ := UpperTheory.V.Pa.Det.extFree j hinj hloc hfin
    have h0 : ((l : ℕ) : x'.A) = 0 := by
      simpa using congrArg (PowerSeries.C (R := x'.K)) (l_zero (algebraMap ℤ_[l] x'.K))
    have hj : algebraMap ℤ_[l] x'.A = j.comp (algebraMap ℤ_[l] x.A) := hom_uniq _ _ h0
    have heps : ∀ g, ((F.eps ℤ_[l] x'.A g : x'.Aˣ) : x'.A) = j (F.eps ℤ_[l] x.A g : x.Aˣ) := by
      intro g
      simp [GFrame.eps, pushCh, hj]
    have hZi : ∀ i, Z.map (p i) = 0 := by
      intro i
      apply h4
      intro g hg
      have lhs : ∀ (e : x.A) (M : Matrix (Fin n) (Fin n) x.A) a c,
          p i (j e * ∑ k, j (M a k) * Z k c) = e * ∑ k, M a k * p i (Z k c) := by
        intro e M a c
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finset.mul_sum, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, ← map_mul, hlin, mul_assoc]
      have rhs : ∀ (M : Matrix (Fin n) (Fin n) x.A) a c,
          p i (∑ k, Z a k * j (M k c)) = ∑ k, p i (Z a k) * M k c := by
        intro M a c
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_comm, hlin, mul_comm]
      ext a c
      have hac := congrFun (congrFun (hZ g hg) a) c
      simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, hmat, Matrix.map_apply, heps] at hac
      simp only [Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, Matrix.map_apply]
      rw [← lhs, ← rhs, hac]
    ext a c
    have hz : ∀ i, p i (Z a c) = 0 := by
      intro i
      have h1 := congrFun (congrFun (hZi i) a) c
      simpa only [Matrix.map_apply, Matrix.zero_apply] using h1
    rw [hsum (Z a c), Matrix.zero_apply]
    simp [hz]
  · intro h3 U hU hne
    obtain ⟨σ, hσ, hsep⟩ := h3 U hU hne
    refine ⟨σ, hσ, ?_⟩
    rw [hmat, Matrix.charpoly_map]
    exact sep_map j hinj _ hsep
  · apply GDet.ext
    intro B _ _ y
    show Matrix.det _ = Matrix.det _
    congr 1
    simp only [MonoidHom.coe_coe, AlgHom.coe_toRingHom, GDet.repAlg]
    congr 2
    apply congrArg
    ext g a b
    simp [hmat]
    try rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.ConstantAndLinearPartsZeroOfMem
section
noncomputable section

open Matrix UpperTheory.V.Alg UpperTheory.V.W

namespace UpperTheory.V.Pa.Det

section Comp

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}

private theorem alg_eq (c : A) : algebraMap A (DD X g) c = DD.C (algebraMap A X c) := rfl

variable (P Q : Matrix (Fin n) (Fin n) (DD X g))

variable (M : Matrix (Fin n) (Fin n) A) (K : Fin g → Matrix (Fin n) (Fin n) X)

variable {N N' : Matrix (Fin n) (Fin n) X}

variable {M}

variable {P}

end Comp

end UpperTheory.V.Pa.Det

open IsLocalRing UpperTheory.V.Pa

private theorem dd_eta_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ m ∈ s, f m).eta = ∑ m ∈ s, (f m).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_eta]
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, DD.add_eta, ih]

private theorem dd_a_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ m ∈ s, f m).a = ∑ m ∈ s, (f m).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_a]
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, DD.add_a, ih]

private theorem dd_ep_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) (j : Fin g) :
    (∑ m ∈ s, f m).ep j = ∑ m ∈ s, (f m).ep j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_ep]
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, DD.add_ep, ih]

private theorem dd_ep'_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) (j : Fin g) :
    (∑ m ∈ s, f m).ep' j = ∑ m ∈ s, (f m).ep' j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_ep']
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, DD.add_ep', ih]

private theorem matrix_map_dd_a_mul {X : Type} [CommRing X] {g n : ℕ} (P Q : Matrix (Fin n) (Fin n) (DD X g)) :
    (P * Q).map DD.a = P.map DD.a * Q.map DD.a := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, dd_a_sum, DD.mul_a]

private theorem matrix_map_dd_ep_mul {X : Type} [CommRing X] {g n : ℕ} (P Q : Matrix (Fin n) (Fin n) (DD X g)) (j : Fin g) :
    (P * Q).map (fun d => d.ep j) = P.map DD.a * Q.map (fun d => d.ep j) + P.map (fun d => d.ep j) * Q.map DD.a := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, dd_ep_sum, DD.mul_ep, Finset.sum_add_distrib]

private theorem matrix_map_dd_ep'_mul {X : Type} [CommRing X] {g n : ℕ} (P Q : Matrix (Fin n) (Fin n) (DD X g)) (j : Fin g) :
    (P * Q).map (fun d => d.ep' j) = P.map DD.a * Q.map (fun d => d.ep' j) + P.map (fun d => d.ep' j) * Q.map DD.a := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, dd_ep'_sum, DD.mul_ep', Finset.sum_add_distrib]

private theorem matrix_map_dd_eta_mul {X : Type} [CommRing X] {g n : ℕ} (P Q : Matrix (Fin n) (Fin n) (DD X g)) :
    (P * Q).map DD.eta = P.map DD.a * Q.map DD.eta + P.map DD.eta * Q.map DD.a +
      ∑ j, (P.map (fun d => d.ep j) * Q.map (fun d => d.ep' j) + P.map (fun d => d.ep' j) * Q.map (fun d => d.ep j)) := by
  ext i k
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, Matrix.sum_apply, dd_eta_sum, DD.mul_eta,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  congr 2
  exact Finset.sum_comm

private theorem mul_apply_eq_zero_of_block_parity {X : Type} [CommRing X] {n a : ℕ} (p q : Prop) (P Q : Matrix (Fin n) (Fin n) X)
    (hP : ∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ p) → P i j = 0)
    (hQ : ∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ q) → Q i j = 0) :
    ∀ i k : Fin n, ¬(((i : ℕ) < a ↔ (k : ℕ) < a) ↔ (p ↔ q)) → (P * Q) i k = 0 := by
  intro i k h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro m _
  by_cases h1 : (((i : ℕ) < a ↔ (m : ℕ) < a) ↔ p)
  · have h2 : ¬(((m : ℕ) < a ↔ (k : ℕ) < a) ↔ q) := by tauto
    rw [hQ m k h2, mul_zero]
  · rw [hP i m h1, zero_mul]

private theorem ofPar_lemma {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n a : ℕ} (p : Prop)
    (P : Matrix (Fin n) (Fin n) X) :
    (P ∈ blkMat n a (⊤ : Submodule A X) ⊥ → ∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ True) → P i j = 0) ∧
    (P ∈ blkMat n a (⊥ : Submodule A X) ⊤ → ∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ False) → P i j = 0) ∧
    ((∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ True) → P i j = 0) → P ∈ blkMat n a (⊤ : Submodule A X) ⊥) ∧
    ((∀ i j : Fin n, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ False) → P i j = 0) → P ∈ blkMat n a (⊥ : Submodule A X) ⊤) := by
  refine ⟨fun h i j hij => ?_, fun h i j hij => ?_, fun h i j => ?_, fun h i j => ?_⟩
  · exact (Submodule.mem_bot A).1 ((h i j).2 (by tauto))
  · exact (Submodule.mem_bot A).1 ((h i j).1 (by tauto))
  · exact ⟨fun _ => Submodule.mem_top, fun hh => (Submodule.mem_bot A).2 (h i j (by tauto))⟩
  · exact ⟨fun hh => (Submodule.mem_bot A).2 (h i j (by tauto)), fun _ => Submodule.mem_top⟩

private theorem ev_od_graded_mul_mem {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n a : ℕ}
    (P Q : Matrix (Fin n) (Fin n) X) :
    (P ∈ Ev A X n a → Q ∈ Ev A X n a → P * Q ∈ Ev A X n a) ∧
    (P ∈ Ev A X n a → Q ∈ Od A X n a → P * Q ∈ Od A X n a) ∧
    (P ∈ Od A X n a → Q ∈ Ev A X n a → P * Q ∈ Od A X n a) ∧
    (P ∈ Od A X n a → Q ∈ Od A X n a → P * Q ∈ Ev A X n a) := by
  have c := ofPar_lemma (A := A) (X := X) (n := n) (a := a) True
  refine ⟨fun hP hQ => ?_, fun hP hQ => ?_, fun hP hQ => ?_, fun hP hQ => ?_⟩
  · exact (c (P * Q)).2.2.1 fun i k h =>
      mul_apply_eq_zero_of_block_parity True True P Q ((c P).1 hP) ((c Q).1 hQ) i k (by tauto)
  · exact (c (P * Q)).2.2.2 fun i k h =>
      mul_apply_eq_zero_of_block_parity True False P Q ((c P).1 hP) ((c Q).2.1 hQ) i k (by tauto)
  · exact (c (P * Q)).2.2.2 fun i k h =>
      mul_apply_eq_zero_of_block_parity False True P Q ((c P).2.1 hP) ((c Q).1 hQ) i k (by tauto)
  · exact (c (P * Q)).2.2.1 fun i k h =>
      mul_apply_eq_zero_of_block_parity False False P Q ((c P).2.1 hP) ((c Q).2.1 hQ) i k (by tauto)

private theorem map_algebraMap_mem_ev_of_mem_and_mem_od_of_mem {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n a : ℕ}
    (P : Matrix (Fin n) (Fin n) A) :
    (P ∈ Ev A A n a → P.map (algebraMap A X) ∈ Ev A X n a) ∧
    (P ∈ Od A A n a → P.map (algebraMap A X) ∈ Od A X n a) := by
  have c := ofPar_lemma (A := A) (X := A) (n := n) (a := a) True P
  have d := ofPar_lemma (A := A) (X := X) (n := n) (a := a) True (P.map (algebraMap A X))
  refine ⟨fun hP => d.2.2.1 fun i j h => ?_, fun hP => d.2.2.2 fun i j h => ?_⟩
  · rw [Matrix.map_apply, c.1 hP i j h, map_zero]
  · rw [Matrix.map_apply, c.2.1 hP i j h, map_zero]

private theorem mem_pairedDualFirstOrderDualMatrixSpace_of_mem_od_of_mem_ev {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}
    (T : Matrix (Fin n) (Fin n) (DD X g)) (ha : T.map DD.a = 0) (he : ∀ c, T.map (fun d => d.ep c) = 0)
    (he' : ∀ c, T.map (fun d => d.ep' c) ∈ Od A X n a) (ht : T.map DD.eta ∈ Ev A X n a) :
    T ∈ pairedDualFirstOrderDualMatrixSpace n A X g a := by
  intro i j
  have h1 := (ofPar_lemma (A := A) True (T.map DD.eta)).1 ht i j
  have h2 : ∀ c, ¬(((i : ℕ) < a ↔ (j : ℕ) < a) ↔ False) → (T i j).ep' c = 0 := fun c =>
    (ofPar_lemma (A := A) True (T.map fun d => d.ep' c)).2.1 (he' c) i j
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact ⟨fun _ => congrFun (congrFun ha i) j, fun _ => funext fun c => congrFun (congrFun (he c) i) j,
      fun _ => funext fun c => h2 c (by tauto), fun hf => absurd hf (by decide)⟩
  · exact ⟨fun _ => congrFun (congrFun ha i) j, fun _ => funext fun c => congrFun (congrFun (he c) i) j,
      fun hf => absurd hf (by decide), fun _ => h1 (by tauto)⟩

theorem UpperTheory.V.Pa.Det.w1sAct :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X] (Z : Matrix (Fin n) (Fin n) (DD X k.g)), Z ∈ pairedDualFirstOrderDualMatrixSpace n x.A X k.g x.a → ∀ g, k.ρ1 X g * Z * k.ρ1 X g⁻¹ ∈ pairedDualFirstOrderDualMatrixSpace n x.A X k.g x.a ∧ (∀ j, ep'M j (k.ρ1 X g * Z * k.ρ1 X g⁻¹) = x.ρX X g * ep'M j Z * x.ρX X g⁻¹) ∧ etaM (k.ρ1 X g * Z * k.ρ1 X g⁻¹) = x.ρX X g * etaM Z * x.ρX X g⁻¹ + ∑ j, ((k.κ j g).map (algebraMap x.A X) * (x.ρX X g * ep'M j Z * x.ρX X g⁻¹) - (x.ρX X g * ep'M j Z * x.ρX X g⁻¹) * (k.κ j g).map (algebraMap x.A X)) ∧ (Z * k.ρ1 X g).trace.eta = (etaM Z * x.ρX X g).trace + ∑ j, (ep'M j Z * (k.κ j g).map (algebraMap x.A X) * x.ρX X g).trace := by
  intro l _ F n x k X _ _ Z hZ g
  have hinv := (UpperTheory.V.Pa.Det.rho1Hom k X).2.2.1 g
  simp only [UpperTheory.V.Pa.Kap.ρ1] at *
  rw [hinv]
  clear hinv
  have hZ' : ∀ i j : Fin n, _ := hZ
  simp only [ddPart] at hZ'
  have hZa : Z.map DD.a = 0 := by
    ext i j
    by_cases h : ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)
    · exact ((hZ' i j).1 h).1 trivial
    · exact ((hZ' i j).2 h).1 trivial
  have hZe : ∀ c : Fin k.g, Z.map (fun d => d.ep c) = 0 := by
    intro c
    ext i j
    by_cases h : ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)
    · exact congrFun (((hZ' i j).1 h).2.1 trivial) c
    · exact congrFun (((hZ' i j).2 h).2.1 trivial) c
  clear hZ'
  have hR : ∀ h : F.G₀, x.ρX (DD X k.g) h = (x.ρX X h).map DD.C := by
    intro h
    funext i j
    simp only [NP.ρX, Matrix.map_apply, alg_eq]
  have hC : ∀ M : Matrix (Fin n) (Fin n) X, (M.map (DD.C (g := k.g))).map DD.a = M ∧
      (∀ c : Fin k.g, (M.map (DD.C (g := k.g))).map (fun d => d.ep c) = 0) ∧
      (∀ c : Fin k.g, (M.map (DD.C (g := k.g))).map (fun d => d.ep' c) = 0) ∧
      (M.map (DD.C (g := k.g))).map DD.eta = 0 := by
    intro M
    refine ⟨?_, fun c => ?_, fun c => ?_, ?_⟩ <;> funext i j <;> simp [DD.C_a, DD.C_ep, DD.C_ep', DD.C_eta]
  set K : Fin k.g → Matrix (Fin n) (Fin n) X := fun j => (k.κ j g).map (algebraMap x.A X) with hKdef
  have hP : ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) + DD.epM K).map DD.a = 1 ∧
      (∀ c, ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) + DD.epM K).map (fun d => d.ep c) = K c) ∧
      (∀ c, ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) + DD.epM K).map (fun d => d.ep' c) = 0) ∧
      ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) + DD.epM K).map DD.eta = 0 := by
    refine ⟨?_, fun c => ?_, fun c => ?_, ?_⟩ <;> funext i j <;> by_cases h : i = j <;>
      simp [Matrix.one_apply, h, DD.epM, DD.add_a, DD.add_ep, DD.add_ep', DD.add_eta, DD.one_a, DD.one_ep,
        DD.one_ep', DD.one_eta, DD.zero_a, DD.zero_ep, DD.zero_ep', DD.zero_eta]
  have hM : ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) - DD.epM K).map DD.a = 1 ∧
      (∀ c, ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) - DD.epM K).map (fun d => d.ep c) = -K c) ∧
      (∀ c, ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) - DD.epM K).map (fun d => d.ep' c) = 0) ∧
      ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) - DD.epM K).map DD.eta = 0 := by
    refine ⟨?_, fun c => ?_, fun c => ?_, ?_⟩ <;> funext i j <;> by_cases h : i = j <;>
      simp [sub_eq_add_neg, Matrix.one_apply, h, DD.epM, DD.add_a, DD.add_ep, DD.add_ep', DD.add_eta, DD.one_a,
        DD.one_ep, DD.one_ep', DD.one_eta, DD.zero_a, DD.zero_ep, DD.zero_ep', DD.zero_eta, DD.neg_a, DD.neg_ep,
        DD.neg_ep', DD.neg_eta]
  have htr : ∀ M : Matrix (Fin n) (Fin n) (DD X k.g), M.trace.eta = (M.map DD.eta).trace := by
    intro M
    simp only [Matrix.trace, Matrix.diag, dd_eta_sum, Matrix.map_apply]
  rw [hR g, hR g⁻¹, htr]
  obtain ⟨hCa, hCe, hCe', hCt⟩ := hC (x.ρX X g)
  obtain ⟨hCa2, hCe2, hCe'2, hCt2⟩ := hC (x.ρX X g⁻¹)
  obtain ⟨hPa, hPe, hPe', hPt⟩ := hP
  obtain ⟨hMa, hMe, hMe', hMt⟩ := hM
  refine ⟨?_, fun c => ?_, ?_, ?_⟩
  · have hρ : x.ρX X g ∈ Ev x.A X n x.a := (map_algebraMap_mem_ev_of_mem_and_mem_od_of_mem _).1 (x.blk g)
    have hρ' : x.ρX X g⁻¹ ∈ Ev x.A X n x.a := (map_algebraMap_mem_ev_of_mem_and_mem_od_of_mem _).1 (x.blk g⁻¹)
    have hW := (UpperTheory.V.Pa.Det.w1sMem (A := x.A) (X := X) (g := k.g) (n := n) (a := x.a)).1 Z hZ
    have hY0 : Z.map DD.eta ∈ Ev x.A X n x.a := hW.1
    have hY : ∀ c, Z.map (fun d => d.ep' c) ∈ Od x.A X n x.a := hW.2
    have hK : ∀ c, K c ∈ Od x.A X n x.a := fun c => (map_algebraMap_mem_ev_of_mem_and_mem_od_of_mem _).2 ((k.mem c).1 g)
    apply mem_pairedDualFirstOrderDualMatrixSpace_of_mem_od_of_mem_ev
    · simp only [matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe, hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
      simp
    · intro c
      simp only [matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe, hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
      simp
    · intro c
      simp only [matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe, hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
      simp
      exact (ev_od_graded_mul_mem _ _).2.2.1 ((ev_od_graded_mul_mem _ _).2.1 hρ (hY c)) hρ'
    · simp only [matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe, hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
      simp
      exact add_mem
        ((ev_od_graded_mul_mem _ _).1 (add_mem ((ev_od_graded_mul_mem _ _).1 hρ hY0)
          (sum_mem fun c _ => (ev_od_graded_mul_mem _ _).2.2.2 ((ev_od_graded_mul_mem _ _).2.2.1 (hK c) hρ) (hY c))) hρ')
        (neg_mem (sum_mem fun c _ => (ev_od_graded_mul_mem _ _).2.2.2 ((ev_od_graded_mul_mem _ _).2.1 hρ (hY c)) ((ev_od_graded_mul_mem _ _).2.1 hρ' (hK c))))
  · simp only [ep'M, matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe,
      hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
    simp
  · simp only [etaM, ep'M, matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe,
      hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
    simp
    simp only [hKdef, Matrix.add_mul, Finset.sum_mul, Matrix.mul_assoc, Finset.sum_sub_distrib]
    abel
  · simp only [etaM, ep'M, matrix_map_dd_a_mul, matrix_map_dd_ep_mul, matrix_map_dd_ep'_mul, matrix_map_dd_eta_mul, hCa, hCe, hCe', hCt, hCa2, hCe2, hCe'2, hCt2, hPa, hPe,
      hPe', hPt, hMa, hMe, hMe', hMt, hZa, hZe]
    simp
    simp only [hKdef, Matrix.mul_assoc]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DTw
section
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem exists_factor {F A M : Type} [Field F] [AddCommGroup A] [Module F A] [AddCommGroup M] [Module F M]
    (T S : A →ₗ[F] M) (h : LinearMap.ker T ≤ LinearMap.ker S) : ∃ d : M →ₗ[F] M, ∀ c, d (T c) = S c := by
  let S' : LinearMap.range T →ₗ[F] M :=
    ((LinearMap.ker T).liftQ S h).comp T.quotKerEquivRange.symm.toLinearMap
  obtain ⟨d, hd⟩ := LinearMap.exists_extend S'
  refine ⟨d, fun c => ?_⟩
  have h1 : d (T c) = S' ⟨T c, LinearMap.mem_range_self T c⟩ := by
    rw [← hd]
    rfl
  have h2 : T.quotKerEquivRange.symm ⟨T c, LinearMap.mem_range_self T c⟩ = Submodule.Quotient.mk c := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [LinearMap.quotKerEquivRange_apply_mk]
  rw [h1]
  simp only [S', LinearMap.comp_apply, LinearEquiv.coe_coe, h2, Submodule.liftQ_apply]

theorem UpperTheory.V.Pa.Det.der :
    ∀ {F G : Type} [Field F] [Group G] {n : ℕ} (D : DetFr F G n) (z : G → Matrix (Fin n) (Fin n) F), TwCoc (fun _ => 1) D.r D.G' z → (∀ i j, D.KillsRel z i j) → ∃ Y, ∀ g ∈ D.G', z g = dTw (fun _ => 1) D.r Y g := by
  intro F G _ _ n D z hz hk
  let A := Finsupp.supported F F (D.G' : Set G)
  let T : A →ₗ[F] Matrix (Fin n) (Fin n) F :=
    (Finsupp.linearCombination F (fun g => D.r g)).comp A.subtype
  let S : A →ₗ[F] Matrix (Fin n) (Fin n) F :=
    (Finsupp.linearCombination F (fun g => z g * D.r g)).comp A.subtype
  have hTS : LinearMap.ker T ≤ LinearMap.ker S := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    ext i j
    have hsupp : ∀ g ∈ (c : G →₀ F).support, g ∈ D.G' := fun g hg =>
      (Finsupp.mem_supported F _).1 c.2 hg
    have := hk i j (c : G →₀ F) hsupp (by simpa [T, Finsupp.linearCombination_apply] using hc)
    simpa [S, Finsupp.linearCombination_apply] using this
  obtain ⟨d, hd⟩ := exists_factor T S hTS
  have hdr : ∀ g ∈ D.G', d (D.r g) = z g * D.r g := by
    intro g hg
    have := hd ⟨Finsupp.single g 1, Finsupp.single_mem_supported F 1 hg⟩
    simpa [T, S] using this
  have hr1 : ∀ g, D.r g⁻¹ * D.r g = 1 := fun g => by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hgen : ∀ g ∈ D.G', ∀ h ∈ D.G',
      d (D.r g * D.r h) = d (D.r g) * D.r h + D.r g * d (D.r h) := by
    intro g hg h hh
    rw [← D.r.map_mul, hdr _ (D.G'.mul_mem hg hh), hdr g hg, hdr h hh, hz g hg h hh, D.r.map_mul]
    simp only [one_smul, Matrix.add_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (D.r g⁻¹) (D.r g) (D.r h), hr1, Matrix.one_mul]
  have hder : ∀ x ∈ Ev F F n D.a, ∀ y ∈ Ev F F n D.a, d (x * y) = d x * y + x * d y := by
    intro x hx y hy
    rw [← D.span] at hx hy
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨g, hg, rfl⟩ := hx'
      induction hy using Submodule.span_induction with
      | mem y hy' =>
        obtain ⟨h, hh, rfl⟩ := hy'
        exact hgen g hg h hh
      | zero => simp
      | add y1 y2 _ _ h1 h2 =>
        simp only [Matrix.mul_add, map_add (f := _), h1, h2]
        abel
      | smul a y _ h1 =>
        simp only [Matrix.mul_smul, map_smul, h1, smul_add]
    | zero => simp
    | add x1 x2 _ _ h1 h2 =>
      simp only [Matrix.add_mul, map_add (f := _), h1, h2]
      abel
    | smul a x _ h1 =>
      simp only [Matrix.smul_mul, map_smul, h1, smul_add]
  obtain ⟨Y, hY⟩ := Det.derEv d hder
  refine ⟨-Y, fun g hg => ?_⟩
  have h1 := hY (D.r g) (D.ev g)
  rw [hdr g hg] at h1
  have h2 : z g = (Y * D.r g - D.r g * Y) * D.r g⁻¹ := by
    rw [← h1, Matrix.mul_assoc, ← D.r.map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
  rw [h2]
  simp only [dTw, one_smul, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [← D.r.map_mul, mul_inv_cancel, map_one, Matrix.mul_one]
  abel
end

