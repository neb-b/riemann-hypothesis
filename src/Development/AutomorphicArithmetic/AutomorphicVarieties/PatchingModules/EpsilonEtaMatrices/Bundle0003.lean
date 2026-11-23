module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FixBdQZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.MemW1IffPattern

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FinrankCentralizerW1Le
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem centralizer_rank_le {A : Type} [CommRing A] [IsDomain A] {n : ℕ} (al : Fin n → A) (P : Matrix (Fin n) (Fin n) A)
    (hal : Function.Injective al) (hP : P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i))) :
    (∀ (N : Type) [AddCommGroup N] [Module A N] (f : N →ₗ[A] Matrix (Fin n) (Fin n) A), Function.Injective f →
      (∀ z, P * f z = f z * P) → Module.finrank A N ≤ n) ∧
    ∀ E Y : Matrix (Fin n) (Fin n) A, P * E = E * P → P * Y = Y * P → E * Y = Y * E := by
  let K := FractionRing A
  have inj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  let φ : Matrix (Fin n) (Fin n) A →ₐ[A] Matrix (Fin n) (Fin n) K := (Algebra.ofId A K).mapMatrix
  have φinj : Function.Injective φ := Matrix.map_injective inj
  obtain ⟨h1, h2⟩ := UpperTheory.V.AlgebraTools.centraliser_rank (fun i => algebraMap A K (al i)) (φ P) (inj.comp hal) (by
    have : φ P = P.map (algebraMap A K) := rfl
    rw [this, Matrix.charpoly_map, hP, Polynomial.map_prod]
    simp)
  refine ⟨fun N _ _ f hf hc => ?_, fun E Y hE hY => φinj ?_⟩
  · set U := LinearMap.ker (LinearMap.mulLeft K (φ P) - LinearMap.mulRight K (φ P)) with hU
    let ψ : N →ₗ[A] U :=
      { toFun := fun z => ⟨φ (f z), by
          rw [hU, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
            ← map_mul, hc, map_mul, sub_self]⟩
        map_add' := fun y z => Subtype.ext (by simp)
        map_smul' := fun c z => Subtype.ext (by simp) }
    have hψ : Function.Injective ψ := fun y z h => hf (φinj (congrArg Subtype.val h))
    apply Module.finrank_le_of_rank_le
    refine (LinearMap.rank_le_of_injective ψ hψ).trans ?_
    rw [← IsLocalization.rank_eq K (nonZeroDivisors A) le_rfl, ← Module.finrank_eq_rank, h1, Fintype.card_fin]
  · obtain ⟨q, hq⟩ := h2 (φ Y) (by rw [← map_mul, hY, map_mul])
    obtain ⟨r, hr⟩ := h2 (φ E) (by rw [← map_mul, hE, map_mul])
    rw [map_mul, map_mul, hq, hr, ← map_mul, ← map_mul, mul_comm]

private theorem dual_sum_ep_prime_coord {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem dual_sum_eta_coord {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem dual_sum_a_coord {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

private theorem finrank_centralizer_W1_le {A : Type} [CommRing A] [IsDomain A] {n a g : ℕ} (al : Fin n → A)
    (P : Matrix (Fin n) (Fin n) A)
    (hal : Function.Injective al) (hP : P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)))
    (hev : P ∈ Ev A A n a) (R : Matrix (Fin n) (Fin n) (DD A g)) (hR : ∀ i j, (R i j).a = P i j)
    (N : Submodule A (Matrix (Fin n) (Fin n) (DD A g))) (h1 : N ≤ pairedDualFirstOrderDualMatrixSpace n A A g a) (h2 : ∀ Z ∈ N, R * Z = Z * R) :
    Module.finrank A N ≤ n := by
  obtain ⟨c1, c2⟩ := centralizer_rank_le al P hal hP
  have ha : ∀ Z ∈ N, ∀ i j, (Z i j).a = 0 ∧ (Z i j).ep = 0 := fun Z hZ i j => by
    by_cases h : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
    · have := (h1 hZ i j).1 h
      exact ⟨this.1 rfl, this.2.1 rfl⟩
    · have := (h1 hZ i j).2 h
      exact ⟨this.1 rfl, this.2.1 rfl⟩
  have hb : ∀ Z ∈ N, ∀ i j s, (Z i j).ep' s = 0 := fun Z hZ i j s => by
    by_cases h : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
    · exact congrFun (((h1 hZ i j).1 h).2.2.1 rfl) s
    · have e := c2 (diagonal fun i => if (i : ℕ) < a then 1 else 0) (Matrix.of fun i j => (Z i j).ep' s) ?_ ?_
      · have e' := congrFun (congrFun e i) j
        rw [diagonal_mul, mul_diagonal, of_apply] at e'
        by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp_all
      · ext u v
        rw [diagonal_mul, mul_diagonal]
        by_cases h' : ((u : ℕ) < a) ↔ ((v : ℕ) < a)
        · simp [h', mul_comm]
        · have : P u v = 0 := (hev u v).2 h'
          simp [this]
      · ext u v
        have e' := congrArg (fun M : Matrix (Fin n) (Fin n) (DD A g) => (M u v).ep' s) (h2 Z hZ)
        simpa [Matrix.mul_apply, dual_sum_ep_prime_coord, hR, fun i j => (ha Z hZ i j).1] using e'
  have hs : ∀ (c : A) (y : DD A g), (c • y).eta = c * y.eta := fun c y => by
    have hc : c • y = DD.C (algebraMap A A c) * y := rfl
    simp [hc]
  refine c1 N
    { toFun := fun Z => Matrix.of fun i j => (Z.1 i j).eta
      map_add' := fun y z => rfl
      map_smul' := fun c z => by ext i j; simp [hs] } ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro Z hZ
    ext i j
    · exact (ha _ Z.2 i j).1
    · exact congrFun (ha _ Z.2 i j).2 _
    · exact hb _ Z.2 i j _
    · exact congrFun (congrFun hZ i) j
  · rintro ⟨Z, hZ⟩
    change P * (Matrix.of fun i j => (Z i j).eta) = (Matrix.of fun i j => (Z i j).eta) * P
    ext u v
    have e' := congrArg (fun M : Matrix (Fin n) (Fin n) (DD A g) => (M u v).eta) (h2 Z hZ)
    simpa [Matrix.mul_apply, dual_sum_eta_coord, hR, fun i j => (ha Z hZ i j).1, fun i j => (ha Z hZ i j).2, hb Z hZ] using e'

theorem UpperTheory.V.Pa.h0q :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (σ : F.G₀) (al : Fin n → x.A), Function.Injective al → (mat x.ρ σ).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)) → ∃ C : ℕ, ∀ (m : ℕ), {Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) | Y ∈ k.EpsilonEtaTensorDual (x.Am m) ∧ k.ρ1 (x.Am m) σ * Y * k.ρ1 (x.Am m) σ⁻¹ = Y}.ncard ≤ Nat.card x.K ^ (m * n + C) := by
  intro l _ F n x k σ al hal hP
  obtain ⟨C, hC⟩ := fixBd l F n x k _ false false false true false false true false Unit (fun _ => 1)
    (fun _ => k.ρ1 x.A σ) (fun _ => k.ρ1 x.A σ⁻¹) false rfl
  refine ⟨C, fun m => ?_⟩
  have red : ∀ g, (k.ρ1 x.A g).map (fun y => (⟨algebraMap x.A (x.Am m) y.a, fun j => algebraMap x.A (x.Am m) (y.ep j), fun j => algebraMap x.A (x.Am m) (y.ep' j), algebraMap x.A (x.Am m) y.eta⟩ : DD (x.Am m) k.g)) = k.ρ1 (x.Am m) g := by
    intro g
    change (x.redD k.g m).mapMatrix (k.ρ1 x.A g) = _
    rw [Kap.ρ1, Kap.ρ1, map_mul, map_add (f := _), map_one]
    rfl
  refine le_trans (le_of_eq ?_) ((hC m).trans (Nat.pow_le_pow_right Nat.card_pos ?_))
  · congr 1
    ext Y
    simp only [red, one_smul, Set.mem_setOf_eq, forall_const, Bool.false_eq_true, IsEmpty.forall_iff, true_and]
    rfl
  · refine Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) _
    refine finrank_centralizer_W1_le al _ hal hP (x.blk σ) (k.ρ1 x.A σ) (fun i j => ?_) _ (inf_le_left.trans inf_le_left) fun Z hZ => ?_
    · have hc : ∀ c : x.A, algebraMap x.A (DD x.A k.g) c = DD.C c := fun c => rfl
      rw [Kap.ρ1, add_mul, one_mul]
      simp [Matrix.mul_apply, dual_sum_a_coord, DD.epM, NP.ρX, hc]
    · obtain ⟨r1, r2, -⟩ := rho1 l F n x k x.A
      have e : (1 : x.A) • (k.ρ1 x.A σ * (Z * k.ρ1 x.A σ⁻¹)) - Z = 0 := (Submodule.mem_iInf _).1 hZ.2 ()
      rw [one_smul, sub_eq_zero] at e
      conv_rhs => rw [← e]
      rw [mul_assoc, mul_assoc, ← r2, inv_mul_cancel, r1, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.PairEx
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem blk_nd {A R N : Type} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup N] (T : R →+ N) (n a : ℕ)
    (V1 V2 U1 U2 : Submodule A R) (h1 : ∀ x ∈ V1, (∀ y ∈ U1, T (x * y) = 0) → x = 0)
    (h2 : ∀ x ∈ V2, (∀ y ∈ U2, T (x * y) = 0) → x = 0) (Z : Matrix (Fin n) (Fin n) R) (hZ : Z ∈ blkMat n a V1 V2)
    (h : ∀ Y ∈ blkMat n a U1 U2, T (trace (Z * Y)) = 0) : Z = 0 := by
  have tr : ∀ (i j : Fin n) (y : R), trace (Z * single j i y) = Z i j * y := by
    intro i j y
    rw [trace_mul_single]; simp
  have mem : ∀ (i j : Fin n) (y : R), ((((i : ℕ) < a) ↔ ((j : ℕ) < a)) → y ∈ U1) →
      (¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → y ∈ U2) → single j i y ∈ blkMat n a U1 U2 := by
    intro i j y e1 e2 p q
    by_cases e : j = p ∧ i = q
    · obtain ⟨rfl, rfl⟩ := e
      rw [single_apply_same]
      exact ⟨fun e => e1 e.symm, fun e => e2 fun e' => e e'.symm⟩
    · rw [single_apply_of_ne _ _ _ _ _ e]
      exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩
  refine Matrix.ext fun i j => ?_
  by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
  · refine h1 _ ((hZ i j).1 e) fun y hy => ?_
    rw [← tr]
    exact h _ (mem i j y (fun _ => hy) fun e' => absurd e e')
  · refine h2 _ ((hZ i j).2 e) fun y hy => ?_
    rw [← tr]
    exact h _ (mem i j y (fun e' => absurd e' e) fun _ => hy)

private def etaH (X : Type) [CommRing X] (g : ℕ) : DD X g →+ X where
  toFun u := u.eta
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem etaH_apply (X : Type) [CommRing X] (g : ℕ) (u : DD X g) : etaH X g u = u.eta := rfl

section
variable {A X N : Type} [CommRing A] [CommRing X] [Algebra A X] [AddCommGroup N] {g : ℕ} (τ : X →+ N)
  (hτ : ∀ y, (∀ z, τ (y * z) = 0) → y = 0)
include hτ

private theorem nd1 : ∀ x ∈ ddPart A X g true false false false,
    (∀ y ∈ ddPart A X g false false false true, (τ.comp (etaH X g)) (x * y) = 0) → x = 0 := by
  rintro x ⟨-, a2, a3, a4⟩ h
  refine DD.ext (hτ _ fun z => ?_) (a2 rfl) (a3 rfl) (a4 rfl)
  have := h ⟨0, 0, 0, z⟩ ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, by simp⟩
  rw [AddMonoidHom.comp_apply, etaH_apply] at this
  simpa using this

private theorem nd2 : ∀ x ∈ ddPart A X g false false false true,
    (∀ y ∈ ddPart A X g true false false false, (τ.comp (etaH X g)) (x * y) = 0) → x = 0 := by
  rintro x ⟨a1, a2, a3, -⟩ h
  refine DD.ext (a1 rfl) (a2 rfl) (a3 rfl) (hτ _ fun z => ?_)
  have := h ⟨z, 0, 0, 0⟩ ⟨by simp, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  rw [AddMonoidHom.comp_apply, etaH_apply] at this
  simpa using this

private theorem nd3 : ∀ x ∈ ddPart A X g false true false false,
    (∀ y ∈ ddPart A X g false false true false, (τ.comp (etaH X g)) (x * y) = 0) → x = 0 := by
  rintro x ⟨a1, -, a3, a4⟩ h
  refine DD.ext (a1 rfl) (funext fun j => hτ _ fun z => ?_) (a3 rfl) (a4 rfl)
  have := h ⟨0, 0, Pi.single j z, 0⟩ ⟨fun _ => rfl, fun _ => rfl, by simp, fun _ => rfl⟩
  rw [AddMonoidHom.comp_apply, etaH_apply] at this
  simpa [Pi.single_apply] using this

private theorem nd4 : ∀ x ∈ ddPart A X g false false true false,
    (∀ y ∈ ddPart A X g false true false false, (τ.comp (etaH X g)) (x * y) = 0) → x = 0 := by
  rintro x ⟨a1, a2, -, a4⟩ h
  refine DD.ext (a1 rfl) (a2 rfl) (funext fun j => hτ _ fun z => ?_) (a4 rfl)
  have := h ⟨0, Pi.single j z, 0, 0⟩ ⟨fun _ => rfl, by simp, fun _ => rfl, fun _ => rfl⟩
  rw [AddMonoidHom.comp_apply, etaH_apply] at this
  simpa [Pi.single_apply] using this

end

theorem UpperTheory.V.Pa.pairEx :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (m : ℕ), ∃ b : k.M1 (x.Am m) →+ k.EpsilonEtaTensorDual (x.Am m) →+ ZMod l, ∀ (rep : Representation x.A G.Γ (k.M1 (x.Am m))) (rep' : Representation x.A G.Γ (k.EpsilonEtaTensorDual (x.Am m))), IsAd G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) (fun _ => 1) (k.M1 (x.Am m)) rep → IsAd G.frame (fun g => k.ρ1 (x.Am m) (h.p₀ g)) (fun g => epsD k (x.Am m) (h.p g)) (k.EpsilonEtaTensorDual (x.Am m)) rep' → IsDualPair G.ε rep rep' b := by
  intro l _ L G G0 h n x k m
  obtain ⟨τ, hτ, hs⟩ := pair1 l G0.frame n x m
  obtain ⟨r1, r2, -⟩ := rho1 l G0.frame n x k (x.Am m)
  set T : DD (x.Am m) k.g →+ ZMod l := τ.comp (etaH (x.Am m) k.g) with hT
  let b : k.M1 (x.Am m) →+ k.EpsilonEtaTensorDual (x.Am m) →+ ZMod l := AddMonoidHom.mk' (fun Z => AddMonoidHom.mk'
    (fun Y => T (trace ((Z : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) * (Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)))))
    fun Y Y' => by rw [Submodule.coe_add, Matrix.mul_add, trace_add, map_add (f := _)])
    fun Z Z' => by
      refine AddMonoidHom.ext fun Y => ?_
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [Submodule.coe_add, Matrix.add_mul, trace_add, map_add (f := _)]
  have hb : ∀ Z Y, b Z Y = T (trace ((Z : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) *
      (Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)))) := fun _ _ => rfl
  have hE : ∀ (γ : G.Γ) (u : DD (x.Am m) k.g), T (epsD k (x.Am m) (h.p γ) * u) = epsBar G.ε γ * T u := by
    intro γ u
    have e : (epsD k (x.Am m) (h.p γ) * u).eta =
        algebraMap x.A (x.Am m) (algebraMap ℤ_[l] x.A (G0.ε (h.p γ) : ℤ_[l])) * u.eta := by
      show (DD.C (algebraMap x.A (x.Am m) (algebraMap ℤ_[l] x.A (G0.ε (h.p γ) : ℤ_[l]))) * u).eta = _
      simp
    show τ (epsD k (x.Am m) (h.p γ) * u).eta = _ * τ u.eta
    rw [e, hs, h.ε]; rfl
  refine ⟨b, fun rep rep' ⟨p1, p2⟩ ⟨q1, q2⟩ => ⟨fun Z hZ => Subtype.ext ?_, fun Y hY => Subtype.ext ?_, ?_⟩⟩
  · exact blk_nd T n x.a _ _ _ _ (nd1 τ hτ) (nd3 τ hτ) _ Z.2 fun Y hY => hZ ⟨Y, hY⟩
  · refine blk_nd T n x.a _ _ _ _ (nd2 τ hτ) (nd4 τ hτ) _ Y.2 fun Z hZ => ?_
    rw [trace_mul_comm]
    exact hY ⟨Z, hZ⟩
  · have e0 : ∀ (g : G.frame.G₀) Z Y, b (rep g Z) (rep' g Y) = epsBar G.ε g * b Z Y := by
      intro g Z Y
      rw [hb, hb, p1, q1, ← hE]
      have i1 : k.ρ1 (x.Am m) (h.p₀ g⁻¹) * k.ρ1 (x.Am m) (h.p₀ g) = 1 := by
        rw [← r2, ← map_mul, inv_mul_cancel, map_one, r1]
      congr 1
      beta_reduce
      generalize k.ρ1 (x.Am m) (h.p₀ g⁻¹) = s at i1 ⊢
      generalize k.ρ1 (x.Am m) (h.p₀ g) = r at i1 ⊢
      rw [one_smul, Matrix.mul_smul, trace_smul, smul_eq_mul]
      congr 1
      rw [← Matrix.mul_assoc, trace_mul_comm]
      simp only [← Matrix.mul_assoc]
      rw [i1, Matrix.one_mul, Matrix.mul_assoc _ s, i1, Matrix.mul_one]
    have ec : ∀ Z Y, b (rep G.c Z) (rep' G.c Y) = epsBar G.ε G.c * b Z Y := by
      intro Z Y
      rw [hb, hb, p2, q2, ← hE]
      congr 1
      beta_reduce
      rw [one_smul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_smul, trace_smul, smul_eq_mul,
        ← transpose_mul, trace_transpose, trace_mul_comm]
    intro γ Z Y
    by_cases hγ : γ ∈ G.η.ker
    · exact e0 ⟨γ, hγ⟩ Z Y
    · have hm : γ * G.c ∈ G.η.ker := by
        rw [MonoidHom.mem_ker] at hγ ⊢
        rcases Int.units_eq_one_or (G.η γ) with e | e
        · exact absurd e hγ
        · rw [map_mul, e, G.η_c]; simp
      have e : γ = γ * G.c * G.c := by rw [mul_assoc, G.c_sq, mul_one]
      have := e0 ⟨_, hm⟩ (rep G.c Z) (rep' G.c Y)
      rw [ec, ← mul_assoc] at this
      rw [e, map_mul rep, map_mul rep', Module.End.mul_apply, Module.End.mul_apply]
      refine this.trans ?_
      simp only [epsBar, map_mul, Units.val_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.UpConj
section
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem up_mul {R : Type} [CommRing R] {n : ℕ} {P Q : Matrix (Fin n) (Fin n) R}
    (hP : ∀ i j, j < i → P i j = 0) (hQ : ∀ i j, j < i → Q i j = 0) :
    (∀ i j, j < i → (P * Q) i j = 0) ∧ ∀ i, (P * Q) i i = P i i * Q i i := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : c < i
    · rw [hP i c hc, zero_mul]
    · rw [hQ c j (lt_of_lt_of_le h (not_lt.1 hc)), mul_zero]
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_single i (fun c _ hc => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hc with h | h
    · rw [hP i c h, zero_mul]
    · rw [hQ c i h, mul_zero]

private theorem up_conj {R : Type} [CommRing R] {n : ℕ} {w wi r s y : Matrix (Fin n) (Fin n) R}
    (h1 : wi * w = 1) (h2 : w * wi = 1) (h3 : r * s = 1)
    (hr : ∀ i j, j < i → (wi * r * w) i j = 0) (hs : ∀ i j, j < i → (wi * s * w) i j = 0)
    (hy : ∀ i j, j < i → (wi * y * w) i j = 0) :
    (∀ i j, j < i → (wi * (r * y * s - y) * w) i j = 0) ∧ ∀ i, (wi * (r * y * s - y) * w) i i = 0 := by
  have key : wi * (r * y * s - y) * w = (wi * r * w) * (wi * y * w) * (wi * s * w) - wi * y * w := by
    rw [Matrix.mul_sub, Matrix.sub_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc w wi, h2, Matrix.one_mul, ← Matrix.mul_assoc w wi, h2, Matrix.one_mul]
  have hRS : (wi * r * w) * (wi * s * w) = 1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc w wi, h2, Matrix.one_mul, ← Matrix.mul_assoc r s, h3, Matrix.one_mul, h1]
  obtain ⟨hA, hAd⟩ := up_mul hr hy
  obtain ⟨hB, hBd⟩ := up_mul hA hs
  have hRSd := (up_mul hr hs).2
  rw [key]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.sub_apply, hB i j hij, hy i j hij, sub_zero]
  · rw [Matrix.sub_apply, hBd i, hAd i]
    have hi := hRSd i
    rw [hRS, Matrix.one_apply_eq] at hi
    linear_combination (-(wi * y * w) i i) * hi

theorem UpperTheory.V.Pa.bMem :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (m : ℕ) (v : F.Vl) (y : k.M1 (x.Am m)) (β : F.Gv v → k.M1 (x.Am m)), y ∈ k.b1 (x.Am m) v → IsLocallyConstant β → (∀ g, (β g : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) = k.ρ1 (x.Am m) (F.φ v g) * y * k.ρ1 (x.Am m) (F.φ v g)⁻¹ - y) → β ∈ k.Zb (x.Am m) v := by
  intro l _ F n x k m v y β hy hβc hβ
  obtain ⟨hone, hmul, -, hw, -⟩ := rho1 l F n x k (x.Am m)
  obtain ⟨h1, h2⟩ := hw v
  have hT := (tri l F n x k (x.Am m) v).1
  have hinv : ∀ g : F.Gv v, k.ρ1 (x.Am m) (F.φ v g) * k.ρ1 (x.Am m) (F.φ v g)⁻¹ = 1 := by
    intro g
    rw [← hmul, mul_inv_cancel, hone]
  have hU : ∀ g : F.Gv v,
      (∀ i j, j < i → (k.wi1 (x.Am m) v * (β g : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) * k.w1 (x.Am m) v) i j = 0) ∧
      ∀ i, (k.wi1 (x.Am m) v * (β g : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) * k.w1 (x.Am m) v) i i = 0 := by
    intro g
    rw [hβ g]
    refine up_conj h1 h2 (hinv g) (hT g).1 ?_ (fun i j hij => hy i j hij)
    have hg := (hT g⁻¹).1
    rwa [map_inv] at hg
  refine ⟨hβc, fun g h => ?_, fun g => fun i j hij => (hU g).1 i j hij, fun g _ i => (hU g).2 i⟩
  rw [hβ (g * h), hβ g, hβ h, map_mul, hmul, _root_.mul_inv_rev, hmul]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel
end

