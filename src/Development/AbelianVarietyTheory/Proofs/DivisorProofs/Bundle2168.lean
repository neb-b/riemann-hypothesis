module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2078
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPreUOfFibres
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyMumfordTorusQuotientTower
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2082
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulEqZero
section
namespace GlobalTheory.CocycleCoboundaryNumerator

theorem exists_numerator (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D] (u v : D)
    (f : (E : Type) → [CommRing E] → [Algebra R E] → (D →ₐ[R] E) → E)
    (hf : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E']
      (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ u) → IsUnit (ψ v) →
        f E' (θ.comp ψ) = θ (f E ψ)) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ c : D, ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ u) → IsUnit (ψ v) → f E ψ * (ψ u * ψ v) ^ N = ψ c := by
  classical
  let L := Localization.Away (u * v)
  let ψ₀ : D →ₐ[R] L := IsScalarTower.toAlgHom R D L
  have hψ₀ : IsUnit (ψ₀ u * ψ₀ v) := by
    rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (u * v)
  obtain ⟨⟨a, _, k, rfl⟩, hk⟩ := IsLocalization.surj (Submonoid.powers (u * v)) (f L ψ₀)
  refine ⟨k, fun N hN => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hN
  refine ⟨a * (u * v) ^ j, fun E _ _ ψ hu hv => ?_⟩
  have huv : IsUnit (ψ (u * v)) := by rw [map_mul]; exact hu.mul hv
  let θ : L →ₐ[R] E := IsLocalization.Away.liftAlgHom (u * v) huv
  have hθ : ∀ x : D, θ (algebraMap D L x) = ψ x := fun x =>
    IsLocalization.Away.lift_eq (u * v) huv x
  have hcomp : θ.comp ψ₀ = ψ := AlgHom.ext fun x => hθ x
  have key := hf L E ψ₀ θ (isUnit_of_mul_isUnit_left hψ₀) (isUnit_of_mul_isUnit_right hψ₀)
  rw [hcomp] at key
  have hk' := congrArg θ hk
  simp only [map_mul, hθ] at hk'
  rw [key, map_mul, ← hk']
  simp only [map_pow, map_mul]
  ring

theorem exists_pow_mul_eq_zero (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D]
    (u x : D)
    (h : ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ u) → ψ x = 0) :
    ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → u ^ M * x = 0 := by
  let L := Localization.Away u
  have h0 : algebraMap D L x = 0 :=
    h L (IsScalarTower.toAlgHom R D L) (IsLocalization.Away.algebraMap_isUnit u)
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers u) L x).mp h0
  refine ⟨m, fun M hM => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hM
  have hm' : u ^ m * x = 0 := hm
  rw [pow_add, mul_comm (u ^ m), mul_assoc, hm', mul_zero]

theorem map_inverse_of_isUnit {E E' : Type} [CommRing E] [CommRing E'] (θ : E →+* E') {x : E}
    (hx : IsUnit x) : Ring.inverse (θ x) = θ (Ring.inverse x) := by
  obtain ⟨w, rfl⟩ := hx
  have hw : θ (w : E) = ((Units.map θ.toMonoidHom w : E'ˣ) : E') := rfl
  rw [Ring.inverse_unit, hw, Ring.inverse_unit]
  rfl

theorem cocycle_is_coboundary (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D]
    (n : ℕ) (s : Fin n → D) (hs : Ideal.span (Set.range s) = ⊤)
    (d : Fin n → Fin n → (E : Type) → [CommRing E] → [Algebra R E] → (D →ₐ[R] E) → E)
    (hnat : ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E']
      [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) →
        d a b E' (AlgHom.comp θ ψ) = θ (d a b E ψ))
    (hcoc : ∀ (a b c : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
      IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → IsUnit (ψ (s c)) →
        d a b E ψ + d b c E ψ = d a c E ψ) :
    ∃ (e : Fin n → (E : Type) → [CommRing E] → [Algebra R E] → (D →ₐ[R] E) → E),
      (∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E']
        [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) →
          e a E' (AlgHom.comp θ ψ) = θ (e a E ψ)) ∧
      ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
        IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E ψ = e b E ψ - e a E ψ := by
  classical

  have h1 : ∀ a b : Fin n, ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∃ c : D, ∀ (E : Type) [CommRing E]
      [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) →
        d a b E ψ * (ψ (s a) * ψ (s b)) ^ N = ψ c := fun a b =>
    exists_numerator R D (s a) (s b) (d a b) (fun E _ _ E' _ _ ψ θ ha hb => hnat a b E E' ψ θ ha hb)
  choose N₀ hN₀ using h1
  obtain ⟨N, hN⟩ : ∃ N, ∀ a b, N₀ a b ≤ N :=
    ⟨Finset.univ.sup (fun p : Fin n × Fin n => N₀ p.1 p.2), fun a b =>
      Finset.le_sup (f := fun p : Fin n × Fin n => N₀ p.1 p.2) (Finset.mem_univ (a, b))⟩
  choose c hc using fun a b => hN₀ a b N (hN a b)

  have h2 : ∀ a b k : Fin n, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → (s a * s b * s k) ^ M *
      (s k ^ N * c a b - s a ^ N * c k b + s b ^ N * c k a) = 0 := by
    intro a b k
    apply exists_pow_mul_eq_zero R D
    intro E _ _ ψ hu
    rw [map_mul, map_mul] at hu
    have ha := isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu)
    have hb := isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left hu)
    have hk := isUnit_of_mul_isUnit_right hu
    have e4 := hcoc k a b E ψ hk ha hb
    simp only [map_add (f := _), map_sub, map_mul, map_pow]
    rw [← hc a b E ψ ha hb, ← hc k b E ψ hk hb, ← hc k a E ψ hk ha]
    linear_combination (ψ (s a) * ψ (s b) * ψ (s k)) ^ N * e4
  choose M₀ hM₀ using h2
  obtain ⟨M, hM⟩ : ∃ M, ∀ a b k, M₀ a b k ≤ M :=
    ⟨Finset.univ.sup (fun p : Fin n × Fin n × Fin n => M₀ p.1 p.2.1 p.2.2), fun a b k =>
      Finset.le_sup (f := fun p : Fin n × Fin n × Fin n => M₀ p.1 p.2.1 p.2.2)
        (Finset.mem_univ (a, b, k))⟩

  obtain ⟨K, c', hc', hy⟩ : ∃ (K : ℕ) (c' : Fin n → Fin n → D),
      (∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E),
        IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E ψ * (ψ (s a) * ψ (s b)) ^ K = ψ (c' a b)) ∧
      ∀ a b k, s k ^ K * c' a b = s a ^ K * c' k b - s b ^ K * c' k a := by
    refine ⟨N + M, fun a b => c a b * (s a * s b) ^ M, fun a b E _ _ ψ ha hb => ?_,
      fun a b k => ?_⟩
    · rw [map_mul, ← hc a b E ψ ha hb, map_pow, map_mul, pow_add]
      ring
    · linear_combination hM₀ a b k M (hM a b k)

  have hsK : Ideal.span (Set.range fun i => s i ^ K) = ⊤ := by
    have h := Ideal.span_pow_eq_top _ hs K
    rw [← Set.range_comp] at h
    exact h
  have h1mem : (1 : D) ∈ Ideal.span (Set.range fun i => s i ^ K) := by
    rw [hsK]; exact Submodule.mem_top
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun D).mp h1mem
  refine ⟨fun a E _ _ ψ => ∑ k, ψ (g k * c' k a) * Ring.inverse (ψ (s a)) ^ K, ?_, ?_⟩
  · intro a E _ _ E' _ _ ψ θ ha
    have hinv : Ring.inverse (θ (ψ (s a))) = θ (Ring.inverse (ψ (s a))) :=
      map_inverse_of_isUnit (θ : E →+* E') ha
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hinv]
    simp only [map_mul, map_pow]
  · intro a b E _ _ ψ ha hb
    have hAK : ψ (s a) ^ K * Ring.inverse (ψ (s a)) ^ K = 1 := by
      rw [← mul_pow, Ring.mul_inverse_cancel _ ha, one_pow]
    have hBK : ψ (s b) ^ K * Ring.inverse (ψ (s b)) ^ K = 1 := by
      rw [← mul_pow, Ring.mul_inverse_cancel _ hb, one_pow]
    have hab := hc' a b E ψ ha hb
    have hsum : ∑ k, ψ (g k) * ψ (s k) ^ K = 1 := by
      have h := congrArg ψ hg
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [map_sum, smul_eq_mul, map_mul, map_pow, map_one] using h
    have hd : d a b E ψ = ∑ k, ψ (g k) * ψ (s k) ^ K * d a b E ψ := by
      rw [← Finset.sum_mul, hsum, one_mul]
    rw [hd, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hyk := congrArg ψ (hy a b k)
    simp only [map_mul, map_pow, map_sub] at hyk
    simp only [map_mul]
    linear_combination (ψ (g k)) * ((Ring.inverse (ψ (s a)) ^ K * Ring.inverse (ψ (s b)) ^ K) * hyk
      + (ψ (s k) ^ K * Ring.inverse (ψ (s a)) ^ K * Ring.inverse (ψ (s b)) ^ K) * hab
      + (Ring.inverse (ψ (s b)) ^ K * ψ (c' k b)
          - ψ (s k) ^ K * d a b E ψ * ψ (s b) ^ K * Ring.inverse (ψ (s b)) ^ K) * hAK
      - (Ring.inverse (ψ (s a)) ^ K * ψ (c' k a) + ψ (s k) ^ K * d a b E ψ) * hBK)

end GlobalTheory.CocycleCoboundaryNumerator
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEq
section
open GlobalTheory.LogDerProj

noncomputable section
set_option autoImplicit false

namespace GlobalTheory.LogDerProj

theorem exists_pow_smul_eq_of_res_eq {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R)
    [IsLocalization.Away f S] (φ : k →+* R) (hφ : φ.FiniteType) (J : Ideal R) (D₁ D₂ : logSub φ J)
    (h : res (S := S) f φ J D₁ = res (S := S) f φ J D₂) : ∃ c : Submonoid.powers f, c • D₁ = c • D₂ := by
  classical
  set E : Derivation ℤ R R := D₁.1 - D₂.1 with hE
  have hloc : ∀ r, ∃ m : Submonoid.powers f, (m : R) * E r = 0 := by
    intro r
    have h1 := congrArg (fun D => D.1 (algebraMap R S r)) h
    simp only [res_apply] at h1
    have h2 : algebraMap R S (E r) = 0 := by
      rw [hE, Derivation.sub_apply, map_sub, h1, sub_self]
    exact (IsLocalization.map_eq_zero_iff (Submonoid.powers f) S _).1 h2
  choose m hm using hloc
  letI := φ.toAlgebra
  have hft : Algebra.FiniteType k R := hφ
  obtain ⟨s, hs⟩ := hft.out
  let c : Submonoid.powers f := ∏ x ∈ s, m x
  have hcs : ∀ x ∈ s, (c : R) * E x = 0 := by
    intro x hx
    have : (c : R) = (∏ y ∈ s.erase x, m y : Submonoid.powers f) * m x := by
      simp only [c]
      rw [← Submonoid.coe_mul, ← Finset.prod_erase_mul s m hx]
    rw [this, mul_assoc, hm x, mul_zero]
  have hall : ∀ r, (c : R) * E r = 0 := by
    intro r
    have hr : r ∈ Algebra.adjoin k (s : Set R) := by rw [hs]; trivial
    induction hr using Algebra.adjoin_induction with
    | mem x hx => exact hcs x hx
    | algebraMap a =>
      have e1 : D₁.1 (φ a) = 0 := D₁.2.1 a
      have e2 : D₂.1 (φ a) = 0 := D₂.2.1 a
      show (c : R) * E (φ a) = 0
      rw [hE, Derivation.sub_apply, e1, e2, sub_self, mul_zero]
    | add x y _ _ hx hy => rw [map_add (f := _), mul_add, hx, hy, add_zero]
    | mul x y _ _ hx hy =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, mul_add]
      calc (c : R) * (x * E y) + (c : R) * (y * E x) = x * ((c : R) * E y) + y * ((c : R) * E x) := by ring
        _ = 0 := by rw [hx, hy, mul_zero, mul_zero, add_zero]
  refine ⟨c, ?_⟩
  apply Subtype.ext
  ext r
  rw [Submonoid.smul_def, Submonoid.smul_def]
  show ((c : R) • D₁.1) r = ((c : R) • D₂.1) r
  rw [Derivation.smul_apply, Derivation.smul_apply, smul_eq_mul, smul_eq_mul, ← sub_eq_zero, ← mul_sub]
  have := hall r
  rwa [hE, Derivation.sub_apply] at this

end GlobalTheory.LogDerProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPreUniformisationEvenTorusCompleteNormal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.PreUnifEven

open GlobalTheory.UU GlobalTheory.LN


set_option maxHeartbeats 1000000 in
theorem nonempty_towerR_of_even {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (P : CP G) (hs : IsSemiAbelian G)
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (Q₀ : TQ (thickObj R (maximalIdeal R) 0 G) X) (P₀ : CP (thickObj R (maximalIdeal R) 0 G))
    (lev₀ : IsLevelCP (maximalIdeal R) 0 P₀ P) (even₀ : ∃ σ : CubTriv P₀.c Q₀.i, σ.Even) :
    Nonempty (TowerR (maximalIdeal R) P X) := by
  have := hs.smooth
  have := hs.geomConnected
  have hsm : ∀ e, Smooth (thickObj R (maximalIdeal R) e G).hom := fun e => by
    show Smooth (pullback.snd _ _); infer_instance
  have hc : ∀ e, GeometricallyConnected (thickObj R (maximalIdeal R) e G).hom := fun e => by
    show GeometricallyConnected (pullback.snd _ _); infer_instance
  let L : ℕ → Type 1 := fun e => {l : Lev (maximalIdeal R) P X e // ∃ σ : CubTriv l.Pe.c l.Q.i, σ.Even}
  have step : ∀ (e : ℕ) (l : L e), ∃ l' : L (e + 1),
      TorusCompat (thickTrans R _ e) (thickMap R _ e G) l.1.Q.i l'.1.Q.i := fun e l => by
    obtain ⟨P₁, h₁⟩ := exists_isLevelCP (maximalIdeal R) (e + 1) P
    obtain ⟨_, hP⟩ := TowerEx.exists_isCPMap_thickMap l.1.lev h₁
    obtain ⟨Q, hQ, hσ⟩ := TowerEx.exists_lift (TowerEx.isNilpotent_max (e + 1)) _
      (Ideal.Quotient.factor_surjective _) _ _ (TowerEx.isGrpPullback_thickMap _ e G) hP l.1.Q l.2
    obtain ⟨D⟩ := TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max (e + 1)) _ P₁ Q hσ
    exact ⟨⟨⟨Q, P₁, h₁, D⟩, hσ⟩, hQ⟩
  choose nxt hnxt using step
  obtain ⟨D₀⟩ := TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max 0) _ P₀ Q₀ even₀
  let l : ∀ e, L e := fun e => Nat.rec (motive := L) ⟨⟨Q₀, P₀, lev₀, D₀⟩, even₀⟩ nxt e
  have tor : ∀ e, TorusCompat (thickTrans R _ e) (thickMap R _ e G) (l e).1.Q.i (l (e + 1)).1.Q.i :=
    fun e => hnxt e (l e)
  choose β hβ hq using fun e => TowerEx.exists_levelMap hs (l e).1 (l (e + 1)).1 (tor e)
  exact ⟨⟨fun e => (l e).1, tor, β, hβ, hq⟩⟩


set_option maxHeartbeats 800000 in
theorem fibres (laws : Laws) (hU : USt) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R)
    (hR : admitted R I) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G) (hG : IsSemiAbelian G)
    (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) (hgen : IsMonHom gen.hom)
    (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))))
    (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (T : TowerR I P X) (k : Type) [Field k]
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))) :
    RelAmple ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) ∧
      KTriv ((Over.pullback x).obj (T.l 0).Q.B) ((T.l 0).D.M.L.L.pull (pullback.fst _ x)) := by
  obtain ⟨⟨hN, _⟩, _, hc, _⟩ := hR
  obtain ⟨a, rfl⟩ : ∃ a : R ⧸ I ^ (0 + 1) →+* k, spMap a = x := ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩
  obtain ⟨V, _, _, _, φ, b, hV, hφ, hab, sq⟩ := ClosedPol.exists_trait R I a
  obtain ⟨ψ, sq'⟩ := ClosedPol.exists_generic_square φ hφ
  obtain ⟨A', gen', hgen', hA'⟩ := ClosedPol.exists_fibre_pull laws sq' P.L.isLB A gen hA
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap φ) G ((Over.pullback (spMap φ)).obj G) _ _
    (toBase_mul_pullback G (spMap φ)) P
  rw [← hP'] at hA'
  obtain ⟨P₀, w₀, H₀⟩ := exists_isLevelCP (IsLocalRing.maximalIdeal V) 0 P'
  obtain ⟨wl, hl⟩ := (T.l 0).lev
  obtain ⟨F, pF, w₃, k₃⟩ := ClosedPol.exists_fourth (G := G) (G' := (Over.pullback (spMap φ)).obj G)
    (H := thickObj R I 0 G)
    (H' := thickObj V (IsLocalRing.maximalIdeal V) 0 ((Over.pullback (spMap φ)).obj G)) (P := P) (P' := P')
    (N := (T.l 0).Pe) (N' := P₀) sq (isGrpPullback_pullback G (spMap φ))
    (isGrpPullback_pullback G (thick R I 0)) (isGrpPullback_pullback _ (thick V (IsLocalRing.maximalIdeal V) 0)) H hl H₀
  obtain ⟨Q₀, D₀, β, pβ, hβ⟩ := ClosedPol.exists_desc_pull pF (T.l 0).Q (T.l 0).D k₃
  have hG' : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hG.comm; infer_instance
    · have := hG.smooth; change Smooth (pullback.snd G.hom (spMap φ)); infer_instance
    · have := hG.separated; change IsSeparated (pullback.snd G.hom (spMap φ)); infer_instance
    · have := hG.quasiCompact; change QuasiCompact (pullback.snd G.hom (spMap φ)); infer_instance
    · have := hG.geomConnected; change GeometricallyConnected (pullback.snd G.hom (spMap φ)); infer_instance
    · intro Ω _ _ q
      obtain ⟨E⟩ := hG.fibres Ω (q ≫ spMap φ)
      let em := (Functor.mapMonNatIso (Over.pullbackComp q (spMap φ)) ≪≫ Functor.mapMonCompIso).app (Mon.mk G)
      let e : (Over.pullback (q ≫ spMap φ)).obj G ≅ (Over.pullback q).obj ((Over.pullback (spMap φ)).obj G) := (Mon.forget _).mapIso em
      haveI : IsMonHom e.hom := by
        show IsMonHom em.hom.hom
        infer_instance
      letI := E.grpB
      haveI := E.q_hom
      haveI := E.i_hom
      exact ⟨{ X := E.X
               addCommGroup := E.addCommGroup
               free := E.free
               finite := E.finite
               B := E.B
               grpB := E.grpB
               isAbelian := E.isAbelian
               q := e.inv ≫ E.q
               q_hom := inferInstance
               q_flat := by rw [Over.comp_left]; have := E.q_flat; have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv; infer_instance
               q_surjective := by rw [Over.comp_left]; have := E.q_surjective; have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv; infer_instance
               q_quasiCompact := by rw [Over.comp_left]; have := E.q_quasiCompact; have : IsIso e.inv.left := Functor.map_isIso (Over.forget _) e.inv; infer_instance
               i := E.i ≫ e.hom
               i_hom := inferInstance
               isKernel := by refine IsPullback.of_iso E.isKernel (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp }⟩
  have ev := UniformizationSetting.exists_even_of_desc D₀
  obtain ⟨wA, hwA⟩ := hA'
  have pol := ClosedPol.pol_dvr laws hU
    { cdvr := hV, semi := hG', gen := gen', gen_hom := hgen', P := P', wA := wA, wA_gen := hwA, X := X, Q₀ := Q₀,
      P₀ := P₀, lev₀ := ⟨w₀, H₀⟩, even₀ := ev } D₀
  have : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  let _ : Field (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) := Ideal.Quotient.field _
  exact ClosedPol.pol_of_ker_eq a b hab _ (T.l 0).Q.isAb (T.l 0).D.M.L.isLB Q₀.B pβ D₀.M.L.isLB hβ pol

theorem isAdmissibleCompleteLocalDomainPrime_of_completeNormal {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) : admitted R (maximalIdeal R) := by
  refine ⟨hB.1, hB.1.2.2.2, hB.2, (maximalIdeal.isMaximal R).isPrime, ?_⟩
  letI := Ideal.Quotient.field (maximalIdeal R)
  infer_instance

end GlobalTheory.Mum.PreUnifEven


set_option maxHeartbeats 1600000 in
theorem GlobalTheory.Mum.exists_preU_even : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → EvenOn P → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ (D : DegPre R) (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G), U.P = P ∧ U.gen = gen := by
  intro R _ _ _ hB G _ _ P hs ⟨X, _, _, _, Q₀, P₀, hlev, hev⟩ A gen hgen hA
  obtain ⟨⟨hL, hL2, hL3, -, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hE := GlobalTheory.LN.ega_holds
  have hU := GlobalTheory.uniformisation_dvr_unconditional
  have hR := GlobalTheory.Mum.PreUnifEven.isAdmissibleCompleteLocalDomainPrime_of_completeNormal hB
  have hP : IsPrincipalIdealRing (R ⧸ maximalIdeal R) := by
    letI := Ideal.Quotient.field (maximalIdeal R)
    infer_instance
  obtain ⟨T⟩ := GlobalTheory.Mum.PreUnifEven.nonempty_towerR_of_even P hs Q₀ P₀ hlev hev
  have hI : maximalIdeal R ≠ ⊤ := hR.2.2.2.1.ne_top
  have := hR.1.1
  have hf := GlobalTheory.Mum.PreUnifEven.fibres hL hU R _ hR G P hs A gen hgen hA X T
  have := GlobalTheory.PreUnifLocal.isLocalRing_quot hI 0
  have e : maximalIdeal R ^ (0 + 1) = maximalIdeal R := pow_one _
  have : (maximalIdeal R ^ (0 + 1)).IsPrime := e.symm ▸ hR.2.2.2.1
  have : IsPrincipalIdealRing (R ⧸ maximalIdeal R ^ (0 + 1)) := e.symm ▸ hP
  have amp : RelAmple (T.l 0).Q.B (T.l 0).D.M.L.L :=
    _root_.GlobalTheory.CubicalFibreAmple.relAmple_of_fibres hL hL2 (R ⧸ maximalIdeal R ^ (0 + 1)) (GlobalTheory.PreUnifLocal.isAdicComplete_quot hR.2.1 _) _
      (T.l 0).Q.isAb (T.l 0).D.M fun k _ x => (hf k x).1
  obtain ⟨a⟩ := _root_.GlobalTheory.TowerAlg.nonempty_alg hL hL2 hE R _ hR G P X T amp
  have k₀ : KTriv (T.l 0).Q.B (T.l 0).D.M.L.L :=
    _root_.GlobalTheory.KTrivLocal.kTriv_of_closed_fibre hL hL2 (R ⧸ maximalIdeal R ^ (0 + 1)) _ (T.l 0).Q.isAb _ (T.l 0).D.M.L.isLB amp (hf _ _).2
  obtain ⟨hb, v, hv⟩ := a.b_pb 0
  have hK : KTriv a.B a.M.L.L := _root_.GlobalTheory.KTrivLocal.kTriv_of_closed_fibre hL hL2 R _ a.isAb _ a.M.L.isLB a.ample
    (GlobalTheory.PreUnifLocal.kTriv_closedFibre (e.symm ▸ hI) hb a.M.L.isLB (T.l 0).D.M.L.isLB hv.gen k₀)
  obtain ⟨c, hadd, hw⟩ := _root_.GlobalTheory.WeightPoint.exists_weightPoints hL hL2 hE R _ hR G P X T a hK
  exact GlobalTheory.PreUnifLocal.exists_preU hL.globalFns (fun D e => _root_.GlobalTheory.gtCoord_compat_of_torusCompat hL.globalFns R _ D e G) hI hs T a hK c hadd
    hw A gen hgen hA
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverSourceBirational
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

namespace GlobalTheory.Discrepancy

theorem DivOver.exists_over : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ E : DivOver p, ∃ E' : DivOver (s ≫ p), DivOver.Over s E' E := by
  intro k _ X Y _ _ p s _ hs E
  let e : X.functionField ≃+* Y.functionField := RingEquiv.ofBijective (functionFieldMap s) hs
  let V : ValuationSubring Y.functionField := E.ring.comap e.symm.toRingHom
  have hV (f : X.functionField) : f ∈ E.ring ↔ functionFieldMap s f ∈ V := by
    change f ∈ E.ring ↔ e.symm (e f) ∈ E.ring
    rw [e.symm_apply_apply]
  let φ : E.ring →+* V :=
    ((functionFieldMap s).comp E.ring.subtype).codRestrict V fun a => (hV _).1 a.2
  have hφ : Function.Bijective φ :=
    ⟨fun _ _ h => Subtype.ext (hs.1 (congrArg Subtype.val h)),
      fun f => ⟨⟨e.symm f.1, f.2⟩, Subtype.ext (e.apply_symm_apply f.1)⟩⟩
  have hc (a : k) : functionFieldMap s (Cartier.constFn p a) = Cartier.constFn (s ≫ p) a :=
    RingHom.congr_fun (GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p s) a
  refine ⟨⟨V, fun a => hc a ▸ (hV _).1 (E.const_mem a),
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (RingEquiv.ofBijective φ hφ), ?_⟩, hV⟩
  have h3 := E.essFiniteType.comp (RingHom.FiniteType.of_surjective φ hφ.2).essFiniteType
  convert h3 using 1
  exact RingHom.ext fun a => Subtype.ext (hc a).symm

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorOverTargetBirational
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

theorem DivOver.exists_over_of_bijective : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ E' : DivOver (s ≫ p), ∃ E : DivOver p, DivOver.Over s E' E := by
  intro k _ X Y _ _ p s _ hb E'
  have e := GlobalTheory.EtaleKlt.functionFieldMap_comp_constFn p s
  have hc : ∀ a, Cartier.constFn p a ∈ E'.ring.comap (functionFieldMap s) := fun a => by
    show functionFieldMap s (Cartier.constFn p a) ∈ E'.ring
    rw [← RingHom.comp_apply, e]; exact E'.const_mem a
  let ψ : E'.ring.comap (functionFieldMap s) →+* E'.ring :=
    (functionFieldMap s).restrict _ E'.ring fun _ hx => hx
  have hψb : Function.Bijective ψ := by
    refine ⟨fun x y h => Subtype.ext (hb.1 (congrArg Subtype.val h)), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hb.2 (y : Y.functionField)
    exact ⟨⟨x, show functionFieldMap s x ∈ E'.ring from hx ▸ y.2⟩, Subtype.ext hx⟩
  let eq : E'.ring.comap (functionFieldMap s) ≃+* E'.ring := RingEquiv.ofBijective ψ hψb
  have hdvr : IsDiscreteValuationRing (E'.ring.comap (functionFieldMap s)) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eq.symm
  have hcomp : eq.symm.toRingHom.comp
      ((Cartier.constFn (s ≫ p)).codRestrict E'.ring E'.const_mem) =
      (Cartier.constFn p).codRestrict _ hc := by
    refine RingHom.ext fun a => eq.injective ?_
    rw [RingHom.comp_apply]
    erw [RingEquiv.apply_symm_apply]
    exact Subtype.ext (RingHom.congr_fun e a).symm
  have hess : ((Cartier.constFn p).codRestrict _ hc).EssFiniteType := by
    rw [← hcomp]
    have h1 := E'.essFiniteType
    letI := ((Cartier.constFn (s ≫ p)).codRestrict E'.ring E'.const_mem).toAlgebra
    letI := (eq.symm.toRingHom.comp
      ((Cartier.constFn (s ≫ p)).codRestrict E'.ring E'.const_mem)).toAlgebra
    haveI : Algebra.EssFiniteType k E'.ring := h1
    let f : E'.ring →ₐ[k] E'.ring.comap (functionFieldMap s) :=
      { eq.symm.toRingHom with commutes' := fun _ => rfl }
    exact Algebra.EssFiniteType.of_surjective f eq.symm.surjective
  exact ⟨⟨E'.ring.comap (functionFieldMap s), hc, hdvr, hess⟩, fun _ => Iff.rfl⟩

end GlobalTheory.Discrepancy
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagChartFramesEigenFramesLocalRingStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagChartFrames_eigenFrames_localRing : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagCover Y), GlobalTheory.VarFlag.FramesExist X := by
  first | exact @GlobalTheory.VarFlag.framesExist_flagCover | exact GlobalTheory.VarFlag.framesExist_flagCover | (intros; apply GlobalTheory.VarFlag.framesExist_flagCover <;> assumption)
end

