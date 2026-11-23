module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ApplyLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0347
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapConstantCoeffEqOne
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

namespace GlobalTheory.NL.WachMat

section Series

open PowerSeries

variable {L : Type} [Field L] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem constantCoeff_rescale' (u : L) (f : L⟦X⟧) : constantCoeff (rescale u f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul, coeff_zero_eq_constantCoeff_apply]

theorem X_pow_dvd_rescale (u : L) (f : L⟦X⟧) (a : ℕ) (h : X ^ a ∣ f) : X ^ a ∣ rescale u f := by
  rw [X_pow_dvd_iff] at h ⊢
  intro m hm
  rw [coeff_rescale, h m hm, mul_zero]

theorem map_constantCoeff_eq_one (G : Matrix ι ι L⟦X⟧) (hG : ∀ i j, X ∣ (G - 1) i j) :
    G.map (constantCoeff (R := L)) = 1 := by
  ext i j
  have := X_dvd_iff.1 (hG i j)
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem X_pow_dvd_of_rescale (u : L) (hu0 : u ≠ 0) (hu : ∀ n : ℕ, n ≠ 0 → u ^ n ≠ 1) (w : L⟦X⟧) (hw : IsUnit w)
    (a : ℕ) (B G G₁ : Matrix ι ι L⟦X⟧) (hG : ∀ i j, X ∣ (G - 1) i j) (hG₁ : ∀ i j, X ∣ (G₁ - 1) i j)
    (h : (X * w) ^ a • (G * B.map (rescale u)) = (rescale u (X * w)) ^ a • (B * G₁)) :
    ∀ i j, X ^ a ∣ B i j := by
  have key : ∀ k, k ≤ a → ∀ i j, X ^ k ∣ B i j := by
    intro k
    induction k with
    | zero => intro _ i j; simp
    | succ k ih =>
      intro hk i j
      choose B' hB' using ih (by omega)
      have hB : B = (X : L⟦X⟧) ^ k • Matrix.of B' := by
        ext1 i j; rw [hB']; rfl
      have hBu : B.map (rescale u) = ((C u) ^ k * (X : L⟦X⟧) ^ k) • (Matrix.of B').map (rescale u) := by
        ext1 i j
        rw [Matrix.map_apply, hB', map_mul, map_pow, rescale_X, mul_pow]; rfl
      rw [hBu] at h
      rw [hB] at h
      simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, map_mul, rescale_X] at h
      have h1 := congrFun (congrFun h i) j
      simp only [Matrix.smul_apply, smul_eq_mul] at h1
      have h2 : w ^ a * C u ^ k * (G * (Matrix.of B').map (rescale u)) i j
          = C u ^ a * rescale u w ^ a * (Matrix.of B' * G₁) i j := by
        apply mul_left_cancel₀ (pow_ne_zero (a + k) (X_ne_zero (R := L)))
        linear_combination h1
      have h3 := congrArg (constantCoeff (R := L)) h2
      have e1 : constantCoeff ((G * (Matrix.of B').map (rescale u)) i j) = constantCoeff (B' i j) := by
        rw [← Matrix.map_apply (f := constantCoeff (R := L)), Matrix.map_mul, map_constantCoeff_eq_one G hG,
          Matrix.one_mul, Matrix.map_apply, Matrix.map_apply, constantCoeff_rescale']
        rfl
      have e2 : constantCoeff ((Matrix.of B' * G₁) i j) = constantCoeff (B' i j) := by
        rw [← Matrix.map_apply (f := constantCoeff (R := L)), Matrix.map_mul, map_constantCoeff_eq_one G₁ hG₁,
          Matrix.mul_one, Matrix.map_apply]
        rfl
      simp only [map_mul, map_pow, constantCoeff_C, constantCoeff_rescale', e1, e2] at h3
      have hw0 : constantCoeff w ≠ 0 := (isUnit_iff_constantCoeff.1 hw).ne_zero
      obtain ⟨d, rfl⟩ : ∃ d, a = k + (d + 1) := ⟨a - (k + 1), by omega⟩
      have h4 : (constantCoeff w ^ (k + (d + 1)) * u ^ k * (u ^ (d + 1) - 1)) * constantCoeff (B' i j) = 0 := by
        linear_combination -h3
      have h5 : constantCoeff (B' i j) = 0 :=
        (mul_eq_zero.1 h4).resolve_left (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hw0) (pow_ne_zero _ hu0))
          (sub_ne_zero.2 (hu _ (by omega))))
      rw [hB', pow_succ]
      exact mul_dvd_mul_left _ (X_dvd_iff.2 h5)
  exact key a le_rfl

end Series

theorem pow_smul_eq {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι] (Q : R) (m m' : ℕ)
    (B B' Pm P₁ P₁' : Matrix ι ι R) (h1 : P₁ * P₁' = (Q ^ m') • (1 : Matrix ι ι R))
    (h2 : Pm * B' = (Q ^ m) • (B * P₁)) : Q ^ (m + m') • B = Pm * B' * P₁' := by
  rw [h2, Matrix.smul_mul, Matrix.mul_assoc, h1, Matrix.mul_smul, Matrix.mul_one, smul_smul, pow_add]

theorem dvd_map_of_pow_smul_eq {R S ι : Type} [CommRing R] [CommRing S] [Fintype ι] (f : R →+* S) (Q : R)
    (hQ : IsUnit (f Q)) (m : ℕ) (B B' Pm P₁' : Matrix ι ι R) (h : Q ^ m • B = Pm * B' * P₁') (x : S)
    (hx : ∀ i j, x ∣ f (B' i j)) (i j : ι) : x ∣ f (B i j) := by
  have h1 := congrArg f (congrFun (congrFun h i) j)
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow] at h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← (hQ.pow m).dvd_mul_left, h1, Matrix.mul_apply, map_sum]
  refine Finset.dvd_sum fun k _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, Matrix.mul_apply, map_sum]
  refine Dvd.dvd.mul_right (Finset.dvd_sum fun k' _ => ?_) _
  rw [map_mul]
  exact (hx _ _).mul_left _


set_option maxHeartbeats 1600000 in
theorem X_pow_dvd_entry : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ (r a m m' : ℕ) (B G G₁ Pm P₁ P₁' : Matrix (Fin r) (Fin r) (AA K LL)), (∀ i j, (G - 1) i j ∈ Ideal.span {(letπ : AA K LL)}) → (∀ i j, (G₁ - 1) i j ∈ Ideal.span {(letπ : AA K LL)}) → (W.X ^ a) • (G * B.map (W.γA W.gam)) = (W.γA W.gam W.X ^ a) • (B * G₁) → P₁ * P₁' = (W.Q ^ m') • (1 : Matrix (Fin r) (Fin r) (AA K LL)) → Pm * B.map W.φA = (W.Q ^ m) • (B * P₁) → ∀ i j, W.X ^ a ∣ B i j := by
  intro D HW l hl K s LL h W r a m m' B G G₁ Pm P₁ P₁' hG hG₁ hγ hP hφ
  obtain ⟨Lγ, Lφ⟩ : LevLaws W := GlobalTheory.NL.Expansion.levLaws D HW l K s LL h
  have Lp := GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h
  obtain ⟨χ, hχ, -, -, -, -, hgam, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨-, Wd, -⟩ := GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  rw [hp] at Lγ Lφ
  have hroot : ∀ (j : ℕ) (ζ : ↥LL.1), ζ ^ (l ^ j) = 1 → ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by
    intro j ζ h1
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl.out).1 (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨k, hk ▸ IsPrimitiveRoot.orderOf ζ⟩
  set u : ↥LL.1 := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)) with hudef
  have hu0 : u ≠ 0 := ((W.χΓ W.gam).isUnit.map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero
  have hu : ∀ n : ℕ, n ≠ 0 → u ^ n ≠ 1 := by
    intro n hn h1
    have h2 := GlobalTheory.Cyc.norm_unit_zpow_sub_one l s (χ W.gam) h.1 h.2.1 hgam n (by exact_mod_cast hn)
    have h3 : ((χ W.gam : ℤ_[l]ˣ) : ℤ_[l]) ^ n = 1 := by
      have inj : Function.Injective (algebraMap ℤ_[l] ↥LL.1) := by
        rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
        exact (algebraMap ℚ_[l] ↥LL.1).injective.comp Subtype.val_injective
      apply inj
      rw [map_pow, map_one, IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL) ↥LL.1, hχ]
      exact h1
    rw [zpow_natCast, Units.val_pow_eq_pow_val, h3, sub_self, norm_zero] at h2
    have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
    refine mul_ne_zero (zpow_pos hl0 _).ne' (norm_ne_zero_iff.2 ?_) h2.symm
    exact_mod_cast hn
  have base : ∀ (i : Let K) p q, PowerSeries.X ^ a ∣ W.lev i 1 (B p q) := by
    intro i
    have r1 : IsPrimitiveRoot (1 : ↥LL.1) (l ^ 0) := by
      rw [pow_zero]; exact IsPrimitiveRoot.one
    obtain ⟨⟨x, -, hx, w₀, -, hπ⟩, -, hX, -⟩ := Lp i 1 ⟨0, r1⟩
    obtain ⟨⟨w, hw, hX⟩, -⟩ := hX (one_pow _)
    rw [hx, sub_self, map_zero, zero_add] at hπ
    have hγ1 : ∀ f, W.lev i 1 (W.γA W.gam f) = PowerSeries.rescale u (W.lev i 1 f) := by
      refine Lγ W.gam i 1 1 0 1 r1 ?_ (one_pow _).symm
      rw [Nat.cast_one, W.gam_gen]
      exact_mod_cast Nat.zero_le _
    have hone : ∀ G : Matrix (Fin r) (Fin r) (AA K LL), (∀ p q, (G - 1) p q ∈ Ideal.span {(letπ : AA K LL)}) →
        ∀ p q, PowerSeries.X ∣ (G.map (W.lev i 1) - 1) p q := by
      intro G hG p q
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hG p q)
      have e : (G.map (W.lev i 1) - 1) p q = W.lev i 1 ((G - 1) p q) := by
        rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [e, hc, map_mul, hπ, mul_assoc]
      exact dvd_mul_right _ _
    refine X_pow_dvd_of_rescale u hu0 hu w hw a (B.map (W.lev i 1)) (G.map (W.lev i 1)) (G₁.map (W.lev i 1))
      (hone G hG) (hone G₁ hG₁) ?_
    ext1 p q
    have h1 := congrArg (W.lev i 1) (congrFun (congrFun hγ p) q)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, map_mul, map_pow, map_sum,
      hγ1] at h1
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, ← hX]
    exact h1
  have hB := pow_smul_eq W.Q m m' B (B.map W.φA) Pm P₁ P₁' hP hφ
  have step : ∀ j : ℕ, j ≤ s - 1 → ∀ (i : Let K) (ζ : ↥LL.1), ζ ^ (l ^ j) = 1 → ∀ p q,
      PowerSeries.X ^ a ∣ W.lev i ζ (B p q) := by
    intro j
    induction j with
    | zero =>
      intro _ i ζ hζ
      rw [pow_zero, pow_one] at hζ
      subst hζ
      exact base i
    | succ j ih =>
      intro hj i ζ hζ
      have hr := hroot _ ζ hζ
      have hζ' : ζ ^ (l ^ (s - 1)) = 1 := by
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
        rw [hd, pow_add, pow_mul, hζ, one_pow]
      obtain ⟨-, -, hX, -⟩ := Lp i ζ hr
      obtain ⟨-, hQ⟩ := hX hζ'
      refine dvd_map_of_pow_smul_eq (W.lev i ζ : AA K LL →+* PowerSeries ↥LL.1) W.Q hQ _ B _ Pm P₁' hB _ fun p q => ?_
      change _ ∣ W.lev i ζ (W.φA (B p q))
      rw [Lφ i ζ hr]
      refine X_pow_dvd_rescale _ _ _ (ih (by omega) _ _ ?_ p q)
      rw [← pow_mul, ← pow_succ', hζ]
  intro p q
  refine Wd a (B p q) fun i ζ hζ => ?_
  exact Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 (step _ le_rfl i ζ hζ p q))

end GlobalTheory.NL.WachMat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixComputesTwistedSelmerResidualTransfer
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
open GlobalTheory.ResSel.CoefMap

namespace GlobalTheory.ResSel.Transfer

section Alg

variable {O Λ K : Type} [CommRing O] [CommRing Λ] [CommRing K] [Algebra O Λ] [Algebra O K] [Module Λ K]
  (φ : Λ →ₐ[O] K) (hs : ∀ (y : Λ) (b : K), y • b = φ y * b)

def idVec (r : ℕ) : (Fin r → K) →ₛₗ[(φ : Λ →+* K)] (Fin r → K) where
  toFun m := m
  map_add' _ _ := rfl
  map_smul' c m := funext fun a => hs c (m a)

include hs in
theorem matAct_eq {n : ℕ} (Φ : Matrix (Fin n) (Fin n) Λ) (x : Fin n → K) :
    matAct (M := K) Φ x = (Φ.map φ).mulVec x := by
  funext a
  simp [matAct, hs, Matrix.mulVec, dotProduct]

include hs in
theorem repOn_eq {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ) (g : Γ) (m : Fin r → K) :
    repOn ρ κ K g m = φ ((κ g : Λˣ) : Λ) • ((ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O K)).mulVec m := by
  funext a
  simp [repOn, matAct, hs, Matrix.mulVec, dotProduct]

theorem idVec_repOn {Γ : Type} [Group Γ] {r : ℕ} (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ)
    (hκ : ∀ g, φ ((κ g : Λˣ) : Λ) = 1) (g : Γ) (m : Fin r → K) :
    idVec φ hs r (repOn ρ κ K g m) = repOn ρ (1 : Γ →* Kˣ) K g (idVec φ hs r m) := by
  change repOn ρ κ K g m = repOn ρ (1 : Γ →* Kˣ) K g m
  rw [repOn_eq φ hs, hκ]
  funext a
  simp [repOn, matAct, Matrix.mulVec, dotProduct]

variable [TopologicalSpace K] [DiscreteTopology K] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {r : ℕ}
  (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Λˣ) (hκ : ∀ g, φ ((κ g : Λˣ) : Λ) = 1)

def tau : H1 (repOn ρ κ K) →ₛₗ[(φ : Λ →+* K)] H1 (repOn ρ (1 : Γ →* Kˣ) K) :=
  slH1 _ _ (idVec φ hs r) continuous_of_discreteTopology (idVec_repOn φ hs ρ κ hκ)

theorem tau_injective : Function.Injective (tau φ hs ρ κ hκ) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    have h1 : (Submodule.Quotient.mk (semilinearCoefficientMapCocycles _ _ (idVec φ hs r) continuous_of_discreteTopology
      (idVec_repOn φ hs ρ κ hκ) z) : H1 (repOn ρ (1 : Γ →* Kˣ) K)) = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at h1 ⊢
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h1
    refine (mem_coboundaries1 _ _).2 ⟨m, fun g => ?_⟩
    have e : repOn ρ κ K g m = repOn ρ (1 : Γ →* Kˣ) K g m := idVec_repOn φ hs ρ κ hκ g m
    rw [e]
    exact hm g

def kerIn {n : ℕ} (Φ : Matrix (Fin n) (Fin n) Λ) (x : LinearMap.ker (Φ.map φ).mulVecLin) :
    LinearMap.ker (matAct (M := K) Φ) :=
  ⟨x.1, by rw [LinearMap.mem_ker, matAct_eq φ hs]; exact x.2⟩

theorem exists_linear (hsurj : Function.Surjective (algebraMap O K)) {n : ℕ} (Φ : Matrix (Fin n) (Fin n) Λ)
    (S : Submodule Λ (H1 (repOn ρ κ K))) (e : LinearMap.ker (matAct (M := K) Φ) ≃ₗ[Λ] S) :
    ∃ E : LinearMap.ker (Φ.map φ).mulVecLin →ₗ[K] H1 (repOn ρ (1 : Γ →* Kˣ) K), Function.Injective E ∧
      ∀ x, E x = tau φ hs ρ κ hκ (e (kerIn φ hs Φ x)).1 := by
  refine ⟨{ toFun := fun x => tau φ hs ρ κ hκ (e (kerIn φ hs Φ x)).1
            map_add' := fun x y => ?_
            map_smul' := fun c x => ?_ }, fun x y hxy => ?_, fun _ => rfl⟩
  · rw [show kerIn φ hs Φ (x + y) = kerIn φ hs Φ x + kerIn φ hs Φ y from rfl, map_add (f := _), Submodule.coe_add, map_add (f := _)]
  · obtain ⟨o, rfl⟩ := hsurj c
    have h1 : kerIn φ hs Φ (algebraMap O K o • x) = algebraMap O Λ o • kerIn φ hs Φ x := by
      apply Subtype.ext
      funext b
      change algebraMap O K o * x.1 b = algebraMap O Λ o • x.1 b
      rw [hs, AlgHom.commutes]
    rw [h1, map_smul, Submodule.coe_smul, map_smulₛₗ, RingHom.id_apply]
    congr 1
    exact φ.commutes o
  · have h1 := e.injective (Subtype.ext (tau_injective φ hs ρ κ hκ hxy))
    have h2 : (kerIn φ hs Φ x).1 = (kerIn φ hs Φ y).1 := congrArg Subtype.val h1
    exact Subtype.ext h2

end Alg

section Sel

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
  (i : X.Tw) {r : ℕ} (ρ : GE N →* GL (Fin r) (X.O0 i))
  {Λ K : Type} [CommRing Λ] [Algebra (X.O0 i) Λ] [CommRing K] [Algebra (X.O0 i) K] [Module Λ K]
  [TopologicalSpace K] [DiscreteTopology K]
  (φ : Λ →ₐ[X.O0 i] K) (hs : ∀ (y : Λ) (b : K), y • b = φ y * b) (κ : GE N →* Λˣ) (hκ : ∀ g, φ ((κ g : Λˣ) : Λ) = 1)

theorem tau_mem_bkOn (v : PlE D.host) (x : H1 ((repOn ρ κ K).comp (DecV N v).subtype))
    (hx : x ∈ bkOn bkP i ρ κ K v) :
    slH1 ((repOn ρ κ K).comp (DecV N v).subtype) ((repOn ρ (1 : GE N →* Kˣ) K).comp (DecV N v).subtype)
      (idVec φ hs r) continuous_of_discreteTopology (fun g m => idVec_repOn φ hs ρ κ hκ g.1 m) x ∈
      bkOn bkP i ρ (1 : GE N →* Kˣ) K v := by
  unfold bkOn at hx ⊢
  split_ifs at hx ⊢ with hv
  · induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, c, y, b, hc, hy, hz, rfl⟩ := hx
      refine Submodule.subset_span ⟨semilinearCoefficientMapCocycles _ _ (idVec φ hs r) continuous_of_discreteTopology
        (fun g m => idVec_repOn φ hs ρ κ hκ g.1 m) z, c, y, b, hc, hy, fun g a => ?_, rfl⟩
      change ((z : ↥(DecV N v) → Fin r → K) g a) = _
      rw [hz, smul_eq_mul, hs, AlgHom.commutes]
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem tau_mem_selOn (Q : Finset (PlE D.host)) (x : H1 (repOn ρ κ K)) (hx : x ∈ selOn bkP i ρ κ K Q) :
    tau φ hs ρ κ hκ x ∈ selOn bkP i ρ (1 : GE N →* Kˣ) K Q := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_slH1 (repOn ρ κ K) (repOn ρ (1 : GE N →* Kˣ) K) (idVec φ hs r) continuous_of_discreteTopology
    (idVec_repOn φ hs ρ κ hκ) (Dec (F := D.host.E) (N.plOm.1 v)).subtype continuous_subtype_val x) ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · exact tau_mem_bkOn bkP i ρ φ hs κ hκ v _ hv
  · exact Submodule.mem_top
  · exact slH1_ur _ _ _ _ _ _ _ hv

end Sel

theorem tors_of_cast_eq_zero {B : Type} [CommRing B] {l : ℕ} (h : (l : B) = 0) (b : B) : ∃ n : ℕ, (l ^ n) • b = 0 :=
  ⟨1, by rw [pow_one, nsmul_eq_mul, h, zero_mul]⟩

theorem computes_transfer : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (M : ℕ) (ι : Type) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ → ∀ (k : Type) [Field k] [Algebra (X.O0 i) k] [TopologicalSpace k] [DiscreteTopology k], ((X.l i : ℕ) : k) = 0 → Function.Surjective (algebraMap (X.O0 i) k) → ∀ aug : abelian₂ X i M ι →ₐ[X.O0 i] k, (∀ δ, aug (MonoidAlgebra.of (X.O0 i) (Del X i M ι) δ) = 1) → ∃ E : LinearMap.ker (Φ.map aug).mulVecLin →ₗ[k] H1 (red i k (Tgl i s)), Function.Injective E ∧ (∀ x, E x ∈ selOn bkP i (Tgl i s) (1 : GE N →* kˣ) k Q) ∧ ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (th : abelian₂ X i M ι →ₐ[X.O0 i] B), ((X.l i : ℕ) : B) = 0 → ∀ x : Fin a → B, (Φ.map th).mulVec x = 0 → ∃ z : GE N → Fin D.R.r → B, IsLocallyConstant z ∧ (∀ g h, z (g * h) = z g + th ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) • ((Tmat i s g).map (algebraMap (X.O0 i) B)).mulVec (z h)) ∧ ∀ f : B →+ k, (∀ y b, f (th y * b) = aug y * f b) → ∃ (x' : LinearMap.ker (Φ.map aug).mulVecLin) (z' : Z1 (red i k (Tgl i s))), (∀ c, x'.1 c = f (x c)) ∧ (∀ g c, z'.1 g c = f (z g c)) ∧ E x' = cl z' := by
  intro D N X bkP i s M ι d Q a Φ hC k _ _ _ _ hk hsurj aug haug
  obtain ⟨e, he⟩ := hC
  letI : Module (abelian₂ X i M ι) k := Module.compHom k (aug : abelian₂ X i M ι →+* k)
  have hs : ∀ (y : abelian₂ X i M ι) (b : k), y • b = aug y * b := fun _ _ => rfl
  have hκ : ∀ g, aug ((delInv i M d g : (abelian₂ X i M ι)ˣ) : abelian₂ X i M ι) = 1 := fun g =>
    haug (delAll X i M d g)⁻¹
  have hkT := tors_of_cast_eq_zero hk
  obtain ⟨E, hEi, hE⟩ := exists_linear aug hs (Tgl i s) (delInv i M d) hκ hsurj Φ _ (e k hkT)
  refine ⟨E, hEi, fun x => ?_, ?_⟩
  · rw [hE]
    exact tau_mem_selOn bkP i _ aug hs _ hκ Q _ (e k hkT (kerIn aug hs Φ x)).2
  intro B _ _ th hB x hx
  letI : Module (abelian₂ X i M ι) B := Module.compHom B (th : abelian₂ X i M ι →+* B)
  have hsB : ∀ (y : abelian₂ X i M ι) (b : B), y • b = th y * b := fun _ _ => rfl
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  have hBT := tors_of_cast_eq_zero hB
  let xB : LinearMap.ker (matAct (M := B) Φ) := ⟨x, by rw [LinearMap.mem_ker, matAct_eq th hsB]; exact hx⟩
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (e B hBT xB).1
  refine ⟨z.1, (IsLocallyConstant.iff_continuous _).2 z.2.1, fun g h => ?_, fun f hf => ?_⟩
  · rw [z.2.2 g h, repOn_eq th hsB, Tgl_coe]
  let fl : B →ₗ[abelian₂ X i M ι] k :=
    { toFun := f
      map_add' := map_add f
      map_smul' := fun y b => hf y b }
  have hx' : (Φ.map aug).mulVec (fun c => f (x c)) = 0 := by
    funext c
    have h1 := congrArg f (congrFun hx c)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Matrix.mulVec, dotProduct, map_sum, hf] using h1
  let z₁ : Z1 (repOn (Tgl i s) (delInv i M d) k) :=
    cocycles1MapOfEquivariant _ _ (fl.compLeft (Fin D.R.r)) continuous_of_discreteTopology (repOn_map (Tgl i s) (delInv i M d) fl) z
  refine ⟨⟨fun c => f (x c), hx'⟩, semilinearCoefficientMapCocycles _ _ (idVec aug hs D.R.r) continuous_of_discreteTopology
    (idVec_repOn aug hs (Tgl i s) (delInv i M d) hκ) z₁, fun _ => rfl, fun _ _ => rfl, ?_⟩
  rw [hE, he B k hBT hkT fl xB (kerIn aug hs Φ ⟨fun c => f (x c), hx'⟩) z z₁ (fun _ => rfl) (fun _ _ => rfl) hz.symm]
  rfl

end GlobalTheory.ResSel.Transfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNonZeroDivisorsOfInvertibleSpanSingleton
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem invertible_eq_zero_of_smul_eq_zero {A : Type} [CommRing A] {M : Type} [AddCommGroup M]
    [Module A M] [Module.Invertible A M] (a : A) (h : ∀ m : M, a • m = 0) : a = 0 := by
  obtain ⟨t, ht⟩ := (Module.Invertible.bijective (R := A) (M := M)).2 1
  have hz : ∀ s : Module.Dual A M ⊗[A] M, a • s = 0 := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => exact smul_zero a
    | tmul f m => rw [← TensorProduct.tmul_smul, h m, TensorProduct.tmul_zero]
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  have : a = contractLeft A M (a • t) := by rw [map_smul, ht, smul_eq_mul, mul_one]
  rw [this, hz t, map_zero]

theorem mem_nonZeroDivisors_of_invertible_span_singleton : ∀ (A : Type) [CommRing A] (d : A),
    Module.Invertible A ↥(Ideal.span {d}) → d ∈ nonZeroDivisors A := by
  intro A _ d hinv
  rw [mem_nonZeroDivisors_iff_right]
  intro a had
  apply invertible_eq_zero_of_smul_eq_zero (M := ↥(Ideal.span {d})) a
  rintro ⟨m, hm⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hm
  ext
  simp only [Submodule.coe_smul, smul_eq_mul, ZeroMemClass.coe_zero]
  calc a * (c * d) = c * (a * d) := by ring
    _ = 0 := by rw [had, mul_zero]

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPowOfMulMemPowBoundedTorsion
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem div_d_continuous_of_bdd_ltorsion :
    ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (d : A) (N : ℕ), d ∈ nonZeroDivisors A →
      (∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d}) →
      ∀ (n : ℕ) (z : A), d * z ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ (2 * (n + N + 1)) →
        z ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ n := by
  intro l _ A _ d N hd hN n z hz
  set m := n + N + 1 with hm
  have h2 : 2 * m = m + m := by ring
  rw [h2] at hz
  have h1 := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(l : A)}) (J := Ideal.span {d})
    (m := m) (n := m) hz
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at h1
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hv

  have hdm : d ^ m = d * d ^ (n + N) := by rw [hm, pow_succ]; ring
  have hla : (l : A) ^ m * a ∈ Ideal.span {d} := by
    rw [Ideal.mem_span_singleton']
    exact ⟨z - b * d ^ (n + N), by rw [hdm] at huv; linear_combination -huv⟩
  obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.1 (hN a m hla)

  have hmN : m = (n + 1) + N := by rw [hm]; ring
  have key : d * (z - (l : A) ^ (n + 1) * a' - b * d ^ (n + N)) = 0 := by
    have : (l : A) ^ m * a = (l : A) ^ (n + 1) * (a' * d) := by
      rw [ha', hmN, pow_add]; ring
    rw [hdm] at huv
    linear_combination (-1 : A) * huv + this
  have hz' : z = (l : A) ^ (n + 1) * a' + b * d ^ (n + N) := by
    have := (mem_nonZeroDivisors_iff.1 hd).1 _ key
    linear_combination this
  rw [hz']
  refine Ideal.add_mem _ ?_ ?_
  · refine Ideal.mul_mem_right _ _ ?_
    have : (l : A) ^ (n + 1) ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ (n + 1) :=
      Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) _
    exact Ideal.pow_le_pow_right (Nat.le_succ n) this
  · refine Ideal.mul_mem_left _ _ ?_
    have : d ^ (n + N) ∈ (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ^ (n + N) :=
      Ideal.pow_mem_pow (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) _
    exact Ideal.pow_le_pow_right (Nat.le_add_right n N) this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootOfUnityPadicComplexMemRangeAlgClosure
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem rootOfUnity_mem_range_Om : ∀ (l : ℕ) [Fact l.Prime] (x : ℂ_[l]) (m : ℕ), 0 < m → x ^ m = 1 → ∃ z : Om l, (z : ℂ_[l]) = x := by
  intro l _ x m hm hx
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) m
  have hζ' : IsPrimitiveRoot (algebraMap (Om l) ℂ_[l] ζ) m :=
    hζ.map_of_injective (algebraMap (Om l) ℂ_[l]).injective
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one hx
  exact ⟨ζ ^ i, by rw [← hi]; exact map_pow (algebraMap (Om l) ℂ_[l]) ζ i⟩

end GlobalTheory
end

