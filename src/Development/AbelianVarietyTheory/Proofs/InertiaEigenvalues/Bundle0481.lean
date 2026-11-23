module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0452
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatible
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
public import GroundTheory.GlobalFields.Adele.Discrete
public import GroundTheory.GlobalFields.Adele.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Formalism.WeaklyAdmissibleFiltrations.Statement

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrthogonalIdempotentsHeckeSpanRep
section
noncomputable section

namespace GlobalTheory.SpanIdem

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

variable {Γ X A : Type} [Group Γ] [CommRing A] {n r t : ℕ}

theorem overK_apply {k : ℕ} (σ : Γ →* GL (Fin k) A) (g : Γ) (u : Fin k → FractionRing A) :
    overK σ g u = ((mat σ g).map (toFr A)).mulVec u := rfl

theorem map_smul_mulVec {k : ℕ} (c : A) (M : Matrix (Fin k) (Fin k) A) (u : Fin k → FractionRing A) :
    ((c • M).map (toFr A)).mulVec u = toFr A c • (M.map (toFr A)).mulVec u := by
  rw [← Matrix.smul_mulVec]
  congr 1
  ext i j
  simp

theorem map_sum_mulVec {k m : ℕ} (M : Fin m → Matrix (Fin k) (Fin k) A) (u : Fin k → FractionRing A) :
    ((∑ i, M i).map (toFr A)).mulVec u = ∑ i, ((M i).map (toFr A)).mulVec u := by
  rw [← Matrix.sum_mulVec]
  congr 1
  exact map_sum (toFr A).mapMatrix M Finset.univ

theorem map_mul_mulVec {k : ℕ} (M N : Matrix (Fin k) (Fin k) A) (u : Fin k → FractionRing A) :
    ((M * N).map (toFr A)).mulVec u = (M.map (toFr A)).mulVec ((N.map (toFr A)).mulVec u) := by
  rw [Matrix.map_mul, Matrix.mulVec_mulVec]

theorem map_one_sub_mulVec {k : ℕ} (M : Matrix (Fin k) (Fin k) A) (u : Fin k → FractionRing A) :
    ((1 - M).map (toFr A)).mulVec u = u - (M.map (toFr A)).mulVec u := by
  have : (1 - M).map (toFr A) = 1 - M.map (toFr A) := by
    have h := map_sub (toFr A).mapMatrix 1 M
    rw [map_one] at h
    exact h
  rw [this, Matrix.sub_mulVec, Matrix.one_mulVec]

theorem eq_of_mulVec {k : ℕ} {M N : Matrix (Fin k) (Fin k) A}
    (h : ∀ u, (M.map (toFr A)).mulVec u = (N.map (toFr A)).mulVec u) : M = N := by
  have h1 : M.map (toFr A) = N.map (toFr A) := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_apply, h]
  exact Matrix.map_injective (IsFractionRing.injective A (FractionRing A)) h1

theorem exists_corner (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (ρ : Γ →* GL (Fin r) A)
    (χ : ℕ → (Γ →* Aˣ)) (π : X)
    (e : (Fin n → FractionRing A) ≃ₗ[FractionRing A] ((Fin r → FractionRing A) × (Fin t → FractionRing A)))
    (hr : 2 ≤ r) (hs : Submodule.span A (Set.range (mat ρ)) = ⊤) (hd : IsDecomp (t := t) (rep π) ρ χ e)
    (P : Matrix (Fin r) (Fin r) A) :
    ∃ a, InRing T rep a ∧
      ∀ u, e (((a π).map (toFr A)).mulVec u) = ((P.map (toFr A)).mulVec (e u).1, 0) := by
  obtain ⟨m, f, h, hP, hχ⟩ := _root_.GlobalTheory.MatCorner.exists_comb_kills_chars ρ χ hr hs P
  refine ⟨∑ k, f k • fun x => mat (rep x) (h k),
    inRing_sum _ fun k _ => inRing_smul _ (inRing_mat _), fun u => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_apply, map_sum_mulVec, map_sum, ← hP, map_sum_mulVec]
  have key : ∀ k, e ((((f k • fun x => mat (rep x) (h k)) π).map (toFr A)).mulVec u) =
      (((f k • mat ρ (h k)).map (toFr A)).mulVec (e u).1,
        fun c : Fin t => toFr A (f k * ((χ ((c : ℕ) + 1) (h k) : Aˣ) : A)) * (e u).2 c) := by
    intro k
    rw [Pi.smul_apply, map_smul_mulVec, map_smul, ← overK_apply, hd, map_smul_mulVec, overK_apply]
    refine Prod.ext rfl ?_
    funext c
    simp [mul_assoc]
    simp [Algebra.smul_def]
  simp only [key]
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_sum]
  · rw [Prod.snd_sum]
    funext c
    rw [Finset.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← Finset.sum_mul, ← map_sum, hχ, map_zero, zero_mul, Pi.zero_apply]

theorem pow_succ_eval {b : X → Matrix (Fin n) (Fin n) A} {π : X} (h : b π * b π = b π) (k : ℕ) :
    (b ^ (k + 1)) π = b π := by
  rw [Pi.pow_apply]
  exact IsIdempotentElem.pow_succ_eq k h

theorem exists_idem (l : ℕ) [Fact l.Prime] [Finite X] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A]
    (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (π : X)
    (b : X → Matrix (Fin n) (Fin n) A) (hb : InRing T rep b) (hπ : b π * b π = b π) :
    ∃ E, InRing T rep E ∧ E * E = E ∧ E π = b π ∧ (∀ y, y * b = 0 → y * E = 0) ∧
      (∀ y, b * y = 0 → E * y = 0) := by
  haveI : Module.Finite ℤ_[l] (Matrix (Fin n) (Fin n) A) :=
    inferInstanceAs (Module.Finite ℤ_[l] (Fin n → Fin n → A))
  obtain ⟨E, hE, hM⟩ := _root_.GlobalTheory.exists_idempotent_sub_mem_of_pow_sub_mem l b
  refine ⟨E, ?_, hE, ?_, fun y hy => ?_, fun y hy => ?_⟩
  · have := hM ((Subalgebra.toSubmodule (ringR T rep)).restrictScalars ℤ_[l]) 0 fun k => by
      rw [sub_zero]
      exact pow_mem ((mem_ringR T rep b).2 hb) (k + 1)
    rw [sub_zero] at this
    exact (mem_ringR T rep E).1 this
  · have := hM (LinearMap.ker (LinearMap.proj π)) b fun k => by
      rw [LinearMap.mem_ker, LinearMap.proj_apply, Pi.sub_apply, pow_succ_eval hπ, sub_self]
    rw [LinearMap.mem_ker, LinearMap.proj_apply, Pi.sub_apply] at this
    exact sub_eq_zero.1 this
  · have := hM (LinearMap.ker (LinearMap.mulLeft ℤ_[l] y)) 0 fun k => by
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, sub_zero, pow_succ', ← mul_assoc, hy, zero_mul]
    rwa [LinearMap.mem_ker, LinearMap.mulLeft_apply, sub_zero] at this
  · have := hM (LinearMap.ker (LinearMap.mulRight ℤ_[l] y)) 0 fun k => by
      rw [LinearMap.mem_ker, LinearMap.mulRight_apply, sub_zero, pow_succ, mul_assoc, hy, mul_zero]
    rwa [LinearMap.mem_ker, LinearMap.mulRight_apply, sub_zero] at this

theorem rank_single {K : Type} [Field K] (i : Fin r) :
    (Matrix.single i i (1 : K)).rank = 1 := by
  classical
  have : Matrix.single i i (1 : K) = Matrix.diagonal (Pi.single i 1) := by
    ext a b
    simp only [Matrix.single_apply, Matrix.diagonal_apply, Pi.single_apply]
    grind
  rw [this, Matrix.rank_diagonal]
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨i, by simp⟩, ?_⟩
  rintro ⟨a, ha⟩
  apply Subtype.ext
  by_contra h
  exact ha (Pi.single_eq_of_ne h 1)

theorem exists_orthogonal_idempotents : ∀ (l : ℕ) [Fact l.Prime] {Γ X A : Type} [Group Γ] [Finite X] [CommRing A] [IsDomain A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A] {n r t : ℕ} (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (π : X) (e : (Fin n → FractionRing A) ≃ₗ[FractionRing A] ((Fin r → FractionRing A) × (Fin t → FractionRing A))), 2 ≤ r → Submodule.span A (Set.range (mat ρ)) = ⊤ → IsDecomp (t := t) (rep π) ρ χ e → ∃ eB e1 : X → Matrix (Fin n) (Fin n) A, (InRing T rep eB ∧ InRing T rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧ e1 * eB = 0) ∧ (∀ u, e (((eB π).map (toFr A)).mulVec u) = (0, (e u).2)) ∧ ∃ ε : Matrix (Fin r) (Fin r) (FractionRing A), ε.rank = 1 ∧ ∀ u, e (((e1 π).map (toFr A)).mulVec u) = (ε.mulVec (e u).1, 0) := by
  intro l _ Γ X A _ _ _ _ _ _ n r t T rep ρ χ π e hr hs hd
  obtain ⟨a, ha, hact⟩ := exists_corner T rep ρ χ π e hr hs hd 1
  have hb : ∀ u, e ((((1 - a) π).map (toFr A)).mulVec u) = (0, (e u).2) := by
    intro u
    rw [Pi.sub_apply, Pi.one_apply, map_one_sub_mulVec, map_sub, hact,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    exact Prod.ext (by simp) (by simp)
  obtain ⟨eB, hB, hBB, hBπ, -, -⟩ := exists_idem l T rep π (1 - a) (inRing_sub inRing_one ha) (by
    apply eq_of_mulVec
    intro u
    apply e.injective
    rw [map_mul_mulVec, hb, hb])
  rw [← hBπ] at hb
  let i : Fin r := ⟨0, by omega⟩
  obtain ⟨a', ha', hact'⟩ := exists_corner T rep ρ χ π e hr hs hd (Matrix.single i i 1)
  have hε : (Matrix.single i i (1 : A)).map (toFr A) = Matrix.single i i 1 := by
    rw [Matrix.map_single, map_one]
  rw [hε] at hact'
  have hc : ∀ u, e ((((1 - eB) π).map (toFr A)).mulVec u) = ((e u).1, 0) := by
    intro u
    rw [Pi.sub_apply, Pi.one_apply, map_one_sub_mulVec, map_sub, hb]
    exact Prod.ext (by simp) (by simp)
  have hb' : ∀ u, e (((((1 - eB) * a' * (1 - eB)) π).map (toFr A)).mulVec u) =
      ((Matrix.single i i 1).mulVec (e u).1, 0) := by
    intro u
    rw [Pi.mul_apply, Pi.mul_apply, map_mul_mulVec, map_mul_mulVec, hc, hact', hc]
  have h1 := inRing_sub inRing_one hB
  obtain ⟨e1, h1R, h11, h1π, hl, hrr⟩ := exists_idem l T rep π ((1 - eB) * a' * (1 - eB))
    (inRing_mul (inRing_mul h1 ha') h1) (by
      apply eq_of_mulVec
      intro u
      apply e.injective
      rw [map_mul_mulVec, hb', hb', Matrix.mulVec_mulVec, Matrix.single_mul_single_same, one_mul])
  refine ⟨eB, e1, ⟨hB, h1R, hBB, h11, hl eB ?_, hrr eB ?_⟩, hb, Matrix.single i i 1, rank_single i, ?_⟩
  · rw [← mul_assoc, ← mul_assoc, mul_sub eB 1 eB, mul_one, hBB, sub_self, zero_mul, zero_mul]
  · rw [mul_assoc, sub_mul 1 eB eB, one_mul, hBB, sub_self, mul_zero]
  · rw [h1π]
    exact hb'

end GlobalTheory.SpanIdem

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallSubgroupCocycleFormNeZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.FormNonzero

theorem cob_of_vanish {G Λ V : Type} [Group G] [CommRing Λ] [AddCommGroup V] [Module Λ V] (π : Representation Λ G V)
    (L : Subgroup G) (hL : ∀ h ∈ L, ∀ m, π h m = m) (z : G) (d : Λ) (hd : IsUnit (d - 1)) (hz : ∀ m, π z m = d • m)
    (hc : ∀ g, g * z * g⁻¹ * z⁻¹ ∈ L) (f : G → V) (hf : ∀ g h, f (g * h) = f g + π g (f h)) (h0 : ∀ h ∈ L, f h = 0) :
    Cob π f := by
  obtain ⟨u, hu⟩ := hd
  refine ⟨((u⁻¹ : Λˣ) : Λ) • f z, fun g => ?_⟩
  have e1 : f (g * z) = f (z * g) := by
    have : g * z = (g * z * g⁻¹ * z⁻¹) * (z * g) := by group
    rw [this, hf, h0 _ (hc g), hL _ (hc g), zero_add]
  rw [hf, hf, hz] at e1
  rw [map_smul, ← smul_sub]
  have e2 : π g (f z) - f z = (d - 1) • f g := by
    rw [sub_smul, one_smul, sub_eq_sub_iff_add_eq_add, add_comm (π g (f z)), e1, add_comm]
  rw [e2, smul_smul, ← hu, Units.inv_mul, one_smul]

theorem repOn_scalar {G O Λ : Type} [Group G] [CommRing O] [CommRing Λ] [Algebra O Λ] {r : ℕ} (ρ : G →* GL (Fin r) O)
    (κ : G →* Λˣ) (Y : Type) [AddCommGroup Y] [Module Λ Y] (z : G) (d : O) (hκ : κ z = 1)
    (hz : (ρ z : Matrix (Fin r) (Fin r) O) = d • (1 : Matrix (Fin r) (Fin r) O)) (m : Fin r → Y) :
    repOn ρ κ Y z m = algebraMap O Λ d • m := by
  funext a
  simp only [repOn, matAct, MonoidHom.coe_mk, OneHom.coe_mk, hκ, hz, Units.val_one, one_smul, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.map_apply, Matrix.smul_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Matrix.one_apply_ne hb.symm]
  · simp

theorem exists_bform_ne_zero : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] [TopologicalSpace A] [DiscreteTopology A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → AntiHom X.cc κ → κ z = 1 → (∀ g ∈ L, κ g = 1) → ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) Z, Univ bkP i s κ Q Φ Z → ∀ (x₀ : Fin a → A) (j : Fin a) (c : A) (y : Z1 (repOn ρ κ⁻¹ A)), matAct Φ x₀ = 0 → x₀ j ∣ c → ¬ Cob (repOn ρ κ⁻¹ A) (fun g => ((X.l i : A) ^ nu X i * c) • y.1 g) → ∃ h ∈ L, bform (X := X) (fun g => rect (Z g) x₀) y.1 h ≠ 0 := by
  intro D N X bkP i s hl M L z hM hz hL A _ _ _ _ _ _ κ Q ρ hS hK hρ hanti hκz hκL a Φ Z hU x₀ j c y hx₀ hj hy
  by_contra hcon
  push Not at hcon
  apply hy
  obtain ⟨d, hd, hd2, hd1, he⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z hS.1.1 hz
  obtain ⟨x, hx, -⟩ := (hU A).1 x₀ hx₀
  have hcl := GlobalTheory.T.two_mul_cocycle_values_zero_on_small_subgroup D N X bkP i s hl M L z hM hz hL A κ Q ρ hS hK hρ hanti hκz hκL x y
    (fun h hh => by rw [hx]; exact hcon h hh)
  let I : Ideal A := Ideal.span {t | ∃ h ∈ L, ∃ b, t = x.1 h b}
  have hjI : x₀ j ∈ I := by
    letI : TopologicalSpace (A ⧸ I) := ⊥
    haveI : DiscreteTopology (A ⧸ I) := ⟨rfl⟩
    have hker : matAct Φ (fun k => I.mkQ (x₀ k)) = 0 := by
      funext k
      have := congrArg I.mkQ (congrFun hx₀ k)
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [matAct, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, Pi.zero_apply, map_zero] using this
    obtain ⟨x', hx', -⟩ := (hU (A ⧸ I)).1 _ hker
    have h0 := (hU (A ⧸ I)).2.1 _ hker (by
      rw [← hx']
      refine cob_of_vanish _ L (fun h hh m => ?_) z (algebraMap (X.O0 i) A d) (by simpa using hd1.map (algebraMap (X.O0 i) A))
        (repOn_scalar _ _ _ z _ hκz (by rw [Tgl_coe, hd])) hL.1.2.2.2.1 _ x'.2.2 (fun h hh => ?_)
      · rw [(_root_.GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hL A κ ρ hK hρ (A ⧸ I) h hh).1, hκL h hh, Units.val_one, one_smul]
      · funext b
        have e : x'.1 h b = I.mkQ (x.1 h b) := by
          rw [hx, hx']
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [rect, map_sum, map_smul]
        rw [e, Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact Ideal.subset_span ⟨h, hh, b, rfl⟩)
    have := congrFun h0 j
    rwa [Pi.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  have hcI : c ∈ I := by
    obtain ⟨t, rfl⟩ := hj
    exact I.mul_mem_right _ hjI
  have hkill : ∀ t ∈ I, ∀ h' ∈ L, ∀ b, (X.l i : A) ^ nu X i * t * y.1 h' b = 0 := by
    intro t ht h' hh' b
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨h, hh, b', rfl⟩ := ht
      exact hcl h hh h' hh' b' b
    | zero => simp
    | add t t' _ _ h1 h2 => rw [mul_add, add_mul, h1, h2, add_zero]
    | smul u t _ h1 => rw [smul_eq_mul]; linear_combination u * h1
  have hρz : (ρ z : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) = ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) • 1 := by
    have hinv : (Tmat i s z)⁻¹ = ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i) • 1 := by
      apply Matrix.inv_eq_left_inv
      rw [hd, Matrix.smul_mul, one_mul, smul_smul, Units.inv_mul, one_smul]
    rw [hρ z, Tdual, he, hinv, Units.val_one, one_smul, Matrix.transpose_smul, Matrix.transpose_one]
  have hdi := GlobalTheory.TwSys.TameScalar.isUnit_sub_one _ (GlobalTheory.TwSys.TameScalar.isUnit_inv_sq_sub_one d hd2)
  refine cob_of_vanish _ L (fun h hh m => ?_) z (algebraMap (X.O0 i) A ((d⁻¹ : (X.O0 i)ˣ) : X.O0 i))
    (by simpa only [map_sub, map_one] using hdi.map (algebraMap (X.O0 i) A))
    (repOn_scalar _ _ _ z _ (by simp [hκz]) hρz) hL.1.2.2.2.1 _ (fun g h => ?_) (fun h hh => ?_)
  · rw [(_root_.GlobalTheory.NewPrime.SmallActs.small_acts D N X i s hl M L z hM hL A κ⁻¹ ρ hK hρ A h hh).2.1]
    simp [hκL h hh]
  · rw [y.2.2, smul_add, map_smul]
  · funext b
    exact hkill c hcI h hh b

end GlobalTheory.NewPrime.FormNonzero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTaylorShiftFrobeniusTwoVariableCompatibleStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_taylorShift_frobenius_twoVariable_compatible : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K] [NormedAlgebra ℚ_[l] K], ∃ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) ∧ (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) ∧ (∀ f : K⟦X⟧, φ₂ (sh f) = sh (frob K l f)) := by
  first | exact @GlobalTheory.TaylorShift.shift_frob_exists | exact GlobalTheory.TaylorShift.shift_frob_exists | (intros; apply GlobalTheory.TaylorShift.shift_frob_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiedChoiceOfReads
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions
open scoped TensorProduct

namespace GlobalTheory.TwistChoice

variable {D : D7}

open Classical in
theorem goodTw_union {E : IntegralHeckeForms.XD D} {N0 : D.ntw.Tw → ℕ} {i : D.ntw.Tw} {e : ℝ} {S} {A B Q : Finset (PlE D.host)} {k : ℕ}
    {ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} (h : IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E N0 i e S (A ∪ B) Q k ψ) :
    IntegralHeckeForms.GoodTw D.nexp (BlochKatoReduction.bk0 D) E N0 i e S A Q k ψ ∧ Disjoint Q B := by
  obtain ⟨⟨h1, h2, h3⟩, h4⟩ := h
  simp only [Finset.disjoint_union_right] at h2
  exact ⟨⟨⟨h1, by simp only [Finset.disjoint_union_right]; exact ⟨h2.1, h2.2.1, h2.2.2.1⟩, h3⟩, h4⟩, h2.2.2.2⟩

def Reading.Pulls {i : D.ntw.Tw} {k : ℕ} {b : Bool} {w : D.what₂.places.Pl} (ρ : Reading i k b w)
    {Q : Finset (PlE D.host)} (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) : Prop :=
  ∀ g, ρ.emb ((ψ₀ g : (D.what₂.LL)ˣ) : D.what₂.LL) = algebraMap ρ.Oe (FractionRing ρ.Oe)
    (algebraMap (D.ntw.Ok i k) ρ.Oe ((ψ (D.ntw.art i Q g) : (D.ntw.Ok i k)ˣ) : D.ntw.Ok i k))

def HasReading (p : TwPack D) (b : Bool) (w : D.what₂.places.Pl) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ) : Prop :=
  ∃ ρ : Reading p.1 p.2.2.1 b w, ρ.Pulls (BlochKatoReduction.Gen.psiAt b p.2.2.2) ψ₀

theorem psiAt_not {Γ A : Type} [Group Γ] [CommGroup A] (b : Bool) (ψ : Γ →* A) (x : Γ) :
    BlochKatoReduction.Gen.psiAt (!b) ψ x = (BlochKatoReduction.Gen.psiAt b ψ x)⁻¹ := by
  cases b <;> simp [BlochKatoReduction.Gen.psiAt]

theorem pull_inv {L K A B Δ : Type} [Field L] [Field K] [CommRing A] [CommRing B] [Group Δ] [Fintype Δ] (e : L →+* K)
    (m : A →+* B) (m' : B →+* K) (χ : Δ →* Aˣ) (x : Lˣ) (δ : Δ) (h : e (x : L) = m' (m (χ δ : A))) :
    x ^ Fintype.card Δ = 1 ∧ e ((x⁻¹ : Lˣ) : L) = m' (m (((χ δ)⁻¹ : Aˣ) : A)) := by
  constructor
  · apply Units.ext
    apply e.injective
    rw [Units.val_pow_eq_pow_val, map_pow e, h, ← map_pow m', ← map_pow m, ← Units.val_pow_eq_pow_val, ← map_pow χ,
      pow_card_eq_one]
    simp
  · rw [Units.val_inv_eq_inv_val, map_inv₀, h]
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]

theorem Reading.Pulls.conj (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {k : ℕ} {b : Bool} {w : D.what₂.places.Pl} {ρ : Reading i k b w}
    {Q : Finset (PlE D.host)} {ψ ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ} {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ}
    (hρ : ρ.Pulls ψ ψ₀) (h : ∀ x, ψ' x = (ψ x)⁻¹) : (ρ.conj hG).Pulls ψ' ψ₀ := by
  intro g
  have h0 := pull_inv ρ.emb (algebraMap (D.ntw.Ok i k) ρ.Oe) (algebraMap ρ.Oe (FractionRing ρ.Oe)) ψ (ψ₀ g) (D.ntw.art i Q g) (hρ g)
  have h2 := h0.2
  rw [← star_root Fintype.card_pos h0.1, ← h] at h2
  exact h2

theorem HasReading.conj (hG : IsGalois ℚ ↥D.LL0) {p : TwPack D} {b : Bool} {w : D.what₂.places.Pl}
    {ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ} (h : HasReading p b w ψ₀) :
    HasReading p (!b) (D.what₂.places.conj w) ψ₀ :=
  let ⟨ρ, hρ⟩ := h
  ⟨ρ.conj hG, hρ.conj hG (psiAt_not b _)⟩

def RankEq (i : D.ntw.Tw) (b : Bool) (Q : Finset (PlE D.host)) (k : ℕ) (ψ : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ)
    (w : D.what₂.places.Pl) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → Module.finrank D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) =
    Module.finrank (FractionRing (D.ntw.Ok i k)) (D.nexp.MtV i j b k Q (ψ.comp (D.ntw.art i Q)))

theorem exists_formsIso {Oe : Type} [CommRing Oe] [IsDomain Oe] [IsDiscreteValuationRing Oe] {A : Type} [CommRing A] [IsDomain A] [Algebra A Oe]
    (hinj : Function.Injective (algebraMap A Oe)) {V : Type} [AddCommGroup V] [Module (FractionRing A) V] [Module A V]
    [IsScalarTower A (FractionRing A) V] (Λ : Submodule A V) (hfg : Λ.FG)
    (hspan : Submodule.span (FractionRing A) (Λ : Set V) = ⊤) (e : D.what₂.LL →+* FractionRing Oe) (μ : D.what₂.Tup) (j : ℕ) (c : Prop)
    (h : c → Module.finrank D.what₂.LL (D.what₂.MtL μ j) = Module.finrank (FractionRing A) V) :
    ∃ f : D.what₂.MtL μ j →ₛₗ[e] FractionRing Oe ⊗[A] V, c →
      (∀ (b : Module.Basis (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j)) D.what₂.LL (D.what₂.MtL μ j)),
        LinearIndependent (FractionRing Oe) (fun a => f (b a)) ∧
          Submodule.span (FractionRing Oe) (Set.range fun a => f (b a)) = ⊤) ∧
      Submodule.span Oe (f '' {x | D.what₂.jMt μ j x ∈ (D.what₂.MtLat μ j).gen}) =
        Submodule.span Oe ((TensorProduct.mk A (FractionRing Oe) V 1) '' (Λ : Set V)) := by
  by_cases hj : c
  · obtain ⟨h1, h2, h3⟩ := form_gen (D.what₂.jMt μ j) (Module.Free.chooseBasis _ _)
      (D.what₂.jMt_basis _ j _) _ (D.what₂.MtLat μ j).span_top (D.what₂.MtLat_sub _ j)
    obtain ⟨h4, h5⟩ := baseChange_lattice hinj Λ hfg hspan
    obtain ⟨f, hf⟩ := exists_semilinear e _ h2 h3
      (Submodule.span Oe ((TensorProduct.mk A (FractionRing Oe) V 1) '' (Λ : Set V))) ((h hj).trans h4.symm)
    exact ⟨f, fun _ => ⟨fun b => hf.1 _ b, hf.2⟩⟩
  · exact ⟨0, fun h1 => absurd h1 hj⟩

section ChoiceOf

variable (twI : D.what₂.places.Pl → D.ntw.Tw) (b : D.what₂.places.Pl → Bool) (Q : D.what₂.places.Pl → Finset (PlE D.host))
  (k : D.what₂.places.Pl → ℕ) (ψ : ∀ w, D.ntw.RCG (twI w) (Q w) →* (D.ntw.Ok (twI w) (k w))ˣ)
  (hr : ∀ w, ReadsAt (twI w) (b w) w) (ρ : ∀ w, Reading (twI w) (k w) (b w) w)
  (h : ∀ w, TwistedAt D w → RankEq (twI w) (b w) (Q w) (k w) (ψ w) w)

def choiceOf : NChoice D :=
  let H := fun w j => exists_formsIso (ρ w).inj _
    (D.nexp.MtLat_fg (twI w) j (b w) (k w) (Q w) ((ψ w).comp (D.ntw.art (twI w) (Q w))))
    (D.nexp.MtLat_span _ _ _ _ _ _) (ρ w).emb (D.what₂.muTw w) j (TwistedAt D w ∧ 1 ≤ j ∧ j ≤ D.R.m)
    fun c => h w c.1 j c.2.1 c.2.2
  { twI := twI
    twI_l := fun w => (hr w).l_eq
    sd := b
    Q := Q
    k' := k
    psi' := ψ
    Oe := fun w => (ρ w).Oe
    algOOe := fun w => ((algebraMap (D.ntw.Ok (twI w) (k w)) (ρ w).Oe).comp
      (algebraMap (D.ntw.O (twI w)) (D.ntw.Ok (twI w) (k w)))).toAlgebra
    towOe := fun w =>
      letI := ((algebraMap (D.ntw.Ok (twI w) (k w)) (ρ w).Oe).comp
        (algebraMap (D.ntw.O (twI w)) (D.ntw.Ok (twI w) (k w)))).toAlgebra
      IsScalarTower.of_algebraMap_eq fun _ => rfl
    Oe_inj := fun w => (ρ w).inj
    Oe_fin := fun w => (ρ w).fin
    Oe_loc := fun w => (ρ w).loc
    embW := fun w => (ρ w).emb
    embW_w := fun w => (ρ w).emb_w
    eMt := fun w j => (H w j).choose
    eMt_basis := fun w j h0 h1 h2 => ((H w j).choose_spec ⟨h0, h1, h2⟩).1
    eMt_lat := fun w j h0 h1 h2 => ((H w j).choose_spec ⟨h0, h1, h2⟩).2 }

end ChoiceOf

theorem readsAt_of_tie {C : NChoice D} (h : NChTie D C) (w : D.what₂.places.Pl) : ReadsAt (C.twI w) (C.sd w) w := by
  intro x
  obtain ⟨φ, hφ⟩ := exists_intMap (sideEmb (C.twI w) (C.sd w))
  haveI := isLocalHom_phiK (C.twI w) (C.k' w)
  haveI := C.Oe_loc w
  have h1 : C.embW w ((x : ↥D.LL0) : D.what₂.LL) = algebraMap (C.Oe w) (FractionRing (C.Oe w))
      (algebraMap _ (C.Oe w) (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) (φ x))) := by
    have h2 := h.embedding_baseField_condition w x (φ x) 1 one_ne_zero (by rw [map_one, mul_one, hφ]; rfl)
    simp only [map_one, mul_one] at h2
    exact h2
  have h2 : (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 (C.twI w)),
      algebraMap _ (FractionRing (D.ntw.O0 (C.twI w))) y = sideEmb (C.twI w) (C.sd w) (x : ↥D.LL0)) ↔
      ¬ IsUnit (algebraMap _ (C.Oe w) (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) (φ x))) := by
    rw [isUnit_map_iff, isUnit_map_iff]
    exact ⟨fun ⟨y, hy, hy'⟩ => IsFractionRing.injective _ (FractionRing _) (hy'.trans (hφ x).symm) ▸ hy,
      fun hu => ⟨_, hu, hφ x⟩⟩
  rw [h2]
  generalize algebraMap _ (C.Oe w) (BlochKatoReduction.Gen.phiK D.ntw (C.twI w) (C.k' w) (φ x)) = u at h1
  generalize ((x : ↥D.LL0) : D.what₂.LL) = x' at h1
  by_cases hx : x' = 0
  · subst hx
    rw [map_zero, eq_comm, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h1
    simp [h1]
  have h3 : 0 < D.what₂.places.val w x' ↔ ¬ 0 ≤ D.what₂.places.val w x'⁻¹ := by
    rw [val_pos_iff, val_nonneg_iff, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 (by simpa using hx))]
  have hu : algebraMap (C.Oe w) (FractionRing (C.Oe w)) u ≠ 0 := h1 ▸ (map_ne_zero _).2 hx
  rw [h3, C.embW_w, map_inv₀, h1, not_iff_not]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨(v⁻¹ : (C.Oe w)ˣ), eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])⟩
  · rintro ⟨v, hv⟩
    exact IsUnit.of_mul_eq_one v (IsFractionRing.injective _ (FractionRing (C.Oe w))
      (by rw [map_mul, hv, mul_inv_cancel₀ hu, map_one]))

theorem ReadsAt.of_pair (hG : IsGalois ℚ ↥D.LL0) {i : D.ntw.Tw} {b : Bool} {v w : D.what₂.places.Pl} (h : ReadsAt i b v)
    (h' : OverOnePair D v w) : ∃ b', ReadsAt i b' w := by
  rcases h' with h' | h'
  · exact ⟨b, h.of_overOne h'⟩
  · exact ⟨!b, (h.conj hG).of_overOne h'⟩

abbrev Pass (D : D7) : Type := (∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)) × Finset (TwPack D)

variable {D₀ D₁ : D7} {E₀ : IntegralHeckeForms.XD D₀} {E₁ : IntegralHeckeForms.XD D₁} {E : IntegralHeckeForms.XD D}

end GlobalTheory.TwistChoice

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueRatUnitriangularMulEntriesMemFundameStatement
section
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_ratUnitriangular_mul_entries_mem_fundamentalSet : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (u : GA E n), u ∈ GlobalTheory.CellDec.NA E n →
    ∃! γ : GL (Fin n) E, γ ∈ GlobalTheory.SmGL.unipB E (Fin n) ∧ ∀ i j : Fin n, i < j →
      ((ratGL E n γ * u : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j ∈ GroundTheory.Global.fundamentalSet E := by
  first | exact @GlobalTheory.CellDec.existsUnique_ratUnip_mul_mem_fundamentalSet | exact GlobalTheory.CellDec.existsUnique_ratUnip_mul_mem_fundamentalSet | (intros; apply GlobalTheory.CellDec.existsUnique_ratUnip_mul_mem_fundamentalSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysOfSplitStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrys_of_split_alt : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V) {n : ℕ} (e : Module.Basis (Fin n) Qp V) [FiniteDimensional Qp LL] (W : Matrix (Fin n) (Fin n) B), IsUnit W.det → (∀ g, (Matrix.of fun i j => algebraMap Qp B (e.repr (ρ g (e j)) i)) * W.map (PD.actB g) = W) → Formalism.WeaklyAdmissibleFiltrations.IsCrys PD ρ := by
  first | exact @GlobalTheory.SplitCrys.isCrys_of_split | exact GlobalTheory.SplitCrys.isCrys_of_split | (intros; apply GlobalTheory.SplitCrys.isCrys_of_split <;> assumption)
end

