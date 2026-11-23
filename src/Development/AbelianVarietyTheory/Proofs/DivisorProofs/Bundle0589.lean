module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0565
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimFiniteGLLeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKernelIdealSuccLeMulLevels
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory

namespace PDiv

theorem finrank_quot_kerIdeal_le_mul {k A B C : Type} [Field k] [CommRing A] [CommRing B]
    [CommRing C] [HopfAlgebra k A] [HopfAlgebra k B] [HopfAlgebra k C] [Module.Finite k A]
    [Module.Finite k B] [Module.Finite k C] (m : B →ₐc[k] A) (r : A →ₐc[k] C)
    (hr : Function.Surjective r) (hk : RingHom.ker (r : A →ₐ[k] C) ≤ kerIdeal m)
    (u : A →ₐc[k] A) (v : B →ₐc[k] B) (w : C →ₐc[k] C) (hm : ∀ b, u (m b) = m (v b))
    (hw : ∀ a, r (u a) = w (r a)) :
    Module.finrank k (A ⧸ kerIdeal u) ≤
      Module.finrank k (C ⧸ kerIdeal w) * Module.finrank k (B ⧸ kerIdeal v) := by
  haveI := _root_.GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom k A A u
  haveI := _root_.GlobalTheory.PDiv.isHopfIdeal_kerIdeal_of_bialgHom k B B v
  let πA : A →ₐc[k] A ⧸ kerIdeal u := Bialgebra.Quotient.mkBialgHom (kerIdeal u)
  let πB : B →ₐc[k] B ⧸ kerIdeal v := Bialgebra.Quotient.mkBialgHom (kerIdeal v)
  have hπA : Function.Surjective πA := Ideal.Quotient.mk_surjective
  have hπB : Function.Surjective πB := Ideal.Quotient.mk_surjective
  have hA : ∀ a, πA (u a) = algebraMap k _ (counit a) :=
    (kerIdeal_le_ker_iff u (πA : A →ₐ[k] A ⧸ kerIdeal u)).1
      fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  have h1 : kerIdeal v ≤ RingHom.ker (πA.comp m : B →ₐ[k] A ⧸ kerIdeal u) :=
    (kerIdeal_le_ker_iff v _).2 fun b => by
      change πA (m (v b)) = _
      rw [← hm, hA, CoalgHomClass.counit_comp_apply]
  let m' : (B ⧸ kerIdeal v) →ₐc[k] A ⧸ kerIdeal u :=
    liftSurj πB hπB (πA.comp m) fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)
  have hm' : m'.comp πB = πA.comp m := BialgHom.ext fun b =>
    liftSurj_apply πB hπB (πA.comp m) (fun b hb => h1 (Ideal.Quotient.eq_zero_iff_mem.1 hb)) b
  let q : A →ₐ[k] (A ⧸ kerIdeal u) ⧸ kerIdeal m' :=
    (Ideal.Quotient.mkₐ k (kerIdeal m')).comp (πA : A →ₐ[k] A ⧸ kerIdeal u)
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective.comp hπA
  have h2 : RingHom.ker (r : A →ₐ[k] C) ≤ RingHom.ker q := fun a ha => by
    have h3 : πA a ∈ kerIdeal m' := by
      rw [← kerIdeal_comp_of_surjective m' hπB, hm', kerIdeal_comp]
      exact Ideal.mem_map_of_mem _ (hk ha)
    exact Ideal.Quotient.eq_zero_iff_mem.2 h3
  let q' : C →ₐ[k] (A ⧸ kerIdeal u) ⧸ kerIdeal m' :=
    AlgHom.liftOfSurjective (r : A →ₐ[k] C) hr q h2
  have hq' : ∀ a, q' (r a) = q a := AlgHom.liftOfSurjective_apply (r : A →ₐ[k] C) hr q h2
  have h4 : kerIdeal w ≤ RingHom.ker q' := (kerIdeal_le_ker_iff w q').2 fun c => by
    obtain ⟨a, rfl⟩ := hr c
    rw [← hw, hq', CoalgHomClass.counit_comp_apply]
    change Ideal.Quotient.mkₐ k (kerIdeal m') (πA (u a)) = _
    rw [hA, AlgHom.commutes]
  let q'' : (C ⧸ kerIdeal w) →ₐ[k] (A ⧸ kerIdeal u) ⧸ kerIdeal m' :=
    Ideal.Quotient.liftₐ (kerIdeal w) q' h4
  have hq'' : Function.Surjective q''.toLinearMap := fun x => by
    obtain ⟨a, rfl⟩ := hq x
    exact ⟨Ideal.Quotient.mk _ (r a), hq' a⟩
  rw [finrank_eq_ker_mul_range k _ _ m']
  exact Nat.mul_le_mul (LinearMap.finrank_le_finrank_of_surjective hq'')
    (LinearMap.finrank_range_le _)

end PDiv

namespace PDivGroup

theorem resOne_app {p : ℕ} {R : Type} [CommRing R] {G H : PDivGroup p R} (f : G ⟶ H) (n : ℕ)
    (a : H.A (n + 1)) : G.resOne n (f.app (n + 1) a) = f.app 1 (H.resOne n a) := by
  induction n with
  | zero => simp only [resOne_zero]
  | succ n ih => rw [resOne_succ, resOne_succ, res_app, ih]

theorem finrank_quot_kerIdeal_succ_le (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    (G : PDivGroup p k) (u : G ⟶ G) (n : ℕ) :
    Module.finrank k (G.A (n + 1) ⧸ kerIdeal (u.app (n + 1))) ≤
      Module.finrank k (G.A 1 ⧸ kerIdeal (u.app 1)) *
        Module.finrank k (G.A n ⧸ kerIdeal (u.app n)) :=
  by
    have hker (n : ℕ) : RingHom.ker (G.resOne n : G.A (n + 1) →ₐ[k] G.A 1) =
        torsionIdeal (R := k) (A := G.A (n + 1)) p := by
      induction n with
      | zero =>
        have hid : (G.resOne 0 : G.A 1 →ₐ[k] G.A 1) = AlgHom.id k _ := by
          ext a; exact G.resOne_zero a
        rw [hid]
        refine le_antisymm ?_ ?_
        · intro a ha
          have : a = 0 := ha
          simp [this]
        · refine (torsionIdeal_le_ker_iff p (AlgHom.id k (G.A (0 + 1)))).2 ?_
          simpa using G.pts_pow_self 1 (WithConv.toConv (AlgHom.id k (G.A 1)))
      | succ n ih =>
        have hcomp : (G.resOne (n + 1) : G.A (n + 2) →ₐ[k] G.A 1) =
            (G.resOne n : G.A (n + 1) →ₐ[k] G.A 1).comp
              (G.res (n + 1) : G.A (n + 2) →ₐ[k] G.A (n + 1)) := by
          ext a; exact G.resOne_succ n a
        have hsurj : Function.Surjective (G.res (n + 1) :
            G.A (n + 2) →ₐ[k] G.A (n + 1)) := G.res_surjective (n + 1)
        have hk : RingHom.ker ((G.resOne n : G.A (n + 1) →ₐ[k] G.A 1).comp
            (G.res (n + 1) : G.A (n + 2) →ₐ[k] G.A (n + 1))) =
            Ideal.comap (G.res (n + 1) : G.A (n + 2) →ₐ[k] G.A (n + 1))
              (RingHom.ker (G.resOne n : G.A (n + 1) →ₐ[k] G.A 1)) := by
          ext a; exact Iff.rfl
        rw [hcomp, hk, ih, ← map_torsionIdeal (G.res_surjective (n + 1)) p]
        erw [Ideal.comap_map_of_surjective _ hsurj]
        refine sup_eq_left.mpr ?_
        have h0 : Ideal.comap (G.res (n + 1) : G.A (n + 2) →ₐ[k] G.A (n + 1)) ⊥ =
            torsionIdeal (R := k) (A := G.A (n + 2)) (p ^ (n + 1)) := by
          rw [← G.ker_res (n + 1)]
          ext a; exact Iff.rfl
        rw [h0]
        exact torsionIdeal_le_of_dvd (dvd_pow_self p (Nat.succ_ne_zero n))
    have hmul : kerIdeal (G.mulP n) =
        torsionIdeal (R := k) (A := G.A (n + 1)) p := by
      unfold torsionIdeal
      rw [← G.mulP_comp_res n, kerIdeal_comp_of_surjective _ (G.res_surjective n)]
    exact finrank_quot_kerIdeal_le_mul (G.mulP n) (G.resOne n) (G.resOne_surjective n)
      ((hker n).trans hmul.symm).le _ _ _ (app_mulP u n) (resOne_app u n)

end PDivGroup

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOneFraction
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

namespace LawUp

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ} {τ : Type}

theorem mvPowerSeriesMap_evalTwoGroups (φ : R →+* S) (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    map φ (at2 c u v) = at2 (map φ c) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  unfold at2
  rw [map_subst (CobCob.elim_has hu hv)]
  congr 1
  funext j
  cases j <;> rfl

theorem map_op (φ : R →+* S) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    {u v : Fin d → MvPowerSeries τ R} (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    (fun i => map φ (op μ u v i)) =
      op (fun i => map φ (μ i)) (fun i => map φ (u i)) (fun i => map φ (v i)) := by
  funext i
  exact mvPowerSeriesMap_evalTwoGroups φ (μ i) hu hv

theorem isLaw_map (φ : R →+* S) {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (h : IsLaw μ) :
    IsLaw (fun i => map φ (μ i)) := by
  have h12 := CobCob.op_const h.const (CobCob.constantCoeff_threeGroupsFirstVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsSecondVariables
  have h23 := CobCob.op_const h.const (CobCob.constantCoeff_threeGroupsSecondVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsThirdVariables
  refine ⟨fun i => ?_, ?_, fun i => ?_, ?_⟩
  · rw [constantCoeff_map, h.const i, map_zero]
  · have e := map_op φ μ (τ := Fin d) (u := fun i => (X i : MvPowerSeries (Fin d) R))
      (v := fun _ => 0) (fun _ => constantCoeff_X _) (fun _ => map_zero _)
    rw [h.unit] at e
    simp only [map_X, map_zero] at e
    exact e.symm
  · have e := mvPowerSeriesMap_evalTwoGroups φ (μ i) (τ := Fin d ⊕ Fin d)
      (u := fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))
      (v := fun i => X (Sum.inl i)) (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)
    simp only [map_X] at e
    unfold swap
    rw [← e]
    exact congrArg (map φ) (h.comm i)
  · have e1 := map_op φ μ h12 CobCob.constantCoeff_threeGroupsThirdVariables
    have e2 := map_op φ μ CobCob.constantCoeff_threeGroupsFirstVariables h23
    have e3 := map_op φ μ (CobCob.constantCoeff_threeGroupsFirstVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsSecondVariables
    have e4 := map_op φ μ (CobCob.constantCoeff_threeGroupsSecondVariables (R := R) (d := d)) CobCob.constantCoeff_threeGroupsThirdVariables
    have hx1 : (fun i => map φ (x1 (R := R) (d := d) i)) = x1 := by funext i; exact map_X _ _
    have hx2 : (fun i => map φ (x2 (R := R) (d := d) i)) = x2 := by funext i; exact map_X _ _
    have hx3 : (fun i => map φ (x3 (R := R) (d := d) i)) = x3 := by funext i; exact map_X _ _
    rw [hx1, hx2] at e3
    rw [hx2, hx3] at e4
    rw [e3, hx3] at e1
    rw [e4, hx1] at e2
    rw [← e1, ← e2, h.assoc]

end LawUp

theorem formalGroupLawCoboundaryTwo_coboundaryOne_fractions : ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLaw μ → ∀ g : MvPowerSeries (Fin d) Q, cob2 (up Q μ) (cob1 (up Q μ) g) = 0 := by
  intro B Q _ _ _ d μ h g
  have hL : IsLaw (up Q μ) := LawUp.isLaw_map (algebraMap B Q) h
  exact ((formalGroupLawCoboundaryTwo_coboundaryOne_alt Q d (up Q μ) hL.const g).2.2.2.2.2 hL).1

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawPointsCommMonoidSubstHom
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.Katz.LawMonoid

variable {R : Type} [CommRing R] {d : ℕ}

theorem constantCoeff_bivariateSeriesSubstPair {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : constantCoeff (at2 c u v) = constantCoeff c :=
  (GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d τ τ u v hu hv).2.2.2.1 c

theorem powerSeriesEvalTwoGroups_swapVariableGroups {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) : at2 (swap c) u v = at2 c v u :=
  (GlobalTheory.Katz.SubstCalc.powerSeriesEvalTwoGroups_rules_alt R d τ τ u v hu hv).2.2.2.2.1 c

theorem cc_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {τ : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (op μ u v i) = 0 := by
  show constantCoeff (at2 (μ i) u v) = 0
  rw [constantCoeff_bivariateSeriesSubstPair hu hv, hμ]

theorem subst_op {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    {τ τ' : Type} [Finite τ] {u v : Fin d → MvPowerSeries τ R}
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0)
    (a : τ → MvPowerSeries τ' R) (ha : ∀ t, constantCoeff (a t) = 0) (i : Fin d) :
    subst a (op μ u v i) = op μ (fun j => subst a (u j)) (fun j => subst a (v j)) i :=
  GlobalTheory.Katz.SubstCalc.subst_powerSeriesEvalTwoGroups hu hv ha (μ i)

theorem constantCoeff_mvPowerSeries_X_eq_zero {τ : Type} (s : τ) : constantCoeff (X s : MvPowerSeries τ R) = 0 := constantCoeff_X s

theorem mon : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), IsLaw μ → ∀ (τ : Type) [Finite τ] (u v w : Fin d → MvPowerSeries τ R), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) → (∀ i, constantCoeff (w i) = 0) → (∀ i, constantCoeff (op μ u v i) = 0) ∧ op μ (op μ u v) w = op μ u (op μ v w) ∧ op μ u v = op μ v u ∧ op μ u (fun _ => 0) = u ∧ ∀ (τ' : Type) (a : τ → MvPowerSeries τ' R), (∀ t, constantCoeff (a t) = 0) → ∀ i, subst a (op μ u v i) = op μ (fun j => subst a (u j)) (fun j => subst a (v j)) i := by
  intro R _ d μ hμ τ _ u v w hu hv hw
  refine ⟨cc_op hμ.const hu hv, ?_, ?_, ?_, fun τ' a ha i => subst_op hu hv a ha i⟩
  ·
    let a : Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries τ R := Sum.elim u (Sum.elim v w)
    have ha : ∀ t, constantCoeff (a t) = 0 := by
      intro t; rcases t with t | t | t
      · exact hu t
      · exact hv t
      · exact hw t
    have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
    have h1 : (fun j => subst a ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = u := by
      funext j; simp only [x1]; rw [subst_X hs]; rfl
    have h2 : (fun j => subst a ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = v := by
      funext j; simp only [x2]; rw [subst_X hs]; rfl
    have h3 : (fun j => subst a ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j)) = w := by
      funext j; simp only [x3]; rw [subst_X hs]; rfl
    have hx1 : ∀ j, constantCoeff ((x1 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    have hx2 : ∀ j, constantCoeff ((x2 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    have hx3 : ∀ j, constantCoeff ((x3 : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R) j) = 0 :=
      fun j => constantCoeff_mvPowerSeries_X_eq_zero _
    funext i
    have e := congrArg (fun F => subst a (F i)) hμ.assoc
    try simp only at e
    rw [subst_op (cc_op hμ.const hx1 hx2) hx3 a ha, subst_op hx1 (cc_op hμ.const hx2 hx3) a ha] at e
    have e1 : (fun j => subst a (op μ x1 x2 j)) = op μ u v := by
      funext j; rw [subst_op hx1 hx2 a ha, h1, h2]
    have e2 : (fun j => subst a (op μ x2 x3 j)) = op μ v w := by
      funext j; rw [subst_op hx2 hx3 a ha, h2, h3]
    rw [e1, e2, h1, h3] at e
    exact e
  · funext i
    show at2 (μ i) u v = at2 (μ i) v u
    rw [← powerSeriesEvalTwoGroups_swapVariableGroups hu hv, hμ.comm i]
  ·
    have hs : HasSubst u := hasSubst_of_constantCoeff_zero hu
    have hX : ∀ j, constantCoeff ((X j : MvPowerSeries (Fin d) R)) = 0 := fun j => constantCoeff_X j
    have h0 : ∀ j : Fin d, constantCoeff ((fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) j) = 0 := fun _ => map_zero _
    funext i
    have e := congrArg (fun F => subst u (F i)) hμ.unit
    try simp only at e
    rw [subst_op hX h0 u hu, subst_X hs] at e
    have e1 : (fun j => subst u ((X j : MvPowerSeries (Fin d) R))) = u := by
      funext j; rw [subst_X hs]
    have e0 : (fun j : Fin d => subst u ((fun _ : Fin d => (0 : MvPowerSeries (Fin d) R)) j)) = fun _ => 0 := by
      funext j; show subst u (0 : MvPowerSeries (Fin d) R) = 0
      rw [← coe_substAlgHom hs]; exact map_zero _
    rw [e1, e0] at e
    exact e

end GlobalTheory.Katz.LawMonoid
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedHomWithFixedPullbackScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomFixUnr

theorem base_eq {X Y Z Y' Z' : Scheme.{0}} (b : Y ⟶ X) (c : Z ⟶ Y) (b' : Y' ⟶ X) (c' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (e : c' ≫ b' = h ≫ c ≫ b) (y : Z') : b' (c' y) = b (c (h y)) := by
  have := congrArg (fun k => k.base y) e
  simpa only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply] using this

def chartPullPullPull {X Y Z Y' Z' : Scheme.{0}} (M : LB X) (b : Y ⟶ X) (c : Z ⟶ Y) (b' : Y' ⟶ X) (c' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (e : c' ≫ b' = h ≫ c ≫ b) : ChartPull ((M.pull b').pull c') ((M.pull b).pull c) h where
  idx J := J
  le J y hy := by
    have h1 := mem_pull.1 (mem_pull.1 hy)
    show h y ∈ ((M.pull b).pull c).U J
    refine mem_pull.2 (mem_pull.2 ?_)
    rw [← base_eq b c b' c' h e y]; exact h1
  g y J J' hj hj' := by
    have hj2 : (𝟙 Z' ≫ c') y ∈ (M.pull b').U (J PUnit.unit) := mem_pull.1 hj
    have hj2' : (𝟙 Z' ≫ c') y ∈ (M.pull b').U (J' PUnit.unit) := mem_pull.1 hj'
    have hk : ∀ K : PUnit → PUnit → M.ι, y ∈ ((M.pull b').pull c').U K → h y ∈ ((M.pull b).pull c).U K := fun K hK =>
      mem_pull.2 (mem_pull.2 (by rw [← base_eq b c b' c' h e y]; exact mem_pull.1 (mem_pull.1 hK)))
    have hk2 : (h ≫ c) y ∈ (M.pull b).U (J PUnit.unit) := by
      have := mem_pull.1 (hk J hj); simpa using this
    have hk2' : (h ≫ c) y ∈ (M.pull b).U (J' PUnit.unit) := by
      have := mem_pull.1 (hk J' hj'); simpa using this
    rw [gm_pull_g (M.pull b') c' (𝟙 Z') y J J' hj hj', gm_pull_g M b' (𝟙 Z' ≫ c') y _ _ hj2 hj2',
      gm_pull_g (M.pull b) c h y J J' (hk J hj) (hk J' hj'), gm_pull_g M b (h ≫ c) y _ _ hk2 hk2']
    have e' : (𝟙 Z' ≫ c') ≫ b' = (h ≫ c) ≫ b := by rw [Category.id_comp, e, Category.assoc]
    rw [e']

theorem lbIso_pull_square {XA XB YA YB ZA ZB : Scheme.{0}} (L : LB XA) (M : LB XB) (φA : YA ⟶ XA) (φB : YB ⟶ XB)
    (Φ : YA ⟶ YB) (ψA : ZA ⟶ XA) (ψB : ZB ⟶ XB) (v : ZA ⟶ ZB) (χA : ZA ⟶ YA) (χB : ZB ⟶ YB)
    (hA : χA ≫ φA = ψA) (hB : χB ≫ φB = ψB) (hv : v ≫ χB = χA ≫ Φ)
    (H : LBIso (L.pull φA) ((M.pull φB).pull Φ)) : LBIso (L.pull ψA) ((M.pull ψB).pull v) :=
  LBIso.chartPull (chartPullSame L (fun _ => ψA) (fun _ => φA) (fun _ => 1) χA fun _ => hA.symm)
    (chartPullPullPull M φB Φ ψB v χA (by rw [← hB, ← Category.assoc, hv, Category.assoc])) H

end GlobalTheory.EndLoc.HomFixUnr

namespace GlobalTheory.EndLoc


open GlobalTheory.EndLoc.HomFixUnr in
theorem formallyUnramified_homFixRep : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B]
    [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (R : HomFixRep A B L M), IsAbelianScheme A → IsAbelianScheme B →
    FormallyUnramified R.π := by
  intro S A B _ _ _ _ L M Rp hA _
  refine FormallyUnramified.of_hom_ext _ fun R R₀ q hq hsq g₁ g₂ hi hg ↦ ?_
  let f : Spec R ⟶ S := g₁ ≫ Rp.π
  let AT : Over (Spec R) := (Over.pullback f).obj A
  let BT : Over (Spec R) := (Over.pullback f).obj B
  let ψA : AT.left ⟶ A.left := pullback.fst A.hom f
  let ψB : BT.left ⟶ B.left := pullback.fst B.hom f
  have hAT : IsGrpPullback AT A f ψA := isGrpPullback_pullback A f
  have hBT : IsGrpPullback BT B f ψB := isGrpPullback_pullback B f
  have hAbT : IsAbelianScheme AT := GlobalTheory.isAbelianScheme_pullback_obj f A hA
  have tr : ∀ (g : Spec R ⟶ Rp.H), g ≫ Rp.π = f → ∀ (G : Over S) [GrpObj G] (GH : Over Rp.H) [GrpObj GH]
      (φ : GH.left ⟶ G.left), IsGrpPullback GH G Rp.π φ →
      ∃ e : (Over.pullback f).obj G ≅ (Over.pullback g).obj GH, IsMonHom e.hom ∧
        IsGrpPullback ((Over.pullback f).obj G) GH g (e.hom.left ≫ pullback.fst GH.hom g) ∧
        (e.hom.left ≫ pullback.fst GH.hom g) ≫ φ = pullback.fst G.hom f := by
    intro g hgf G _ GH _ φ hG
    have h' : IsGrpPullback ((Over.pullback g).obj GH) G f (pullback.fst GH.hom g ≫ φ) :=
      ((isGrpPullback_pullback GH g).comp hG).congr hgf rfl
    obtain ⟨e, he, heφ⟩ := grpPullback_iso (isGrpPullback_pullback G f) h'
    haveI := he
    exact ⟨e, he, ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback GH g)).congr (Category.id_comp _) rfl,
      by rw [Category.assoc, heφ]⟩
  have build : ∀ g : Spec R ⟶ Rp.H, g ≫ Rp.π = f → ∃ (v : AT ⟶ BT) (χA : AT.left ⟶ Rp.AH.left)
      (χB : BT.left ⟶ Rp.BH.left), IsMonHom v ∧ IsGrpPullback AT Rp.AH g χA ∧ IsGrpPullback BT Rp.BH g χB ∧
        χA ≫ Rp.φA = ψA ∧ χB ≫ Rp.φB = ψB ∧ v.left ≫ χB = χA ≫ Rp.Φ.left := by
    intro g hgf
    obtain ⟨eA, heA, hpA, hφA⟩ := tr g hgf A Rp.AH Rp.φA Rp.pbA
    obtain ⟨eB, heB, hpB, hφB⟩ := tr g hgf B Rp.BH Rp.φB Rp.pbB
    haveI := heA
    haveI := heB
    haveI := Rp.hom
    have hie : eB.inv.left ≫ eB.hom.left = 𝟙 _ := by rw [← Over.comp_left, eB.inv_hom_id, Over.id_left]
    refine ⟨eA.hom ≫ (Over.pullback g).map Rp.Φ ≫ eB.inv, _, _, inferInstance, hpA, hpB, hφA, hφB, ?_⟩
    have hm : ((Over.pullback g).map Rp.Φ).left ≫ pullback.fst Rp.BH.hom g =
        pullback.fst Rp.AH.hom g ≫ Rp.Φ.left := pullback.lift_fst _ _ _
    simp only [Over.comp_left, Category.assoc]
    rw [reassoc_of% hie, hm]
  obtain ⟨v₁, χA₁, χB₁, hv₁, hpA₁, hpB₁, hχA₁, hχB₁, hχ₁⟩ := build g₁ rfl
  obtain ⟨v₂, χA₂, χB₂, hv₂, hpA₂, hpB₂, hχA₂, hχB₂, hχ₂⟩ := build g₂ hg.symm
  let I : Ideal R := RingHom.ker q.hom
  have hI : IsNilpotent I := ⟨2, hsq⟩
  let j : Sp (R ⧸ I) ⟶ Sp R := spMap (Ideal.Quotient.mk I)
  have hj : j ≫ g₁ = j ≫ g₂ := by
    let ε : (R ⧸ I) ≃+* R₀ := RingHom.quotientKerEquivOfSurjective hq
    have hε : Spec.map q = Spec.map (CommRingCat.ofHom ε.toRingHom) ≫ j := by
      rw [← Spec.map_comp]
      congr 1
    haveI : IsIso (CommRingCat.ofHom ε.toRingHom) := ε.toCommRingCatIso.isIso_hom
    rw [hε, Category.assoc, Category.assoc] at hi
    exact (cancel_epi _).1 hi
  have hχA : pullback.fst AT.hom j ≫ χA₁ = pullback.fst AT.hom j ≫ χA₂ := by
    apply Rp.pbA.1.hom_ext
    · rw [Category.assoc, Category.assoc, hχA₁, hχA₂]
    · rw [Category.assoc, Category.assoc, hpA₁.1.w, hpA₂.1.w, pullback.condition_assoc, pullback.condition_assoc, hj]
  have hv : v₁ = v₂ := by
    refine GlobalTheory.NilRigidity.eq_of_pullback_quotient_eq I hI AT BT hAbT v₁ v₂ ?_
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [show ((Over.pullback j).map v₁).left ≫ pullback.fst BT.hom j =
          pullback.fst AT.hom j ≫ v₁.left from pullback.lift_fst _ _ _,
        show ((Over.pullback j).map v₂).left ≫ pullback.fst BT.hom j =
          pullback.fst AT.hom j ≫ v₂.left from pullback.lift_fst _ _ _]
      apply hBT.1.hom_ext
      · calc (pullback.fst AT.hom j ≫ v₁.left) ≫ ψB
            = pullback.fst AT.hom j ≫ v₁.left ≫ χB₁ ≫ Rp.φB := by rw [hχB₁, Category.assoc]
          _ = pullback.fst AT.hom j ≫ χA₁ ≫ Rp.Φ.left ≫ Rp.φB := by rw [reassoc_of% hχ₁]
          _ = pullback.fst AT.hom j ≫ χA₂ ≫ Rp.Φ.left ≫ Rp.φB := by rw [reassoc_of% hχA]
          _ = pullback.fst AT.hom j ≫ v₂.left ≫ χB₂ ≫ Rp.φB := by rw [reassoc_of% hχ₂]
          _ = (pullback.fst AT.hom j ≫ v₂.left) ≫ ψB := by rw [hχB₂, Category.assoc]
      · rw [Category.assoc, Category.assoc, Over.w v₁, Over.w v₂]
    · rw [show ((Over.pullback j).map v₁).left ≫ pullback.snd BT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _,
        show ((Over.pullback j).map v₂).left ≫ pullback.snd BT.hom j =
          pullback.snd AT.hom j from pullback.lift_snd _ _ _]
  have hL : LBIso (L.pull ψA) ((M.pull ψB).pull v₁.left) :=
    lbIso_pull_square L M Rp.φA Rp.φB Rp.Φ.left ψA ψB v₁.left χA₁ χB₁ hχA₁ hχB₁ hχ₁ Rp.iso
  obtain ⟨g, -, hg'⟩ := Rp.rep (Spec R) f AT BT ψA ψB v₁ hAT hBT hv₁ hL
  have e1 := hg' g₁ ⟨rfl, χA₁, χB₁, hpA₁, hpB₁, hχA₁, hχB₁, hχ₁⟩
  have e2 := hg' g₂ ⟨hg.symm, χA₂, χB₂, hpA₂, hpB₂, hχA₂, hχB₂, by rw [hv]; exact hχ₂⟩
  rw [e1, e2]

end GlobalTheory.EndLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDatumBiconnOf
section
set_option autoImplicit false
noncomputable section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem hasDatum_biconn_of (hfr : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), Nonempty (BFrame ε))
    (hmat : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, IsConn G → IsConn G.dual → ∀ F : BFrame ε, ∃ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin G.height) F.B) (Gm : Matrix (Fin G.height) (Fin d ⊕ Fin k) F.B) (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate) (w : Module.Basis (Fin d) O G.omega) (lb : Module.Basis (Fin k) O G.dual.Lie), d + k = G.height ∧ IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin G.height) (Fin G.height) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) ∧ (∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0) ∧ (∀ j m, F.θ (Y (Sum.inr j) m) = lb j (hodgeTate G (tb m))) ∧ ∀ m, dlog G (χ m) = ∑ i, F.θ (Gm m (Sum.inl i)) • w i)
    (hlift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B), IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin h) (Fin h) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → ∃ (Fa : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)) (Ga : Matrix (Fin h) (Fin d ⊕ Fin k) (Ainf p O)) (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) ∧ Fa = Ψ * Fa.map (phiInv p O) ∧ Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) ∧ (∀ i m, WittVector.fontaineTheta O p (Fa i m) = F.θ (Y i m)) ∧ ∀ m i, WittVector.fontaineTheta O p (Ga m i) = F.θ (Gm m i))
    (hfin : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O) (d k : ℕ), d + k = G.height → ∀ (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate) (w : Module.Basis (Fin d) O G.omega) (lb : Module.Basis (Fin k) O G.dual.Lie) (Fa : Matrix (Fin d ⊕ Fin k) (Fin G.height) (Ainf p O)) (Ga : Matrix (Fin G.height) (Fin d ⊕ Fin k) (Ainf p O)) (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin G.height) (Fin G.height) (Ainf p O)) → Fa = Ψ * Fa.map (phiInv p O) → Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) → (∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0) → (∀ i m, WittVector.fontaineTheta O p (Fa (Sum.inl i) m) = 0) → (∀ j m, WittVector.fontaineTheta O p (Fa (Sum.inr j) m) = lb j (hodgeTate G (tb m))) → (∀ m j, WittVector.fontaineTheta O p (Ga m (Sum.inr j)) = 0) → (∀ m, dlog G (χ m) = ∑ i, WittVector.fontaineTheta O p (Ga m (Sum.inl i)) • w i) → HasDatum hε G) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, IsConn G → IsConn G.dual → HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG hD
  obtain ⟨F⟩ := hfr p C v O hv ε hε
  obtain ⟨d, k, U, Y, Gm, tb, χ, w, lb, hdk, hU, hY, hGm, hGY, hY0, hG0, hn1, hn2, hpair, hYl, hdl⟩ :=
    hmat p C v O hv ε hε G hG hD F
  obtain ⟨Fa, Ga, Ψ, Ψ', h1, h2, h3, h4, h5⟩ :=
    hlift p C v O hv ε hε F d k G.height U Y Gm ⟨hU, hY, hGm, hGY, hY0, hG0, hn1, hn2⟩
  refine hfin p C v O hv ε hε G d k hdk tb χ w lb Fa Ga Ψ Ψ' h1 h2 h3 hpair
    (fun i m => (h4 _ _).trans (hY0 i m)) (fun j m => (h4 _ _).trans (hYl j m))
    (fun m j => (h5 _ _).trans (hG0 m j)) (fun m => ?_)
  rw [hdl m]
  exact Finset.sum_congr rfl fun i _ => by rw [h5]

end GlobalTheory.PDivLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimFiniteGLLeOneStatement
section
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittakerSpaceDimFiniteGL_le_one : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (τ : Representation ℂ (GL (Fin r) F) V), τ.IsIrreducible → whDim ψ τ ≤ 1 := by
  first | exact @GlobalTheory.FinGL.GGFree.whDim_le_one | exact GlobalTheory.FinGL.GGFree.whDim_le_one | (intros; apply GlobalTheory.FinGL.GGFree.whDim_le_one <;> assumption)
end

