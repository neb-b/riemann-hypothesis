module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsValueEq
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1996
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2023
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0912
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1403
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.WeilSqKer

open GlobalTheory.CechPic GlobalTheory.DiagPairing

theorem weilIs_eq_one : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (m : ℕ), (m : k) ≠ 0 → ∀ (a b : Over.mk x₀ ⟶ A), a ^ m = 1 → b ^ m = 1 → (∃ t : (P.pull (lift (snd A (Over.mk x₀) ≫ a ^ 2) (fst A (Over.mk x₀))).left).Gen, t.IsGen) → ∀ c : Γ((Over.mk x₀).left, ⊤)ˣ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) (m : ℤ) a b c → c = 1 := by
  intro S A _ _ hA P hP h₁ h₂ hsym hamp k _ _ x₀ m hm a b ha hb ha2 c hc
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  obtain ⟨t, ht⟩ := GlobalTheory.HkFam.cube_of_exists_relAmple hA hD hamp hD
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP h₁ h₂
        T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP h₁ h₂
        T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hS : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) :=
    (cls_eq_iff hP (pull_isLB hP _)).2 hsym
  have hsw : ∀ (T : Over S) (x y : T ⟶ A), pc hP x y = pc hP y x := fun T x y => by
    have h := congrArg (pull (lift x y).left) hS
    rw [← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst] at h
    exact h
  let T : Over S := Over.mk x₀
  have e : ∀ g : T ⊗ A ⟶ A, pull g.left (cls _ hD) = pc hP g g := fun g => by
    rw [cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
    rfl

  have hpt : ∀ {N : LB T.left} (hN : N.IsLB), cls N hN = 0 := fun {N} hN => by
    haveI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    obtain ⟨p⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum k))
    obtain ⟨i, hi⟩ := exists_chart hN p
    exact (cls_eq_zero_iff hN).2
      (DescendedPrincipal.exists_gen_of_chart hN i fun y => Subsingleton.elim p y ▸ hi)
  have haa : pc hP (fst T A ≫ a) (fst T A ≫ a) = 0 := by
    unfold pc
    rw [← comp_lift, Over.comp_left, pull_comp, ← cls_pull hP _ (pull_isLB hP _),
      hpt (pull_isLB hP _), map_zero]
  have ha2' : pc hP (fst T A ≫ a) (snd T A) + pc hP (fst T A ≫ a) (snd T A) = 0 := by
    rw [← hB]
    obtain ⟨u, hu⟩ := ha2
    have z := (cls_eq_zero_iff (pull_isLB hP _)).2 ⟨u, hu⟩
    rw [cls_pull hP] at z
    have z' := congrArg (pull (β_ T A).hom.left) z
    rw [← pull_comp, ← Over.comp_left, comp_lift, braiding_hom_snd_assoc, braiding_hom_fst, map_zero] at z'
    unfold pc
    rw [← MonObj.comp_mul, ← pow_two]
    exact z'
  obtain ⟨φ, hφ⟩ : ∃ φ : LB.Gen (Out.thetaLB A (P.pull (lift (𝟙 A) (𝟙 A)).left) 1 a), φ.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hD _ _)).1 ?_
    rw [cls_linComb hD, Fin.sum_univ_two]
    show (1 : ℤ) • pull (snd T A).left _ + (-1 : ℤ) • pull ((fst T A ≫ a) * snd T A).left _ = 0
    rw [e, e, hB, hB', hB', hsw _ (snd T A) (fst T A ≫ a), haa]
    calc _ = -(pc hP (fst T A ≫ a) (snd T A) + pc hP (fst T A ≫ a) (snd T A)) := by abel
      _ = 0 := by rw [ha2', neg_zero]
  have h1 : Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) 1 a 1 1 :=
    DescendedPrincipal.weilIs_one_right hG hA hD fun p => by
      obtain ⟨θ, hθ⟩ := CommutatorPairing.exists_pull hD (⟨a, φ, hφ⟩ : Out.ThetaGrp A _ 1 T)
        (Out.overResι (⊤ : T.left.Opens))
      exact ⟨⊤, trivial, θ, hθ⟩
  have h1' := CommPairing.weilIs_symm hD h1
  have hc' := CommPairing.weilIs_symm hD hc
  rw [inv_one, ← hb] at h1'
  have hc'' : Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) ((1 : ℤ) * (m : ℕ)) b a c⁻¹ := by
    rw [_root_.one_mul]; exact hc'
  have key := PairingLevels.weilIs_value_eq hG hA hD ht hc'' h1'
  exact inv_eq_one.1 key

end GlobalTheory.WeilSqKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingPullbackPowerMapLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutatorPairing_pullback_powerMap_level : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (H₀ : LB A.left) (P : LB (G2 A).left), IsAbelianScheme A → H₀.IsLB → Out.RelAmple A H₀ → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (m a b : ℕ) (n : ℤ) (T : Over S) (x₁ x₂ y₁ y₂ : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) (GlobalTheory.UPel.HT.Hecke.lbPow P m) n (lift (x₁ ^ a) (x₂ ^ b)) (lift (y₁ ^ a) (y₂ ^ b)) c → Out.WeilIs (G2 A) P (n * ((m * a * b : ℕ) : ℤ)) (lift x₁ x₂) (lift y₁ y₂) c := by
  first | (exact @GlobalTheory.HeckePullLevel.weilIs_powPull) | (exact GlobalTheory.HeckePullLevel.weilIs_powPull) | (intros; apply GlobalTheory.HeckePullLevel.weilIs_powPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemGivesThickeningTower
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem isSystem_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R))
    (t : ℕ → W.IdealSheafData), IsSystem f I t →
    ∃ (q : ∀ e, (t e).subscheme ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
      (β : ∀ e, (t e).subscheme ⟶ (t (e + 1)).subscheme),
      (∀ e, (t e).subschemeι ≫ f = q e ≫ thick R I e) ∧
      (∀ e, β e ≫ (t (e + 1)).subschemeι = (t e).subschemeι) ∧
      ∀ e, IsPullback (β e) (q e) (q (e + 1)) (thickTrans R I e) := by
  intro R _ I W f t ht
  have hci : ∀ e, IsClosedImmersion (thick R I e) := fun e =>
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))
      Ideal.Quotient.mk_surjective
  have hmono : ∀ e, Mono (thick R I e) := fun e => by haveI := hci e; infer_instance
  have hfst : ∀ e, (pullback.fst f (thick R I e)).ker = baseIdeal f (I ^ (e + 1)) := by
    intro e
    haveI := hci e
    have h := (_root_.GlobalTheory.FormalAlg.reduces_iff_ker_eq R (I ^ (e + 1)) W W (pullback f (thick R I e)) f (𝟙 W)
      (pullback.fst f (thick R I e)) (pullback.snd f (thick R I e)) inferInstance inferInstance
      pullback.condition).1
      ⟨pullback.fst f (thick R I e), Category.comp_id _, by
        simpa using IsPullback.of_hasPullback f (thick R I e)⟩
    simpa using h.symm
  have hle : ∀ e, (pullback.fst f (thick R I e)).ker ≤ (t e).subschemeι.ker := fun e => by
    rw [hfst, Scheme.IdealSheafData.ker_subschemeι]
    exact ht.baseIdeal_le e
  let q : ∀ e, (t e).subscheme ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) := fun e =>
    haveI := hci e
    IsClosedImmersion.lift (pullback.fst f (thick R I e)) (t e).subschemeι (hle e) ≫ pullback.snd _ _
  have hq : ∀ e, (t e).subschemeι ≫ f = q e ≫ thick R I e := fun e => by
    haveI := hci e
    simp only [q, Category.assoc, ← pullback.condition]
    rw [← Category.assoc, IsClosedImmersion.lift_fac]
  clear_value q
  have hb : ∀ e, ∃ b : (t e).subscheme ⟶ (t (e + 1)).subscheme, b ≫ (t (e + 1)).subschemeι = (t e).subschemeι ∧
      IsPullback b (q e) ((t (e + 1)).subschemeι ≫ f) (thick R I e) := fun e =>
    (_root_.GlobalTheory.FormalAlg.reduces_iff_ker_eq R (I ^ (e + 1)) W _ _ f (t (e + 1)).subschemeι (t e).subschemeι (q e)
      inferInstance inferInstance (hq e)).2
      (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]; exact (ht e).symm)
  choose β hβ using hb
  refine ⟨q, β, hq, fun e => (hβ e).1, fun e => ?_⟩
  have hbot : IsPullback (thickTrans R I e) (𝟙 _) (thick R I (e + 1)) (thick R I e) := by
    haveI := hmono (e + 1)
    refine IsPullback.of_isLimit' ⟨by simp [thickTrans_comp]⟩ ?_
    refine PullbackCone.IsLimit.mk _ (fun s => s.snd) (fun s => ?_) (fun s => by simp)
      (fun s m _ h2 => by simpa using h2)
    rw [← cancel_mono (thick R I (e + 1)), Category.assoc, thickTrans_comp]
    exact s.condition.symm
  have hcomm : β e ≫ q (e + 1) = q e ≫ thickTrans R I e := by
    haveI := hmono (e + 1)
    rw [← cancel_mono (thick R I (e + 1))]
    calc (β e ≫ q (e + 1)) ≫ thick R I (e + 1) = β e ≫ (t (e + 1)).subschemeι ≫ f := by
          rw [Category.assoc, hq]
      _ = (t e).subschemeι ≫ f := by rw [← Category.assoc, (hβ e).1]
      _ = q e ≫ thick R I e := hq e
      _ = (q e ≫ thickTrans R I e) ≫ thick R I (e + 1) := by rw [Category.assoc, thickTrans_comp]
  refine IsPullback.of_bot ?_ hcomm hbot
  rw [Category.comp_id, ← hq]
  exact (hβ e).2

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConductorSquareFlatBaseChangeSchemes
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch.FlatSq

open TensorProduct

theorem inj_of_isPushout {A B F G : Type} [CommRing A] [CommRing B] [CommRing F] [CommRing G]
    (f : A →+* F) (g : A →+* B) (h : F →+* G) (k : B →+* G)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom h) (CommRingCat.ofHom k))
    (hf : f.Flat) (hg : Function.Injective g) : Function.Injective h := by
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := h.toAlgebra
  letI := k.toAlgebra
  letI : Algebra A G := (h.comp f).toAlgebra
  haveI : IsScalarTower A F G := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A B G := IsScalarTower.of_algebraMap_eq (fun a => by
    have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) sq.w
    simpa [RingHom.algebraMap_toAlgebra] using this)
  haveI : Module.Flat A F := hf
  have hP : Algebra.IsPushout A F B G := (CommRingCat.isPushout_iff_isPushout).1 sq
  have hP' : Algebra.IsPushout A B F G := hP.symm
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have e1 : Algebra.IsPushout.equiv A B F G ((1 : B) ⊗ₜ x) = 0 := by
    rw [Algebra.IsPushout.equiv_tmul]; simpa [RingHom.algebraMap_toAlgebra] using hx
  have e2 : ((1 : B) ⊗ₜ[A] x) = 0 := by
    simpa using (Algebra.IsPushout.equiv A B F G).injective (e1.trans (map_zero _).symm)
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := F) (Algebra.linearMap A B) hg
  have e3 : LinearMap.rTensor F (Algebra.linearMap A B) ((1 : A) ⊗ₜ x) = 0 := by simpa using e2
  have e4 : ((1 : A) ⊗ₜ[A] x) = 0 := hinj (e3.trans (map_zero _).symm)
  simpa using congrArg (TensorProduct.lid A F) e4

end GlobalTheory.Pinch.FlatSq

namespace GlobalTheory.Pinch.FlatSq

open TensorProduct

theorem ideal_mul_of_isPushout {A B F G : Type} [CommRing A] [CommRing B] [CommRing F] [CommRing G]
    (f : A →+* F) (g : A →+* B) (h : F →+* G) (k : B →+* G)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom h) (CommRingCat.ofHom k))
    (J : Ideal A) (hJ : ∀ a ∈ J, ∀ b : B, ∃ a' ∈ J, g a' = g a * b) :
    ∀ x ∈ J.map f, ∀ r : G, ∃ y ∈ J.map f, h y = h x * r := by
  have hw : ∀ a, k (g a) = h (f a) := fun a => by
    have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) sq.w
    simpa using this.symm
  have hQ : ∀ x ∈ J.map f, ∀ b : B, ∃ y ∈ J.map f, h y = h x * k b := by
    intro x hx
    change x ∈ Ideal.span _ at hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      intro b
      obtain ⟨a', ha', e⟩ := hJ a ha b
      refine ⟨f a', Ideal.mem_map_of_mem f ha', ?_⟩
      rw [← hw, ← hw, e, map_mul]
    | zero => intro b; exact ⟨0, Ideal.zero_mem _, by simp⟩
    | add z w _ _ hz hw' =>
      intro b
      obtain ⟨y1, hy1, e1⟩ := hz b
      obtain ⟨y2, hy2, e2⟩ := hw' b
      exact ⟨y1 + y2, Ideal.add_mem _ hy1 hy2, by rw [map_add (f := _), e1, e2, map_add (f := _), add_mul]⟩
    | smul m z _ hz =>
      intro b
      obtain ⟨y1, hy1, e1⟩ := hz b
      refine ⟨m * y1, Ideal.mul_mem_left _ m hy1, ?_⟩
      rw [smul_eq_mul, map_mul, e1, map_mul]; ring
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := h.toAlgebra
  letI := k.toAlgebra
  letI : Algebra A G := (h.comp f).toAlgebra
  haveI : IsScalarTower A F G := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A B G := IsScalarTower.of_algebraMap_eq (fun a => (hw a).symm)
  have hP : Algebra.IsPushout A F B G := (CommRingCat.isPushout_iff_isPushout).1 sq
  have hP' : Algebra.IsPushout A B F G := hP.symm
  intro x hx r
  induction r using hP'.out.inductionOn with
  | tmul m =>
    refine ⟨x * m, Ideal.mul_mem_right _ _ hx, ?_⟩
    rw [map_mul]; rfl
  | smul b n hn =>
    obtain ⟨y1, hy1, e1⟩ := hn
    obtain ⟨y, hy, e⟩ := hQ y1 hy1 b
    refine ⟨y, hy, ?_⟩
    rw [e, e1, Algebra.smul_def, RingHom.algebraMap_toAlgebra]; ring
  | add n1 n2 h1 h2 =>
    obtain ⟨y1, hy1, e1⟩ := h1
    obtain ⟨y2, hy2, e2⟩ := h2
    exact ⟨y1 + y2, Ideal.add_mem _ hy1 hy2, by rw [map_add (f := _), e1, e2, mul_add]⟩

theorem ker_le_of_isPushout {A Q F G : Type} [CommRing A] [CommRing Q] [CommRing F] [CommRing G]
    (f : A →+* F) (q : A →+* Q) (h : F →+* G) (k : Q →+* G)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom q) (CommRingCat.ofHom h) (CommRingCat.ofHom k))
    (hq : Function.Surjective q) (x : F) (hx : h x = 0) : x ∈ (RingHom.ker q).map f := by
  letI := f.toAlgebra
  letI := q.toAlgebra
  letI := h.toAlgebra
  letI := k.toAlgebra
  letI : Algebra A G := (h.comp f).toAlgebra
  haveI : IsScalarTower A F G := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower A Q G := IsScalarTower.of_algebraMap_eq (fun a => by
    have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) sq.w
    simpa [RingHom.algebraMap_toAlgebra] using this)
  have hP : Algebra.IsPushout A F Q G := (CommRingCat.isPushout_iff_isPushout).1 sq
  have hs : Function.Surjective (Algebra.ofId A Q) := hq
  let e1 := Algebra.TensorProduct.quotIdealMapEquivTensorQuot F (RingHom.ker (Algebra.ofId A Q))
  let e2 : F ⊗[A] (A ⧸ RingHom.ker (Algebra.ofId A Q)) ≃ₐ[A] F ⊗[A] Q :=
    Algebra.TensorProduct.congr AlgEquiv.refl (Ideal.quotientKerAlgEquivOfSurjective hs)
  let e3 := Algebra.IsPushout.equiv A F Q G
  have key : e3 (e2 (e1 (Ideal.Quotient.mk _ x))) = 0 := by
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    simp only [e2, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, AlgEquiv.coe_algHom, map_one]
    rw [Algebra.IsPushout.equiv_tmul]
    simpa [RingHom.algebraMap_toAlgebra] using hx
  have : Ideal.Quotient.mk (Ideal.map (algebraMap A F) (RingHom.ker (Algebra.ofId A Q))) x = 0 := by
    apply e1.injective; apply e2.injective; apply e3.injective
    rw [key]; simp
  rw [Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

end GlobalTheory.Pinch.FlatSq

namespace GlobalTheory.Pinch.FlatSq

theorem spMap_appLE_apply {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')
    (e : (⊤ : (Sp R').Opens) ≤ spMap φ ⁻¹ᵁ ⊤) (a : Γ(Sp R, ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of R')).hom (((spMap φ).appLE ⊤ ⊤ e).hom a) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom a) := by
  have h1 : (spMap φ).appLE ⊤ ⊤ e = (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  have := congrArg (fun t => t.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
  rw [h1]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this

theorem cond_of_flat (R : Type) [CommRing R] (R' : Type) [CommRing R'] [Algebra R R']
    (hinj : Function.Injective (algebraMap R R')) (c : Ideal R)
    (hc : ∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r)
    (X X' Z : Scheme.{0}) (u : X ⟶ Sp R) (p : X' ⟶ X) (u' : X' ⟶ Sp R') (i : Z ⟶ X) (v : Z ⟶ Sp (R ⧸ c))
    (hu : Flat u) (hp : IsPullback p u' u (spMap (algebraMap R R')))
    (hi : IsPullback i v u (spMap (Ideal.Quotient.mk c))) : GlobalTheory.Pinch.Cond p i := by
  intro W hW
  have poP := (isIso_pushoutSection_iff hp (US := ⊤) (UT := ⊤) (UX := W) (UY := p ⁻¹ᵁ W) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen hp _ _ _ (isAffineOpen_top _)
    (isAffineOpen_top _) hW)
  have poZ := (isIso_pushoutSection_iff hi (US := ⊤) (UT := ⊤) (UX := W) (UY := i ⁻¹ᵁ W) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen hi _ _ _ (isAffineOpen_top _)
    (isAffineOpen_top _) hW)
  have hfl : (u.appLE ⊤ W le_top).hom.Flat :=
    HasRingHomProperty.appLE (P := @Flat) u hu ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  let eR := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let eR' := (Scheme.ΓSpecIso (CommRingCat.of R')).commRingCatIsoToRingEquiv
  let eQ := (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ c))).commRingCatIsoToRingEquiv
  let gA := ((spMap (algebraMap R R')).appLE ⊤ ⊤ le_top).hom
  let qA := ((spMap (Ideal.Quotient.mk c)).appLE ⊤ ⊤ le_top).hom
  have hg : ∀ a, eR' (gA a) = algebraMap R R' (eR a) := fun a => spMap_appLE_apply _ _ a
  have hq : ∀ a, eQ (qA a) = Ideal.Quotient.mk c (eR a) := fun a => spMap_appLE_apply _ _ a
  have gA_inj : Function.Injective gA := by
    intro a b hab
    apply eR.injective; apply hinj
    rw [← hg, ← hg, hab]
  have qA_surj : Function.Surjective qA := by
    intro t
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (eQ t)
    refine ⟨eR.symm z, eQ.injective ?_⟩
    rw [hq, RingEquiv.apply_symm_apply, hz]
  let J := RingHom.ker qA
  have hJ : ∀ a ∈ J, ∀ b, ∃ a' ∈ J, gA a' = gA a * b := by
    intro a ha b
    have hx : eR a ∈ c := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hq, RingHom.mem_ker.1 ha, map_zero]
    obtain ⟨y, hy, e⟩ := hc (eR a) hx (eR' b)
    refine ⟨eR.symm y, ?_, eR'.injective ?_⟩
    · rw [RingHom.mem_ker]; apply eQ.injective
      rw [hq, RingEquiv.apply_symm_apply, map_zero, Ideal.Quotient.eq_zero_iff_mem]; exact hy
    · rw [hg, RingEquiv.apply_symm_apply, e, map_mul, hg]
  refine ⟨?_, ?_⟩
  · rw [Scheme.Hom.app_eq_appLE]
    exact inj_of_isPushout _ _ _ _ poP hfl gA_inj
  · intro x hx r
    rw [Scheme.Hom.app_eq_appLE] at hx
    have hxJ := ker_le_of_isPushout _ _ _ _ poZ qA_surj x hx
    obtain ⟨y, hy, e⟩ := ideal_mul_of_isPushout _ _ _ _ poP J hJ x hxJ r
    refine ⟨y, ?_, ?_⟩
    · rw [Scheme.Hom.app_eq_appLE]
      have hle : J.map (u.appLE ⊤ W le_top).hom ≤ RingHom.ker (i.appLE W (i ⁻¹ᵁ W) le_rfl).hom := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        rw [Ideal.mem_comap, RingHom.mem_ker]
        have := congrArg (fun φ => (CommRingCat.Hom.hom φ) a) poZ.w
        simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
        have h0 : qA a = 0 := RingHom.mem_ker.1 ha
        simp only [qA] at h0
        rw [this, h0, map_zero]
      exact hle hy
    · rw [Scheme.Hom.app_eq_appLE]; exact e

end GlobalTheory.Pinch.FlatSq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongruenceSubgroupIndicatorWeight
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.CongMatch

lemma unit_product_rescale_disjoint_finsets (q : ℕ) (hq : q ≠ 0) (v : ℤ) (N : ℕ) (X : ℚ) :
    ((-((Real.sqrt (((q ^ 2 : ℕ)) : ℝ) : ℝ) : ℂ)) ^ N)⁻¹ * ((((-(q : ℚ)) ^ (-(v - ((N : ℕ) : ℤ))) * X : ℚ)) : ℂ) =
      ((-1 : ℂ) ^ v * ((Real.sqrt ((((q ^ 2 : ℕ)) : ℝ) ^ (-v)) : ℝ) : ℂ)) * (X : ℂ) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : Real.sqrt (((q ^ 2 : ℕ)) : ℝ) = q := by push_cast; exact Real.sqrt_sq hq0
  have h2 : Real.sqrt ((((q ^ 2 : ℕ)) : ℝ) ^ (-v)) = (q : ℝ) ^ (-v) := by
    push_cast
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul]
    exact Real.sqrt_sq (by positivity)
  rw [h1, h2]
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hm : (-(q : ℂ)) ≠ 0 := neg_ne_zero.2 hqc
  push_cast
  have e1 : (-(q : ℂ)) ^ (-(v - (N : ℤ))) = (-(q : ℂ)) ^ (N : ℤ) * (-(q : ℂ)) ^ (-v) := by
    rw [← zpow_add₀ hm]; congr 1; ring
  have e2 : (-(q : ℂ)) ^ (-v) = (-1 : ℂ) ^ v * (q : ℂ) ^ (-v) := by
    rw [neg_eq_neg_one_mul, mul_zpow]
    congr 1
    rw [_root_.zpow_neg, ← _root_.inv_zpow, inv_neg, inv_one]
  rw [e1, e2, zpow_natCast]
  field_simp

theorem match_principal_congruence_inert : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (n a b k : ℕ), a + b = n → 1 ≤ k → Match n a b w 1 ((({γ : UL n w | γ.1 ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}} : Set (UL n w))).indicator 1) (fun y : GLw a w × GLw b w => ((-((Real.sqrt (qV E w : ℝ) : ℝ) : ℂ)) ^ (k * a * b))⁻¹ * (if y.1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w (n := a) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w (n := b) ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w (n := b) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) := by
  intro E _ _ _ hU w hw n a b k hab hk
  obtain ⟨K, e, he1, he2, he3, hq⟩ := GlobalTheory.InertUQ.exists_uq E hU w hw
  obtain ⟨t, ht, htv⟩ := GlobalTheory.T.exists_small_conjFixed_of_valuation K k hk
  intro Q₁ Q₂ hm₁ hm₂ hd₁ hd₂ hsep hc₁ hc₂
  obtain ⟨B₁, h11, h12, h13, h14⟩ := _root_.GlobalTheory.InvAlgConstr.exists_invAlg_adjoinRoot E w hw K e he1 t ht.1 Q₁ hm₁ hc₁
  obtain ⟨B₂, h21, h22, h23, h24⟩ := _root_.GlobalTheory.InvAlgConstr.exists_invAlg_adjoinRoot E w hw K e he1 t ht.1 Q₂ hm₂ hc₂
  obtain ⟨hsB, hres⟩ := _root_.GlobalTheory.UnitLemma.ShiftRes.val_resultant_shift E w K e he3 k t ht.1 htv a b Q₁ Q₂ B₁ B₂ hm₁ hm₂ hd₁ hd₂ hsep h11 h12 h13 h21 h22 h23
  have hid := _root_.GlobalTheory.UnitLemma.CongruenceCayley.identity_of_principal_congruence (GlobalTheory.T.unitLemma_lieAlgebra_unitaryGroup_of_jacquetRallis _root_.GlobalTheory.JR.unitMatch_all).1 K t ht B₁ B₂ h14 h24 hsB
  rw [GlobalTheory.T.stableTwistedOrbitalIntegral_integralNormCongruence_product E w hw a b k Q₁ Q₂ _ hm₁ hm₂ hd₁ hd₂ hsep,
    GlobalTheory.T.twistedOrbitalIntegral_levelFunction_inert_eq_latticeCount E hU w hw K e he1 he2 he3 hq k t ht htv a Q₁ B₁ hm₁ hd₁ hsep.of_mul_left hc₁ h11 h12 h13 h14,
    GlobalTheory.T.twistedOrbitalIntegral_levelFunction_inert_eq_latticeCount E hU w hw K e he1 he2 he3 hq k t ht htv b Q₂ B₂ hm₂ hd₂ hsep.of_mul_right hc₂ h21 h22 h23 h24,
    GlobalTheory.T.kappaOrbitalIntegral_congruence_inert_latticeCount E hU w hw K e he1 he2 he3 hq k t ht htv n a b Q₁ Q₂ B₁ B₂ hab hm₁ hm₂ hd₁ hd₂ hsep hc₁ hc₂
      h11 h12 h13 h14 h21 h22 h23 h24]
  unfold GlobalTheory.UnitLemma.InvAlg.Identity at hid
  rw [← Rat.cast_mul, ← hid, hres]
  have hq0 : K.q ≠ 0 := by
    intro h0
    have hc := K.card_res
    rw [h0] at hc
    haveI : Nonempty (IsLocalRing.ResidueField K.O) := ⟨0⟩
    have := Nat.card_pos (α := IsLocalRing.ResidueField K.O)
    simp at hc; omega
  unfold delta absHalf
  rw [if_neg hw, hq]
  exact unit_product_rescale_disjoint_finsets K.q hq0 _ (k * a * b) _

end GlobalTheory.CongMatch
end

