module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0374
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0312
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FirstHalfLocalCohomologyVanishingOfLocalDualityT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import GroundTheory.LocalFields.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfForallAnnihilatorAnnihilatorFieldModInteger
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultVTwistedDual
section
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.DualJump

open GlobalTheory.DRFil GlobalTheory.DRDual

theorem multV_twisted_dual {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K LL : FinExt l) {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
    {V' : Type} [AddCommGroup V'] [Module ↥LL.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥LL.1 V']
    [FiniteDimensional ↥LL.1 V'] (ρ' : Representation ↥LL.1 ↥(GK K) V')
    (m : V →ₗ[↥LL.1] V' →ₗ[↥LL.1] ↥LL.1) (j : ℤ) (hm : Function.Bijective m)
    (hg : ∀ g x y, m (ρ g x) (ρ' g y) = ((cycLL (P.PD K) ↥LL.1 g ^ j : (↥LL.1)ˣ) : ↥LL.1) * m x y)
    (h : IsDR (P.PD K) ρ) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) :
    multV (P.PD K) ρ' τ (-a - j) = multV (P.PD K) ρ τ a := by
  have := K.2
  have := LL.2
  have := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
  have hs := filSpans T K LL ρ h
  let ρ₀ : Representation ↥LL.1 ↥(GK K) V' := twistRep (cycLL (P.PD K) ↥LL.1 ^ (-j)) ρ'
  have hρ₀ : ∀ g y, ρ₀ g y = ((cycLL (P.PD K) ↥LL.1 g ^ (-j) : (↥LL.1)ˣ) : ↥LL.1) • ρ' g y :=
    fun g y => rfl
  have hβ : ∀ g x y, m (ρ g x) (ρ₀ g y) = m x y := fun g x y => by
    rw [hρ₀, map_smul, hg, smul_eq_mul, zpow_neg, Units.inv_mul_cancel_left]
  have hβ' : Function.Bijective m.flip := (LinearEquiv.ofBijective m hm).flip.bijective
  have ht : (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K : P.R.BdR) = (P.PD K).ι (P.PD K).t := rfl
  obtain ⟨-, h2⟩ := twist_unit (P.PD K) ρ₀ ρ' (GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR P K ^ (-j)) (-j)
    (fun g => (P.PD K).χ g ^ (-j)) (tdR_zpow_mem T K _)
    (by rw [← zpow_neg]; exact tdR_zpow_mem T K _) (act_zpow _ _ ht _)
    (fun g => by rw [← zpow_neg, ← zpow_neg]; exact act_zpow _ _ ht _ g)
    (fun g x => by
      rw [hρ₀, ← algebraMap_smul ↥LL.1]
      congr 1
      exact congrArg Units.val
        (map_zpow (Units.map (algebraMap ℚ_[l] ↥LL.1 : ℚ_[l] →* ↥LL.1)) ((P.PD K).χ g) (-j)))
  obtain ⟨n, d, k, had⟩ := GlobalTheory.DRFil.exists_adapted (P.PD K) (isField_dR T) ρ hs τ
  obtain ⟨d', had'⟩ := had.dual ρ₀ m hβ hβ'
  rw [show -a - j = -j + -a by ring, h2, had.multV_eq, had'.multV_eq]
  simp only [neg_inj]

theorem dualJumpL : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)), (∀ (l : ℕ) [Fact l.Prime], Nonempty (LocTied l (L l) (A l))) → DualJumpL L := by
  intro L AI hT l _ K LL A A' m hm h τ a
  obtain ⟨T⟩ := hT l
  obtain ⟨hg, h1, -, hd⟩ := hm
  have hi : Function.Injective m :=
    (injective_iff_map_eq_zero m).2 fun x hx => h1 x fun y => by rw [hx, LinearMap.zero_apply]
  have hb : Function.Bijective m :=
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hd.trans (Subspace.dual_finrank_eq (K := ↥LL.1) (V := A'.V)).symm)).1 hi⟩
  have key := multV_twisted_dual T K LL A.ρ A'.ρ m 1 hb (fun g x y => by rw [zpow_one]; exact hg g x y) h τ (-a - 1)
  rw [show -(-a - 1) - 1 = a by ring] at key
  rw [(GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l (L l) (AI l) T K LL A'.V A'.ρ τ a).2.2,
    (GlobalTheory.Per.JumpMult.jump_iff_mult_ne_zero l (L l) (AI l) T K LL A.V A.ρ τ (-a - 1)).2.2, key]

end GlobalTheory.DualJump
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoInvDualOfSetup
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime


open IsLocalRing GlobalTheory.ScalarFrob in
theorem noInvDual_of_setup : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (z : GE N), Setup bkP i s κ Q → IsDual i s ρ → IsTameInertiaElementAtTwistPrime X i z → NoInvDual i κ ρ := by
  intro D N X bkP i s A _ _ _ _ κ Q ρ z hS hρ hz Y' _ _ m hm
  obtain ⟨h, hloc, -, -, hκ, -⟩ := hS
  obtain ⟨e, he, -, hu, hε⟩ := GlobalTheory.TwSys.TameScalar.exists_scalar_tmat_of_tame_inertia D N X bkP i s z h.1 hz
  have c0 : residue (X.O0 i) e ≠ 0 := (residue_ne_zero_iff_isUnit _).2 e.isUnit
  have c1 : residue (X.O0 i) e ≠ 1 := by
    rw [← residue_ne_zero_iff_isUnit, map_sub, map_one, sub_ne_zero] at hu
    exact hu
  have e1 : resT i s z = residue (X.O0 i) e • 1 := by
    rw [resT_apply, he]
    ext a b
    by_cases hab : a = b <;> simp [hab]
  have e2 := dual_of_scalar i s (by rw [hε]; simp) c0 e1
  rw [← hρ z] at e2
  have hκ' : ∃ n : ℕ, κ⁻¹ z ^ (X.l i ^ n) = 1 := by
    obtain ⟨n, hn⟩ := hκ z
    exact ⟨n, by rw [MonoidHom.inv_apply, inv_pow, hn, inv_one]⟩
  exact eq_zero_of_scalar Fact.out (GlobalTheory.PrimeToInertia.l_mem i) ρ κ⁻¹ hκ' (inv_ne_one.2 c1) e2 (q := 1) Nat.cast_one m
    (by rw [one_smul]; exact hm z)

end GlobalTheory.NewPrime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PairingEquivariant
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.PairEquiv

section General

variable {A : Type} [CommRing A] {Y Y' : Type} [AddCommGroup Y] [Module A Y] [AddCommGroup Y'] [Module A Y'] {n r : ℕ}

theorem vecPair_matAct {β : Y →+ Y' →+ ZMod n} (hβ : Bal A β) (T : Matrix (Fin r) (Fin r) A) (x : Fin r → Y)
    (y : Fin r → Y') : vecPair r β (matAct T x) y = vecPair r β x (matAct T.transpose y) := by
  rw [vecPair_apply, vecPair_apply]
  change ∑ c, β (∑ a, T c a • x a) (y c) = ∑ a, β (x a) (∑ c, T c a • y c)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, AddMonoidHom.finsetSum_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => hβ _ _ _

theorem vecPair_smul {β : Y →+ Y' →+ ZMod n} (hβ : Bal A β) (k : A) (x : Fin r → Y)
    (y : Fin r → Y') : vecPair r β (k • x) y = vecPair r β x (k • y) := by
  rw [vecPair_apply, vecPair_apply]
  exact Finset.sum_congr rfl fun a _ => hβ _ _ _

theorem tors_of_finite [IsLocalRing A] [Finite A] (b : Y) :
    ∃ m, ∀ x ∈ IsLocalRing.maximalIdeal A ^ m, x • b = 0 := by
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at hm
  refine ⟨m, fun x hx => ?_⟩
  rw [hm, Ideal.zero_eq_bot, Ideal.mem_bot] at hx
  rw [hx, zero_smul]

theorem map_padicInt_eq_val {l : ℕ} [Fact l.Prime] (f : ℤ_[l] →+* A) {m : ℕ} (h : (l : A) ^ m = 0) (a : ℤ_[l]) :
    f a = ((PadicInt.toZModPow m a).val : A) := by
  have h1 : a - ((PadicInt.toZModPow m a).val : ℤ_[l]) ∈ RingHom.ker (PadicInt.toZModPow m) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
  obtain ⟨c, hc⟩ := h1
  have h2 := congrArg f hc
  rw [map_sub, map_natCast, map_mul, map_pow, map_natCast, h, zero_mul, sub_eq_zero] at h2
  exact h2

end General

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem transpose_mul_Tdual (i : X.Tw) (s : X.Sig i) (g : GE N) :
    (Tmat i s g).transpose * Tdual i s g = ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • 1 := by
  have h3 : IsUnit (Tmat i s g).det := by
    rw [← Tgl_coe]; exact Matrix.isUnits_det_units _
  rw [Tdual, Matrix.mul_smul, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ h3, Matrix.transpose_one]

theorem pairing_equivariant : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Setup bkP i s κ Q → Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y] (Y' : Type) [AddCommGroup Y'] [Module A Y'] [TopologicalSpace Y'] [DiscreteTopology Y'] (β : Y →+ Y' →+ ZMod (X.l i ^ (nu X i + 1))), Bal A β → ContAction (repOn (Tgl i s) κ Y) ∧ ContAction (repOn ρ κ⁻¹ Y') ∧ (∀ g x y, vecPair D.R.r β (repOn (Tgl i s) κ Y g x) (repOn ρ κ⁻¹ Y' g y) = ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))) * vecPair D.R.r β x y) ∧ ∀ v, v ∉ placesOver D.host.E (X.l i) → v ∉ Spl i → v ∉ Q → ∀ B : ValuationSubring N.Om, IsPlaceOver B v → ∀ τ ∈ Ine (F := D.host.E) B, repOn (Tgl i s) κ Y τ = 1 ∧ repOn ρ κ⁻¹ Y' τ = 1 := by
  intro D N X bkP i s A _ _ _ _ κ Q ρ hS hK hρ Y _ _ _ _ Y' _ _ _ _ β hβ
  have := hS.2.1
  have hκ := hS.2.2.2.1
  refine ⟨?_, ?_, fun g x y => ?_, fun v hl hv hQ B hB τ hτ => ?_⟩
  · refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) _ ?_ κ hκ tors_of_finite
    simp_rw [Tgl_coe]; exact GlobalTheory.PrimeToInertia.continuous_Tmat i s
  · refine GlobalTheory.PrimeToInertia.contAction_repOn (X.twistBaseCoefficientRing_isAdic i) _ ?_ κ⁻¹ ?_ tors_of_finite
    · simp_rw [hρ _]; exact GlobalTheory.PrimeToInertia.continuous_Tdual i s
    · convert hκ using 2
      ext g
      simp [MonoidHom.mem_ker]
  · have hl : ((X.l i : ℕ) : A) ^ (nu X i + 1) = 0 := by
      have := hK ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i))
        (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (GlobalTheory.PrimeToInertia.l_mem i))
      rwa [map_mul, map_pow, map_natCast, ← pow_succ] at this
    have he : algebraMap (X.O0 i) A ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) =
        (((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))).val : A) :=
      map_padicInt_eq_val ((algebraMap (X.O0 i) A).comp (algebraMap ℤ_[X.l i] (X.O0 i))) hl _
    change vecPair _ β ((κ g : A) • matAct ((Tgl i s g : Matrix _ _ (X.O0 i)).map (algebraMap (X.O0 i) A)) x)
      (((κ g)⁻¹ : Aˣ).val • matAct ((ρ g : Matrix _ _ (X.O0 i)).map (algebraMap (X.O0 i) A)) y) = _
    rw [vecPair_smul hβ, smul_smul, Units.mul_inv, one_smul, vecPair_matAct hβ, ← Module.End.mul_apply, ← matAct_mul,
      ← Matrix.transpose_map, ← Matrix.map_mul, hρ, Tgl_coe, transpose_mul_Tdual]
    have e : matAct ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) • (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i))).map
        (algebraMap (X.O0 i) A)) y =
        ((cycMod D.host.E N.Om (X.l i) (nu X i + 1) g : (ZMod (X.l i ^ (nu X i + 1)))ˣ) : ZMod (X.l i ^ (nu X i + 1))).val • y := by
      funext a
      rw [← Nat.cast_smul_eq_nsmul A, ← he]
      change ∑ b, algebraMap (X.O0 i) A (((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) * (1 : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) a b) • y b = _
      simp [Matrix.one_apply, apply_ite (algebraMap (X.O0 i) A), ite_smul]
    rw [e, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
  · have h1 := GlobalTheory.SelFun.Colim.tgl_eq_one bkP i s hS.1.1 v hl hv B hB τ hτ
    have h2 := hS.2.2.2.2.2.2.2 v hQ B hB τ hτ
    have h3 : cycZ D.host.E N.Om (X.l i) τ = 1 := by
      refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
      rw [cycZ_toZModPow_eq hl hB (q := 1) (fun x hx => by simpa using hτ.2 x hx) n]
      simp
    have h4 : eps0 X i τ = 1 := by
      rw [eps0, MonoidHom.comp_apply, h3, map_one]
    have h5 : ρ τ = 1 := by
      apply Units.ext
      rw [hρ, Tdual, h4, ← Tgl_coe, h1]
      simp
    exact ⟨LinearMap.ext (GlobalTheory.SelFun.Colim.repOn_eq_of_eq_one _ _ h1 h2),
      LinearMap.ext (GlobalTheory.SelFun.Colim.repOn_eq_of_eq_one _ _ h5 (by simp [h2]))⟩

end GlobalTheory.NewPrime.PairEquiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PerfectPairingFiniteModuleRowsCriterion
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun
  GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.CharDual

theorem exists_char_ne_zero (n : ℕ) (hn : n ≠ 0) {G : Type} [AddCommGroup G]
    (hG : ∀ g : G, n • g = 0) {g : G} (hg : g ≠ 0) : ∃ φ : G →+ ZMod n, φ g ≠ 0 := by
  haveI : NeZero n := ⟨hn⟩
  letI : Module (ZMod n) G := AddCommGroup.zmodModule hG
  obtain ⟨f, hf⟩ := GlobalTheory.ZModPerp.exists_dual_ne_zero (n := n) hg
  exact ⟨f.toAddMonoidHom, hf⟩

variable (A : Type) [CommRing A] (n : ℕ)

def charModule : Module A (A →+ ZMod n) where
  smul a φ := φ.comp (AddMonoidHom.mulLeft a)
  one_smul φ := by
    ext b
    show φ (1 * b) = φ b
    rw [one_mul]
  mul_smul a a' φ := by
    ext b
    show φ (a * a' * b) = φ (a' * (a * b))
    rw [mul_left_comm, mul_assoc]
  smul_zero a := by ext b; rfl
  smul_add a φ ψ := by ext b; rfl
  add_smul a a' φ := by
    ext b
    show φ ((a + a') * b) = φ (a * b) + φ (a' * b)
    rw [add_mul, map_add (f := _)]
  zero_smul φ := by
    ext b
    show φ (0 * b) = 0
    rw [zero_mul, map_zero]

end GlobalTheory.NewPrime.CharDual

namespace GlobalTheory.NewPrime


open GlobalTheory.NewPrime.CharDual in
theorem charDual_cogenerator : ∀ (A : Type) [CommRing A] [Finite A] (n : ℕ), n ≠ 0 → (n : A) = 0 →
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module A Y) (_ : Finite Y) (β : Y →+ A →+ ZMod n),
      Perf A β ∧ ∀ (a : ℕ) (Φ : Matrix (Fin a) (Fin a) A) (v : Fin a → A),
        (∀ x : Fin a → Y, matAct Φ x = 0 → ∑ j, v j • x j = 0) → v ∈ what₂ Φ := by
  intro A _ _ n hn hnA
  haveI : NeZero n := ⟨hn⟩
  letI : Module A (A →+ ZMod n) := charModule A n
  haveI : Finite (A →+ ZMod n) :=
    Finite.of_injective (fun φ : A →+ ZMod n => (φ : A → ZMod n)) DFunLike.coe_injective
  refine ⟨A →+ ZMod n, inferInstance, inferInstance, inferInstance, AddMonoidHom.id _, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a y y'
    rfl
  · intro y hy
    ext b
    exact hy b
  · intro y' hy'
    by_contra h
    obtain ⟨φ, hφ⟩ := exists_char_ne_zero n hn (G := A) (fun g => by
      rw [nsmul_eq_mul, hnA, zero_mul]) h
    exact hφ (hy' φ)
  · intro a Φ v hv
    by_contra hvr
    set Q := (Fin a → A) ⧸ what₂ Φ
    have hQ : ∀ q : Q, n • q = 0 := by
      intro q
      induction q using Submodule.Quotient.induction_on with
      | H w =>
        show n • (Submodule.Quotient.mk w : Q) = 0
        rw [← Nat.cast_smul_eq_nsmul A, ← Submodule.Quotient.mk_smul, hnA, zero_smul,
          Submodule.Quotient.mk_zero]
    have hmk : (Submodule.Quotient.mk v : Q) ≠ 0 := by
      rwa [Ne, Submodule.Quotient.mk_eq_zero]
    obtain ⟨ψ, hψ⟩ := exists_char_ne_zero n hn hQ hmk
    let L : (Fin a → A) →+ ZMod n := ψ.comp (what₂ Φ).mkQ.toAddMonoidHom
    let x : Fin a → (A →+ ZMod n) := fun j => L.comp (AddMonoidHom.single (fun _ => A) j)
    have key : ∀ (w : Fin a → A) (b : A), (∑ j, w j • x j) b = L (fun k => w k * b) := by
      intro w b
      have hsum (s : Finset (Fin a)) : (∑ j ∈ s, w j • x j) b = ∑ j ∈ s, (w j • x j) b := by
        classical
        induction s using Finset.induction_on with
        | empty => simp
        | @insert j s hj ih => simp [hj, ih]
      rw [hsum]
      have : (fun k => w k * b) = ∑ j, Pi.single j (w j * b) := (Finset.univ_sum_single _).symm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [this, map_sum]
      rfl
    have hx : matAct Φ x = 0 := by
      funext i
      ext b
      show (∑ j, Φ i j • x j) b = 0
      rw [key]
      have : (fun k => Φ i k * b) = b • Φ i := by
        funext k
        simp [mul_comm]
      rw [this]
      have hmem : b • Φ i ∈ what₂ Φ := Submodule.smul_mem _ b (Submodule.subset_span ⟨i, rfl⟩)
      show ψ (Submodule.Quotient.mk _) = 0
      rw [(Submodule.Quotient.mk_eq_zero _).2 hmem, map_zero]
    have h1 := congrArg (fun f : A →+ ZMod n => f 1) (hv x hx)
    rw [key] at h1
    simp only [mul_one] at h1
    exact hψ h1

end GlobalTheory.NewPrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlacesOkOfModEqOne
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem placesOk_of_modEq_one : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (q0 : ℕ) (w0 : HeightOneSpectrum (𝓞 H.E)), q0.Prime → (∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p ≡ 1 [MOD H.QS * H.q * H.d]) → (∀ k, q0 ≠ H.g k) → q0 ≠ H.pde → q0 ≠ H.pde' → OverP H q0 w0 → PlacesOk H q0 w0 ∧ 5 ≤ q0 := by
  intro R H q0 w0 hq hmod hg hp hp' hw
  have hprime : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], p.Prime := by
    intro p h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    exacts [H.g_prime 0, H.g_prime 1, H.pde_prime, H.pde'_prime, hq]
  have h4 : (4 : ℕ) ∣ H.QS * H.q * H.d := (by norm_num : 4 ∣ 16).trans H.sixteen_dvd_condN
  have h5 : ∀ p ∈ [H.g 0, H.g 1, H.pde, H.pde', q0], 5 ≤ p := by
    intro p h
    have h1 : p % 4 = 1 % 4 := (hmod p h).of_dvd h4
    have h2 := (hprime p h).two_le
    omega
  refine ⟨⟨hw, ?_, fun p h => ?_⟩, h5 q0 (by simp)⟩
  · have a1 := H.g_ne
    have a2 := H.pde_ne
    have a3 := H.pde_ne_g 0
    have a4 := H.pde_ne_g 1
    have a5 := hg 0
    have a6 := hg 1
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, not_false_eq_true,
      and_true]
    omega
  · have hs := GlobalTheory.Mem.Chr.splitsC_of_modEq_one R H p (hprime p h) (hmod p h)
    have := h5 p h
    refine ⟨hprime p h, by omega, ?_, fun P hP => (GlobalTheory.Mem.Chr.splitsC_main R H p (hprime p h) hs P hP).1⟩
    exact GlobalTheory.SplitEmbSep.not_dvd_discr_of_split (hprime p h) _
      ((GlobalTheory.Mem.Chr.ncard_places_eq_primesOver (hprime p h)).symm.trans hs)

end GlobalTheory.LamTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupReal
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem pow_mem_upperRamificationGroup_real : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e : ℕ) (v : ℝ), 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M v, σ ^ p ∈ upperRamificationGroup F ↥M (min (2 * v) (v + e)) := by
  intro F _ _ _ _ M _ _ p e v hv hOrd σ hσ

  have hc : (0 : ℤ) ≤ ⌈v⌉ := Int.ceil_nonneg hv
  have hn : ((⌈v⌉.toNat : ℕ) : ℝ) = ((⌈v⌉ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hc
  have hσn : σ ∈ upperRamificationGroup F ↥M ((⌈v⌉.toNat : ℕ) : ℝ) := by
    rw [hn, ← upperRamificationGroup_eq_ceil]
    exact hσ
  have hpow := _root_.GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_abelian_nat F M p e ⌈v⌉.toNat hOrd σ hσn

  have hvn : v ≤ ((⌈v⌉.toNat : ℕ) : ℝ) := by
    rw [hn]; exact Int.le_ceil v
  have hle : min (2 * v) (v + e) ≤ ((min (2 * ⌈v⌉.toNat) (⌈v⌉.toNat + e) : ℕ) : ℝ) := by
    push_cast
    exact min_le_min (by linarith) (by linarith)
  exact upperRamificationGroup_antitone F ↥M hle hpow

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowInvSmulLiftMemDivisibleCocyclesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primePow_inv_smul_lift_mem_divisible_cocycles : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A' : GRep ↥(GK K) ℚ_[l] LL O) (LA' : Lattice (O := O) A'.ρ) (r : ℕ) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) (c' : ↥(quotientCocycles LA' _ hI')), (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T)) ∈ divisibleCocycles LA' := by
  first | exact @GlobalTheory.DivLift.pow_inv_smul_liftQ_mem_Z1D | exact GlobalTheory.DivLift.pow_inv_smul_liftQ_mem_Z1D | (intros; apply GlobalTheory.DivLift.pow_inv_smul_liftQ_mem_Z1D <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismCoverInjectiveAndDescent
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem eq_zero_of_mem_adI_pow {l : ℕ} {R : Type} [CommRing R] (B : Obj l R) (x : B.A)
    (hx : ∀ n : ℕ, x ∈ adI B ^ n) : x = 0 := by
  refine B.complete.toIsHausdorff.haus x fun n => ?_
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  exact hx n

theorem cover_injective_and_descent : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C : Obj l R) (h : Hom B C),
    Cover h → Function.Injective h.f ∧ ∀ (D : Obj l R) (p q : Hom C D), IsPO h h p q →
      ∀ c, p.f c = q.f c → c ∈ h.f.range := by
  intro l _ R _ B C h hc

  have hinj : ∀ m : ℕ, Function.Injective (qmap h m) := fun m =>
    RingHom.FaithfullyFlat.injective (hc.ff m)

  have hlev : ∀ (m : ℕ) (b : B.A), h.f b ∈ adI C ^ m → b ∈ adI B ^ m := fun m b hb => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply hinj m
    rw [qmap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hb
  refine ⟨fun x y hxy => ?_, fun D p q hpo c hpq => ?_⟩
  · rw [← sub_eq_zero]
    refine eq_zero_of_mem_adI_pow B _ fun n => hlev n _ ?_
    rw [map_sub, hxy, sub_self]; exact Ideal.zero_mem _
  ·
    have happ : ∀ m : ℕ, ∃ b : B.A, h.f b - c ∈ adI C ^ m := fun m => by
      have hd := (_root_.GlobalTheory.BSP.ff_descent_elem_pushout _ _ _ (qmap h m) (qmap p m) (qmap q m) (hc.ff m) (hpo.po m)).2
        (Ideal.Quotient.mk _ c) (by rw [qmap_mk, qmap_mk, hpq])
      obtain ⟨b', hb'⟩ := hd
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
      refine ⟨b, ?_⟩
      rw [qmap_mk, Ideal.Quotient.eq] at hb'
      exact hb'
    choose b hb using happ
    have hcauchy : ∀ {m n : ℕ}, m ≤ n → b m ≡ b n [SMOD (adI B ^ m • ⊤ : Submodule B.A B.A)] := by
      intro m n hmn
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      refine hlev m _ ?_
      have e : h.f (b m - b n) = (h.f (b m) - c) - (h.f (b n) - c) := by rw [map_sub]; ring
      rw [e]
      exact Ideal.sub_mem _ (hb m) (Ideal.pow_le_pow_right hmn (hb n))
    obtain ⟨L, hL⟩ := B.complete.toIsPrecomplete.prec' b hcauchy
    refine ⟨L, ?_⟩
    rw [← sub_eq_zero]
    refine eq_zero_of_mem_adI_pow C _ fun n => ?_
    have h1 : b n - L ∈ adI B ^ n := by
      have := hL n
      rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    have h2 : h.f (b n - L) ∈ adI C ^ n := adI_pow_le h n h1
    have e : h.f L - c = (h.f (b n) - c) - h.f (b n - L) := by rw [map_sub]; ring
    rw [e]
    exact Ideal.sub_mem _ (hb n) h2

end GlobalTheory.BSP
end

