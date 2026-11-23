module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InstSecondCountable
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0225
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0270

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdelicWeilRepresentationModel
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.Model

theorem conjE_conjE (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply]
  simp

theorem sgA_incE (D : D7) (x : D.host.E) : sgA D (inc D x) = inc D (D.host.conj x) := by
  simp [sgA, inc, Formalism.UG.sigR, Formalism.UG.inclE]

theorem wd_at_zero (D : D7) (T : Tor D) {a d : ℕ} (G : VC D a d → ℂ) : Wd D T 0 G = G := by
  funext z
  simp [Wd, wdPh, ee, qH, U, Hf]

theorem pt_zero (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} :
    pt D (tor0 D cc δ) δ (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  simp [pt, embV, tor0]

theorem pt_nsmul (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (m : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (m • z) = m • pt D (tor0 D cc δ) δ z := by
  funext τ i j
  simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
  ring

def incM (D : D7) (N N' : ℕ) : Matrix (Fin N') (Fin N) D.host.E →+ XA D N N' :=
  (inc D).toAddMonoidHom.mapMatrix

theorem incM_apply (D : D7) (N N' : ℕ) (z : Matrix (Fin N') (Fin N) D.host.E) : incM D N N' z = z.map (inc D) := rfl

theorem exists_div (D : D7) {N N' : ℕ} {m : ℕ} (hm : 0 < m) (z : Matrix (Fin N') (Fin N) D.host.E) (a : XA D N N')
    (h : z.map (inc D) = m • a) : ∃ z' : Matrix (Fin N') (Fin N) D.host.E, z = m • z' ∧ z'.map (inc D) = a := by
  have hm' : (m : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  refine ⟨Matrix.of fun i j => (m : D.host.E)⁻¹ * z i j, ?_, ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    field_simp
  · ext i j
    have h1 := congrFun (congrFun h i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, nsmul_eq_mul] at h1
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, h1]
    rw [← mul_assoc, ← map_natCast (inc D) m, ← map_mul, inv_mul_cancel₀ hm', map_one, one_mul]

theorem mul_nsmul_left {X : Type} [AddCommGroup X] (f : X → ℂ) (h0 : f 0 = 1) (h : ∀ x y, f (x + y) = f x * f y)
    (m : ℕ) (x : X) : f (m • x) = f x ^ m := by
  induction m with
  | zero => simp [h0]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

theorem exists_isModel (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) (N N' : ℕ) :
    ∃ w γ WA, GlobalTheory.FinWeil.IsModel D cc δ N N' w γ WA := by
  obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.FinWeil.AdelicChar.exists_psi D hD cc δ hc
  obtain ⟨w, hw, hwd⟩ := _root_.GlobalTheory.FinWeil.WdCocycle.wd_cocycle D hD cc δ hc
  obtain ⟨hinv, halt, hadj, hl, hr⟩ := _root_.GlobalTheory.FinWeil.gamA_alg D hD cc δ hc ψ hψ N N'
  have hsd := GlobalTheory.T.completedStandardAdelicLattice_selfDual D hD cc δ hc ψ hψ N N'
  obtain ⟨hrat, -, hdense, hden, -, -⟩ := _root_.GlobalTheory.CompletedLattice.completed_lattice D hD cc δ hc N N'
  have htt := _root_.GlobalTheory.FinWeil.RatTransl.wd_mem_TT D hD cc δ hc N N'
  let W₀ : Matrix (Fin N') (Fin N) D.host.E → TTs D (tor0 D cc δ) N N' →ₗ[ℂ] TTs D (tor0 D cc δ) N N' := fun z =>
    { toFun := fun F => ⟨Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F, htt z F F.2⟩
      map_add' := fun F G => Subtype.ext (wd_add _ _ _)
      map_smul' := fun c F => Subtype.ext (wd_smul _ _ _) }
  have hz1 : ∀ y : XA D N N', gamA ψ 0 y = 1 := fun y => by simp [gamA, hψ.2.1]
  have hz2 : ∀ y : XA D N N', gamA ψ y 0 = 1 := fun y => by simp [gamA, hψ.2.1]
  have hn1 : ∀ (m : ℕ) (x y : XA D N N'), gamA ψ (m • x) y = gamA ψ x y ^ m := fun m x y =>
    mul_nsmul_left (fun x => gamA ψ x y) (hz1 y) (fun a b => hl a b y) m x
  have hn2 : ∀ (m : ℕ) (x y : XA D N N'), gamA ψ x (m • y) = gamA ψ x y ^ m := fun m x y =>
    mul_nsmul_left (fun y => gamA ψ x y) (hz2 x) (fun a b => hr x a b) m y
  have hiso : ∀ a ∈ latA D cc N N', ∀ b ∈ latA D cc N N', gamA ψ (w • a) b = 1 := fun a ha b hb =>
    (hsd _).1 ((latA D cc N N').smul_mem w ha) b hb
  obtain ⟨WA, h1, h2, h3⟩ := GlobalTheory.FinWeil.exists_extension_of_dense (incM D N N') (latA D cc N N').toAddSubgroup
    (fun x y => gamA ψ (w • x) y) W₀
    (fun x y z => by simp only [smul_add, hl]) (fun x y z => hr _ _ _) hiso
    (fun x => by
      obtain ⟨m, hm, hx⟩ := hden x
      refine ⟨m, hm, fun a ha => ⟨?_, ?_⟩⟩
      · have := hiso _ hx a ha
        rw [smul_comm, hn1] at this
        simp only [hn2, this]
      · have := hiso a ha _ hx
        rw [hn2] at this
        show gamA ψ (w • m • a) x = 1
        rw [smul_comm, hn1, this])
    (fun x y v => by
      apply Subtype.ext
      have h := (hwd N N' x y).2.2 v
      have h' : gamA ψ (w • incM D N N' x) (incM D N N' y) =
          psi0 D cc δ (∑ i, ∑ j, (w : D.host.E) * x i j * D.host.conj (y i j)) := by
        rw [← hψ.2.2.1]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [gamA, incM_apply, Matrix.smul_apply, Matrix.map_apply, smul_AE, sgA_incE, map_sum, map_mul]
      show Wd D _ _ (Wd D _ _ _) = gamA ψ (w • incM D N N' x) (incM D N N' y) • Wd D _ _ _
      rw [h', h])
    (fun x m hm => hdense x m hm)
    (fun v => by
      obtain ⟨m, hm, hv⟩ := v.2.2
      refine ⟨m, hm, ?_⟩
      rintro z ⟨a, ha, hz⟩
      obtain ⟨z', rfl, rfl⟩ := exists_div D hm z a hz
      apply Subtype.ext
      show Wd D _ (pt D _ δ (m • z')) _ = _
      rw [pt_nsmul]
      exact hv _ ((hrat z').1 ha))
  refine ⟨w, gamA ψ, WA, ⟨fun r => ?_, hw, hl, hr, halt, hadj, fun v => ?_, h2⟩, hsd, hinv, fun z F => ?_, h3⟩
  · apply RingOfIntegers.ext
    rw [coe_sgO, coe_sgO, conjE_conjE]
  · have := h1 0
    rw [map_zero] at this
    rw [this]
    apply Subtype.ext
    show Wd D _ (pt D _ δ 0) _ = _
    rw [pt_zero, wd_at_zero]
  · rw [← incM_apply, h1]
    rfl

end GlobalTheory.FinWeil.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalStableLeISupEigen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

theorem form_aeval_of_left_eigen {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V)
    (φ : V →ₗ[ℂ] ℂ) (c : ℂ) (h : ∀ v, φ (T v) = c * φ v) (f : Polynomial ℂ) (v : V) :
    φ (Polynomial.aeval T f v) = f.eval c * φ v := by
  have hpow : ∀ (n : ℕ) (v : V), φ ((T ^ n) v) = c ^ n * φ v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, ih, h]; ring
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, map_smul, hpow, smul_eq_mul, mul_assoc]

theorem finiteDimensional_stable_le_iSup_eigen :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (U : H →L[ℂ] H), (∀ v, ‖U v‖ = ‖v‖) → ∀ (E : ℕ → Submodule ℂ H) (lam : ℕ → ℂ), Function.Injective lam → (∀ m, FiniteDimensional ℂ (E m)) → (∀ m, ∀ e ∈ E m, U e = lam m • e) → Dense ((⨆ m, E m : Submodule ℂ H) : Set H) → ∀ (W : Submodule ℂ H), FiniteDimensional ℂ W → (∀ w ∈ W, U w ∈ W) → W ≤ ⨆ m, E m := by
  intro H _ _ _ U hU E lam hinj hfin heig hdense W hW hst
  classical
  have hinner : ∀ a b : H, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ := fun a b =>
    (⟨(U : H →ₗ[ℂ] H), hU⟩ : H →ₗᵢ[ℂ] H).inner_map_map a b
  have hleft : ∀ m, ∀ e ∈ E m, ∀ y, ⟪e, U y⟫_ℂ = lam m * ⟪e, y⟫_ℂ := by
    intro m e he y
    by_cases h0 : e = 0
    · simp [h0]
    have h1 : ‖lam m‖ = 1 := by
      have := hU e
      rw [heig m e he, norm_smul] at this
      have hne : ‖e‖ ≠ 0 := norm_ne_zero_iff.mpr h0
      exact mul_right_cancel₀ hne (by rw [this, one_mul])
    have h2 : lam m * (starRingEnd ℂ) (lam m) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]; simp
    have h3 := hinner e y
    rw [heig m e he, inner_smul_left] at h3
    rw [← h3, ← mul_assoc, h2, one_mul]
  let T : Module.End ℂ W := (U : H →ₗ[ℂ] H).restrict hst
  let f : Polynomial ℂ := LinearMap.charpoly T
  have hf0 : f ≠ 0 := (LinearMap.charpoly_monic T).ne_zero
  have hfT : Polynomial.aeval T f = 0 := LinearMap.aeval_self_charpoly T
  have hsfin : (lam ⁻¹' {z | f.IsRoot z}).Finite :=
    (Polynomial.finite_setOf_isRoot hf0).preimage hinj.injOn
  let s : Finset ℕ := hsfin.toFinset
  have hout : ∀ m, m ∉ s → ∀ e ∈ E m, ∀ y ∈ W, ⟪e, y⟫_ℂ = 0 := by
    intro m hm e he y hy
    have hne : f.eval (lam m) ≠ 0 := by
      intro h
      exact hm (hsfin.mem_toFinset.mpr h)
    have := form_aeval_of_left_eigen T (((innerₛₗ ℂ e : H →ₗ[ℂ] ℂ)).comp W.subtype) (lam m)
      (fun v => hleft m e he v) f ⟨y, hy⟩
    rw [hfT] at this
    simp only [LinearMap.zero_apply, map_zero] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hne
  let F : Submodule ℂ H := ⨆ m ∈ s, E m
  haveI hF : FiniteDimensional ℂ F := by
    have : F = s.sup E := by simp [F, Finset.sup_eq_iSup]
    rw [this]; infer_instance
  have hFle : F ≤ ⨆ m, E m := iSup₂_le fun m _ => le_iSup E m
  have hForth : ∀ m, m ∉ s → F ≤ (E m)ᗮ := by
    intro m hm
    refine iSup₂_le fun k hk x hx => ?_
    rw [Submodule.mem_orthogonal]
    intro e he
    have h1 := hleft m e he x
    rw [heig k x hx, inner_smul_right] at h1
    have hne : lam k - lam m ≠ 0 := by
      intro h
      have := hinj (sub_eq_zero.mp h)
      exact hm (this ▸ hk)
    have : (lam k - lam m) * ⟪e, x⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hne
  intro y hy
  have hz : y - F.starProjection y ∈ (⨆ m, E m)ᗮ := by
    rw [← Submodule.iInf_orthogonal, Submodule.mem_iInf]
    intro m
    by_cases hm : m ∈ s
    · have hle : E m ≤ F := le_iSup₂_of_le (f := fun m (_ : m ∈ s) => E m) m hm le_rfl
      exact Submodule.orthogonal_le hle (Submodule.sub_starProjection_mem_orthogonal y)
    · refine Submodule.sub_mem _ ?_ (hForth m hm (F.starProjection_apply_mem y))
      rw [Submodule.mem_orthogonal]
      intro e he
      exact hout m hm e he y hy
  have hz0 : y - F.starProjection y = 0 := by
    have htop : (⨆ m, E m : Submodule ℂ H).topologicalClosure = ⊤ :=
      Submodule.dense_iff_topologicalClosure_eq_top.mp hdense
    rw [Submodule.topologicalClosure_eq_top_iff] at htop
    rw [htop] at hz
    exact (Submodule.mem_bot ℂ).mp hz
  rw [sub_eq_zero.mp hz0]
  exact hFle (F.starProjection_apply_mem y)

end GlobalTheory.HolDS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockIntertwinerCommutesUnitaryAndExtends
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockExtGroup

theorem pi_comm {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
    {T2 : GrpData r s} (F : FockData T0 T1 T2) (g : T1.G) (h : T2.G) (x : F.H) :
    F.π (g, 1) (F.π (1, h) x) = F.π (1, h) (F.π (g, 1) x) := by
  rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul]
  simp

theorem comm_and_extend : ∀ (p q n : ℕ) (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2), 1 ≤ n → ∀ (D : DSRep T1) (τ : URep T2) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H) (I : D.HK.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (v₀ : M.V), IrrU τ → IsHCMod τ M j → v₀ ≠ 0 → IsGIntw F D.HK M I → (∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v₀))) ∧ ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y)) → (∀ (h : T2.G) (x : D.HK.V) (v v' : M.V), j v' = τ.π h (j v) → F.π (1, h) (F.ι (I (x ⊗ₜ v))) = F.ι (I (x ⊗ₜ v'))) ∧ ∀ v : M.V, ∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v))) ∧ ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y) := by
  intro p q n T0 T1 T2 F hn D τ M j I v₀ hτ hM hv₀ hI hJ
  obtain ⟨hfin, -, -, hirr⟩ := GlobalTheory.CompactCoverIrr.hcMod_finite_irr n hn T2 τ M j hτ hM ⟨v₀, 0, hv₀⟩
  obtain ⟨hF, -, hder⟩ := GlobalTheory.FockEmbExp.fock_derived p q n 0 T0 T1 T2 F
  let σ : URep T2 :=
    { H := F.H
      π := F.π.comp (MonoidHom.inr _ _)
      isom := fun _ x => F.isom _ x
      cont := fun x => (F.cont x).comp (hF.comp (continuous_const.prodMk continuous_id)) }
  have h1 : ∀ (h : T2.G) (x : D.HK.V) (v v' : M.V), j v' = τ.π h (j v) →
      F.π (1, h) (F.ι (I (x ⊗ₜ v))) = F.ι (I (x ⊗ₜ v')) := by
    intro h x v v' hv
    have hK : h ∈ T2.Kset := by
      rintro (a | a) (b | b) hab
      · exact (hab trivial).elim
      · exact b.elim0
      · exact a.elim0
      · exact a.elim0
    let j₂ : M.V →ₗ[ℂ] σ.H := F.ι ∘ₗ I ∘ₗ TensorProduct.mk ℂ D.HK.V M.V x
    obtain ⟨w, hw1, hw2⟩ := GlobalTheory.RealPar.pair_kEquivariant_of_lie n 0 T2
      (GlobalTheory.CoverKGen.kset_gen n 0 (by omega) T2) τ σ M.V (fun Y => M.act Y) j j₂
      (fun Y hY _ w => ⟨hM.2.2 Y hY w, by
        have h2 := hder Y hY (I (x ⊗ₜ w))
        have h3 : fockAct2 p q n 0 Y (I (x ⊗ₜ w)) = I (x ⊗ₜ M.act Y w) := hI.2 Y x w
        rw [h3] at h2
        exact h2⟩) h hK v
    obtain rfl : v' = w := hM.1 (hv.trans hw1)
    exact hw2
  refine ⟨h1, ?_⟩
  let N : Submodule ℂ M.V :=
    { carrier := {v | ∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v))) ∧
        ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y)}
      add_mem' := by
        rintro a b ⟨J, hJ1, hJ2⟩ ⟨J', hJ1', hJ2'⟩
        exact ⟨J + J', fun x => by simp [hJ1, hJ1', TensorProduct.tmul_add],
          fun g y => by simp [hJ2, hJ2']⟩
      zero_mem' := ⟨0, fun x => by simp, fun g y => by simp⟩
      smul_mem' := by
        rintro c a ⟨J, hJ1, hJ2⟩
        exact ⟨c • J, fun x => by simp [hJ1, TensorProduct.tmul_smul],
          fun g y => by simp [hJ2]⟩ }
  rcases hirr N (by
    rintro h v ⟨J, hJ1, hJ2⟩ v' hv
    refine ⟨F.π (1, h) ∘L J, fun x => ?_, fun g y => ?_⟩
    · rw [ContinuousLinearMap.comp_apply, hJ1, h1 h x v v' hv]
    · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, pi_comm, hJ2]) with h | h
  · have : v₀ ∈ N := hJ
    rw [h] at this
    exact (hv₀ this).elim
  · intro v
    have : v ∈ N := h ▸ Submodule.mem_top
    exact this

end GlobalTheory.FockExtGroup
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasDerivAtPhiCol
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.HolDS.DerPt

section Gen

variable {n : Type} [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry (X : Matrix n n ℂ) (i j : n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X)) i j) (X i j) 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix n n ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_det_of_one (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A 0 = 1)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) A'.trace 0 := by
  first
  | exact @_root_.GlobalTheory.DetDerivativeAtOne.hasDerivAt_det_of_one
  | exact _root_.GlobalTheory.DetDerivativeAtOne.hasDerivAt_det_of_one
  | (apply _root_.GlobalTheory.DetDerivativeAtOne.hasDerivAt_det_of_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.DetDerivativeAtOne.hasDerivAt_det_of_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DetDerivativeAtOne.hasDerivAt_det_of_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DetDerivativeAtOne.hasDerivAt_det_of_one ..)

end Gen

variable {p q : ℕ}

end GlobalTheory.HolDS.DerPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralKerSumGraphEq
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.Graph

theorem integral_kerSum_graph_eq : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∀ (B : V →ₗ[ℂ] V), (∀ x, B x - a (B x) = x) → ∀ (Λ Λ' : AddSubgroup V) [DiscreteTopology Λ], Λ' ≤ Λ → (∀ y ∈ Λ', a y ∈ Λ) → ∀ α : V → ℂ, IsSemichar H Λ α → (∀ y ∈ Λ', α (a y) = α y) → ∀ Fd : Set V, IsAddFundamentalDomain Λ' Fd μ → ∀ (M : Type) [Fintype M] (s : M → V), (∀ m, s m ∈ Λ) → (∀ x ∈ Λ, ∃! p : M × Λ', x = s p.1 - ((p.2 : V) - a p.2)) → ∃ κ : ℝ, 0 < κ ∧ ∫ z in Fd, kerSum H Λ α z (a z) * cexp (-(π : ℂ) * H z z) ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * ∑ m, α (s m) * cexp (-((π : ℂ) * I) * ((H (B (s m)) (s m)).im : ℂ)) := by
  intro V _ _ _ _ _ μ _ H hH a ha hdet B hB1 Λ Λ' _ hle haΛ α hα hαa Fd hFd M _ s hs huniq
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable Λ' := (AddSubgroup.inclusion_injective hle).countable
  obtain ⟨κ, hκ, hg⟩ := integral_gaussian_unitary_pos V μ H hH a ha hdet
  refine ⟨κ, hκ, ?_⟩
  have hint : ∀ x, Integrable (term H a α x) μ := fun x => by
    have : term H a α x = _ := funext fun z => term_eq H a ha α x (B x) z (hB1 x)
    rw [this]
    exact (hg (B x) _).1.const_mul _
  have hval : ∀ x, ∫ z, term H a α x z ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) *
      (α x * cexp (-((π : ℂ) * I) * ((H (B x) x).im : ℂ))) := fun x => by
    simp only [fun z => term_eq H a ha α x (B x) z (hB1 x)]
    rw [integral_const_mul, (hg (B x) _).2, ← value_eq H hH a ha x (B x) (hB1 x)]
    ring
  let f : M × Λ' → Λ := fun p => ⟨s p.1 - ((p.2 : V) - a p.2),
    Λ.sub_mem (hs _) (Λ.sub_mem (hle p.2.2) (haΛ _ p.2.2))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      exact (huniq _ (f p).2).unique rfl (congrArg Subtype.val hpq)
    · intro x
      obtain ⟨p, hp, -⟩ := huniq x x.2
      exact ⟨p, Subtype.ext hp.symm⟩
  have hsum : ∀ z, kerSum H Λ α z (a z) * cexp (-(π : ℂ) * H z z) =
      ∑ m, ∑' y : Λ', term H a α (s m) (z + y) := fun z => by
    have h1 : Summable (fun x : Λ => term H a α x z) :=
      ((GlobalTheory.UnitaryTheta.KerSum.kerSum_spec V H hH Λ α hα).1 (a z) z).mul_right _
    have h2 := (Equiv.ofBijective f hf).summable_iff.2 h1
    rw [kerSum, ← tsum_mul_right]
    change ∑' x : Λ, term H a α x z = _
    rw [← (Equiv.ofBijective f hf).tsum_eq]
    refine (h2.tsum_prod).trans ?_
    rw [tsum_fintype]
    refine Finset.sum_congr rfl fun m _ => tsum_congr fun y => ?_
    exact term_shift H hH a ha Λ α hα (s m) y z (hs m) (hle y.2) (haΛ _ y.2) (hαa _ y.2)
  have hu := fun m => GlobalTheory.integral_unfold_fundamentalDomain V μ Λ' Fd hFd _ (hint (s m))
  simp only [hsum]
  rw [integral_finsetSum _ (fun m _ => (hu m).1)]
  simp only [fun m => (hu m).2, hval]
  rw [← Finset.mul_sum]

end GlobalTheory.UnitaryTheta.Graph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemOfIsometryEigenOfDenseISup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory

theorem mem_of_isometry_eigen_of_dense_iSup :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (U : H →L[ℂ] H), (∀ v, ‖U v‖ = ‖v‖) → ∀ (E : ℕ → Submodule ℂ H) (lam : ℕ → ℂ), Function.Injective lam → (∀ m, FiniteDimensional ℂ (E m)) → (∀ m, ∀ e ∈ E m, U e = lam m • e) → Dense ((⨆ m, E m : Submodule ℂ H) : Set H) → ∀ (m : ℕ) (y : H), U y = lam m • y → y ∈ E m := by
  intro H _ _ _ U hU E lam hlam hfin hE hd m y hy
  let V : H →ₗᵢ[ℂ] H := ⟨U.toLinearMap, hU⟩
  have hin : ∀ a b : H, ⟪U a, U b⟫_ℂ = ⟪a, b⟫_ℂ := fun a b => V.inner_map_map a b
  haveI := hfin m
  obtain ⟨p, hp, q, hq, rfl⟩ := (E m).exists_add_mem_mem_orthogonal y
  have hUq : U q = lam m • q := by
    rw [map_add (f := _), hE m p hp, smul_add] at hy
    exact add_left_cancel hy
  have horth : ∀ m', ∀ e ∈ E m', ⟪e, q⟫_ℂ = 0 := by
    intro m' e he
    by_cases hm : m' = m
    · subst hm
      exact (Submodule.mem_orthogonal _ _).1 hq e he
    by_cases he0 : e = 0
    · simp [he0]
    have h1 := hin e q
    have h2 := hin e e
    rw [hE m' e he, hUq, inner_smul_left, inner_smul_right] at h1
    rw [hE m' e he, inner_smul_left, inner_smul_right] at h2
    have hee : ⟪e, e⟫_ℂ ≠ 0 := by simpa using he0
    have h3 : (starRingEnd ℂ) (lam m') * lam m' = 1 := by
      apply mul_right_cancel₀ hee
      rw [one_mul, mul_assoc, h2]
    by_contra hne
    have h4 : (starRingEnd ℂ) (lam m') * lam m = 1 := by
      apply mul_right_cancel₀ hne
      rw [one_mul, mul_assoc, h1]
    have h5 : (starRingEnd ℂ) (lam m') ≠ 0 := left_ne_zero_of_mul_eq_one h3
    exact hm (hlam (mul_left_cancel₀ h5 (h3.trans h4.symm)))
  have hle : (⨆ m, E m : Submodule ℂ H) ≤ (ℂ ∙ q)ᗮ := by
    refine iSup_le fun m' e he => ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact horth m' e he
  have hq0 : q = 0 := by
    have hcl : closure ((⨆ m, E m : Submodule ℂ H) : Set H) ⊆ ((ℂ ∙ q)ᗮ : Submodule ℂ H) :=
      closure_minimal hle (Submodule.isClosed_orthogonal _)
    have := hcl (hd q)
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_left] at this
    simpa using this
  simpa [hq0] using hp

end GlobalTheory
end

