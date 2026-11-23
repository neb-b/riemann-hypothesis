module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0224
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdeleClassFiniteness.LatticeIdealNonzero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsModerateGrowthSmoothFrechetRep
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCcrOperatorsThetaFunctions
section
noncomputable section

namespace GlobalTheory.Mem.Lift.ThOps

theorem exists_restrict {Θ M : Type} [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup M] [Module ℂ M] (j : Θ →ₗ[ℂ] M)
    (hj : Function.Injective j) (A : Module.End ℂ M) (hA : ∀ f, ∃ g, j g = A (j f)) :
    ∃ a : Module.End ℂ Θ, ∀ f, j (a f) = A (j f) := by
  choose a ha using hA
  exact ⟨{ toFun := a
           map_add' := fun f g => hj (by simp only [map_add (f := _), ha])
           map_smul' := fun c f => hj (by simp only [map_smul, ha, RingHom.id_apply]) }, ha⟩

theorem isCCR_restrict {Θ M κ : Type} [DecidableEq κ] [AddCommGroup Θ] [Module ℂ Θ] [AddCommGroup M] [Module ℂ M]
    (j : Θ →ₗ[ℂ] M) (hj : Function.Injective j) {x d : κ → Module.End ℂ Θ} {x₀ d₀ : κ → Module.End ℂ M}
    (hx : ∀ k f, j (x k f) = x₀ k (j f)) (hd : ∀ k f, j (d k f) = d₀ k (j f)) (h : GlobalTheory.Mem.Lift.IsCCR x₀ d₀) :
    GlobalTheory.Mem.Lift.IsCCR x d := by
  refine ⟨fun k l => LinearMap.ext fun f => hj ?_, fun k l => LinearMap.ext fun f => hj ?_,
    fun k l => LinearMap.ext fun f => hj ?_⟩
  · simpa only [Module.End.mul_apply, hx] using LinearMap.congr_fun (h.1 k l) (j f)
  · simpa only [Module.End.mul_apply, hd] using LinearMap.congr_fun (h.2.1 k l) (j f)
  · have := LinearMap.congr_fun (h.2.2 k l) (j f)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, hx, hd] at this ⊢
    rw [this]
    split_ifs <;> simp


open Matrix GlobalTheory.RealWeil in
theorem exists_ops {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (hd : H.det ≠ 0)
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] (ρ : (ι → ℂ) → B →L[ℂ] B)
    (hρ : IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ) {Θ : Type} [AddCommGroup Θ] [Module ℂ Θ] (J : Θ →ₗ[ℂ] B)
    (hJ : Function.Injective J) (hs : ∀ f, Sm ρ (J f)) (hk : ∀ v f, ∃ g, J g = dH ρ v (J f)) :
    ∃ x d : ι → Module.End ℂ Θ, IsCCR x d ∧
      ∀ (X : Matrix ι ι ℂ) (f : Θ), J ((∑ k, ∑ l, X k l • (x k * d l)) f) = nOp ρ H X (J f) := by
  obtain ⟨x₀, d₀, hx₀, hd₀, hc⟩ := exists_isCCR_xOp_dOp ι H hH hd B ρ hρ
  let j : Θ →ₗ[ℂ] smS ρ := J.codRestrict _ hs
  have hj : Function.Injective j := fun f g e => hJ (congrArg Subtype.val e)
  have h1 : ∀ k, ∃ a : Module.End ℂ Θ, ∀ f, j (a f) = x₀ k (j f) := fun k => exists_restrict j hj _ fun f => by
    obtain ⟨g₁, e₁⟩ := hk (Pi.single k 1) f
    obtain ⟨g₂, e₂⟩ := hk (Complex.I • Pi.single k 1) f
    refine ⟨g₁ - Complex.I • g₂, Subtype.ext ?_⟩
    rw [hx₀]
    change J _ = xOp ρ k (J f)
    rw [xOp, map_sub, map_smul, e₁, e₂]
  have h2 : ∀ k, ∃ a : Module.End ℂ Θ, ∀ f, j (a f) = d₀ k (j f) := fun k => exists_restrict j hj _ fun f => by
    obtain ⟨g₁, e₁⟩ := hk (H⁻¹ *ᵥ Pi.single k 1) f
    obtain ⟨g₂, e₂⟩ := hk (Complex.I • H⁻¹ *ᵥ Pi.single k 1) f
    refine ⟨(-(1 / (4 * Real.pi)) : ℂ) • (g₁ + Complex.I • g₂), Subtype.ext ?_⟩
    rw [hd₀]
    change J _ = dOp ρ H k (J f)
    rw [dOp, map_smul, map_add (f := _), map_smul, e₁, e₂]
  choose x hx using h1
  choose d hd' using h2
  refine ⟨x, d, isCCR_restrict j hj hx hd' hc, fun X f => ?_⟩
  have ex : ∀ k f, J (x k f) = xOp ρ k (J f) := fun k f => (congrArg Subtype.val (hx k f)).trans (hx₀ k _)
  have ed : ∀ k f, J (d k f) = dOp ρ H k (J f) := fun k f => (congrArg Subtype.val (hd' k f)).trans (hd₀ k _)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [nOp, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, map_sum, map_smul, ex, ed]

end GlobalTheory.Mem.Lift.ThOps

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical


open GlobalTheory.RealWeil in
theorem GlobalTheory.Mem.Lift.exists_isCCR_theta : ∀ (D : D7) (θ : InfF D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D), ∃ x d : GlobalTheory.RealWeil.Ix S T → Module.End ℂ (GlobalTheory.RealWeil.thetaSub ψ S T), IsCCR x d ∧ ∀ (X : Matrix (GlobalTheory.RealWeil.Ix S T) (GlobalTheory.RealWeil.Ix S T) ℂ) (f : GlobalTheory.RealWeil.thetaSub ψ S T) (F : GlobalTheory.RealWeil.BB ψ S T), (F.1 : WO S T → ℂ) = f.1 → ((∑ k, ∑ l, X k l • (x k * d l)) f).1 = (nOp (GlobalTheory.RealWeil.rhoV hψ σ S T) (GlobalTheory.RealWeil.HM S T) X F).1 := by
  intro D θ σ h ψ hψ S T
  let J : thetaSub ψ S T →ₗ[ℂ] BB ψ S T :=
    { toFun := fun f => toB hψ f.1 f.2
      map_add' := fun f g => QB_ext fun x => rfl
      map_smul' := fun a f => QB_ext fun x => rfl }
  have hc : ∀ f, ((J f).1 : WO S T → ℂ) = f.1 := fun f => coe_toB hψ f.1 f.2
  have hJ : Function.Injective J := fun f g e => Subtype.ext (by rw [← hc, ← hc, e])
  have ht : ∀ f, IsThetaFunO ψ S T (J f).1 := fun f => (hc f).symm ▸ f.2
  have hs : ∀ f, GlobalTheory.RealWeil.Sm (rhoV hψ σ S T) (J f) := fun f => sm_of_theta h hψ _ (ht f)
  have hk : ∀ v f, ∃ g, J g = dH (rhoV hψ σ S T) v (J f) := by
    intro v f
    obtain ⟨F', hF', hd⟩ := exists_deriv h hψ (J f) (ht f) v
    refine ⟨⟨F'.1, hF'⟩, QB_ext fun w => ?_⟩
    rw [hc]
    exact (hd w).unique (((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v (hs f)))
  obtain ⟨x, d, hxd, hn⟩ := ThOps.exists_ops (HM S T) HM_herm HM_det (rhoV hψ σ S T) (isHeis_rhoB h hψ) J hJ hs hk
  refine ⟨x, d, hxd, fun X f F hF => ?_⟩
  have e : F = J f := QB_ext fun w => by rw [hF, hc]
  rw [e, ← hn, hc]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharpoly
section
noncomputable section
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
namespace GlobalTheory.MemN.SerInhab

theorem trace_mulLeft {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ _ (LinearMap.mulLeft ℂ a) = (Fintype.card G : ℂ) * a.coeff 1 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
  have : ∀ x : G, (LinearMap.toMatrix (MonoidAlgebra.basis G ℂ) (MonoidAlgebra.basis G ℂ)
      (LinearMap.mulLeft ℂ a)).diag x = a.coeff 1 := by
    intro x
    simp [Matrix.diag, LinearMap.toMatrix_apply, MonoidAlgebra.basis]
  rw [Finset.sum_congr rfl fun x _ => this x]
  simp

theorem coeff_mem {G : Type} [Group G] [Finite G] {N : ℕ} (hN : 0 < N) (hG : Nat.card G ∣ N)
    (e : MonoidAlgebra ℂ G) (he : e * e = e) (hc : ∀ a, e * a = a * e) (x : G) :
    e.coeff x ∈ IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} := by
  classical
  haveI := Fintype.ofFinite G
  set K := IntermediateField.adjoin ℚ {Complex.exp (2 * Real.pi * Complex.I / (N : ℕ))} with hK
  set s : MonoidAlgebra ℂ G := MonoidAlgebra.single x⁻¹ 1 with hs
  have hsN : s ^ N = 1 := by
    rw [hs, MonoidAlgebra.single_pow, one_pow,
      orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard x⁻¹).trans hG)]
    rfl
  have hpow : (e * s) ^ (N + 1) = e * s := by
    rw [Commute.mul_pow (hc s), IsIdempotentElem.pow_succ_eq N he, pow_succ, hsN, one_mul]
  have hζ := Complex.isPrimitiveRoot_exp N hN.ne'
  have hζK : Complex.exp (2 * Real.pi * Complex.I / (N : ℕ)) ∈ K :=
    IntermediateField.mem_adjoin_simple_self _ _
  have htr : LinearMap.trace ℂ _ (LinearMap.mulLeft ℂ (e * s)) ∈ K := by
    rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
    refine multiset_sum_mem _ fun μ hμ => ?_
    have hroot := isRoot_of_mem_roots hμ
    have h1 := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mpr hroot
    obtain ⟨v, hv⟩ := h1.exists_hasEigenvector
    have h2 := hv.pow_apply (N + 1)
    rw [LinearMap.pow_mulLeft, hpow, hv.apply_eq_smul] at h2
    have h3 : μ = μ ^ (N + 1) := smul_left_injective ℂ hv.2 h2
    by_cases h0 : μ = 0
    · rw [h0]; exact zero_mem _
    · have h4 : μ ^ N = 1 := by
        rw [pow_succ] at h3
        exact mul_right_cancel₀ h0 (by rw [one_mul]; exact h3.symm)
      haveI : NeZero N := ⟨hN.ne'⟩
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h4
      rw [← hi]; exact pow_mem hζK i
  rw [trace_mulLeft] at htr
  have h5 : (e * s).coeff 1 = e.coeff x := by simp [hs]
  rw [h5] at htr
  have h6 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have := mul_mem (inv_mem (natCast_mem K (Fintype.card G))) htr
  rwa [← mul_assoc, inv_mul_cancel₀ h6, one_mul] at this

theorem exists_primitive (G : Type) [Group G] [Finite G] :
    ∃ (n : ℕ) (p : Fin n → MonoidAlgebra ℂ G), (∀ i, p i * p i = p i) ∧ (∀ i a, p i * a = a * p i) ∧
      (∀ i j, i ≠ j → p i * p j = 0) ∧ (∀ i, p i ≠ 0) ∧ ∑ i, p i = 1 ∧
      ∀ z, (∀ a, z * a = a * z) → z ∈ Submodule.span ℂ (Set.range p) := by
  classical
  have : NeZero (Nat.card G : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨n, d, hd, ⟨φ⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ (MonoidAlgebra ℂ G)
  refine ⟨n, fun i => φ.symm (Pi.single i 1), fun i => ?_, fun i a => ?_, fun i j hij => ?_, fun i => ?_, ?_,
    fun z hz => ?_⟩
  · rw [← map_mul, ← Pi.single_mul, one_mul]
  · apply φ.injective
    simp only [map_mul, AlgEquiv.apply_symm_apply]
    funext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  · rw [← map_mul, map_eq_zero_iff _ φ.symm.injective]
    funext k
    by_cases h : k = i
    · subst h; simp [hij]
    · simp [h]
  · rw [ne_eq, map_eq_zero_iff _ φ.symm.injective]
    intro h
    haveI := hd i
    have h' := congrFun h i
    rw [Pi.single_eq_same] at h'
    exact one_ne_zero h'
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [← map_sum, Finset.univ_sum_single, ← map_one φ.symm]; rfl
  · have hc : ∀ y, φ z * y = y * φ z := by
      intro y
      obtain ⟨x, rfl⟩ := φ.surjective y
      rw [← map_mul, ← map_mul, hz]
    have h1 : ∀ i, ∃ c : ℂ, φ z i = c • 1 := by
      intro i
      have hci : ∀ M : Matrix (Fin (d i)) (Fin (d i)) ℂ, φ z i * M = M * φ z i := by
        intro M
        have := congrFun (hc (Pi.single i M)) i
        simpa using this
      obtain ⟨c, hcc⟩ := Matrix.mem_range_scalar_of_commute_single (M := φ z i) (fun a b _ => (hci _).symm)
      exact ⟨c, by rw [← hcc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩
    choose c hc' using h1
    have h2 : z = ∑ i, c i • φ.symm (Pi.single i 1) := by
      apply φ.injective
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, AlgEquiv.apply_symm_apply]
      funext j
      rw [hc', Finset.sum_apply, Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb.symm]
      · simp
    rw [h2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem exists_family {G S : Type} [Group G] [Finite G] (c : G → S) (hc : Function.Surjective c)
    (hconj : ∀ x y, c (x * y) = c (y * x)) [Fintype S] :
    ∃ (q : S → MonoidAlgebra ℂ G), (∀ i, q i * q i = q i) ∧ (∀ i a, q i * a = a * q i) ∧
      (∀ i j, i ≠ j → q i * q j = 0) ∧ (∀ i, q i ≠ 0) ∧ ∑ i, q i = 1 := by
  classical
  obtain ⟨n, p, h1, h2, h3, h4, h5, h6⟩ := exists_primitive G
  let z : S → MonoidAlgebra ℂ G := fun s =>
    .ofCoeff (Finsupp.equivFunOnFinite.symm fun x => if c x = s then 1 else 0)
  have hz : ∀ s x, (z s).coeff x = if c x = s then 1 else 0 := fun s x => rfl
  have hzc : ∀ s a, z s * a = a * z s := by
    intro s a
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [mul_add, add_mul, ha, hb]
    | single x r =>
      ext y
      simp [hz, hconj y, mul_comm]
  have hli : LinearIndependent ℂ z := by
    rw [Fintype.linearIndependent_iff]
    intro a ha s
    obtain ⟨x, rfl⟩ := hc s
    have := congrArg (fun w : MonoidAlgebra ℂ G => w.coeff x) ha
    simpa [hz, Finsupp.finsetSum_apply] using this
  have hcard : Fintype.card S ≤ Fintype.card (Fin n) := by
    have := linearIndependent_le_span_aux' z hli (Set.range p) (by rintro _ ⟨s, rfl⟩; exact h6 _ (hzc s))
    exact this.trans (Fintype.card_range_le p)
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  haveI : Nonempty S := ⟨c 1⟩
  obtain ⟨π, hπ⟩ : ∃ π : Fin n → S, Function.Surjective π :=
    ⟨Function.invFun ι, Function.invFun_surjective ι.injective⟩
  let q : S → MonoidAlgebra ℂ G := fun s => ∑ i ∈ Finset.univ.filter (fun i => π i = s), p i
  have hpq : ∀ i s, p i * q s = if π i = s then p i else 0 := by
    intro i s
    simp only [q, Finset.mul_sum]
    rw [Finset.sum_filter, Finset.sum_eq_single i]
    · rw [h1]
    · intro b _ hb; rw [h3 i b hb.symm]; simp
    · simp
  refine ⟨q, fun s => ?_, fun s a => ?_, fun s t hst => ?_, fun s h => ?_, ?_⟩
  · conv_lhs => enter [1]; simp only [q]
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [hpq, if_pos (by simpa using hi)]
  · simp only [q, Finset.sum_mul, Finset.mul_sum, h2]
  · conv_lhs => enter [1]; simp only [q]
    rw [Finset.sum_mul]
    refine Finset.sum_eq_zero fun i hi => ?_
    have : π i = s := by simpa using hi
    rw [hpq, if_neg (this ▸ hst)]
  · obtain ⟨i, rfl⟩ := hπ s
    have := hpq i (π i)
    rw [h, mul_zero, if_pos rfl] at this
    exact h4 i this.symm
  · rw [← h5]; exact Finset.sum_fiberwise _ _ _

theorem exists_charpoly {F : Type} [Field F] {r : ℕ} (f : F[X]) (hm : f.Monic) (hd : f.natDegree = r)
    (h0 : f.coeff 0 ≠ 0) : ∃ x : GL (Fin r) F, (x : Matrix (Fin r) (Fin r) F).charpoly = f := by
  subst hd
  let pb := AdjoinRoot.powerBasis' hm
  have h : (Algebra.leftMulMatrix pb.basis pb.gen).charpoly = f := by
    rw [charpoly_leftMulMatrix]
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic hm
  let M : Matrix (Fin f.natDegree) (Fin f.natDegree) F := Algebra.leftMulMatrix pb.basis pb.gen
  have hM : M.charpoly = f := h
  have hdet : M.det ≠ 0 := by
    rw [Matrix.det_eq_sign_charpoly_coeff, hM]
    exact mul_ne_zero (pow_ne_zero _ (by simp)) h0
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, hM⟩

theorem exists_isSer : ∀ (r g N : ℕ), g.Prime → 0 < N → Nat.card (GL (Fin r) (ZMod g)) ∣ N →
    ∃ e, IsSer r g N e := by
  intro r g N hg hN hG
  classical
  haveI : Fact g.Prime := ⟨hg⟩
  let P : (ZMod g)[X] → Prop := fun f => f.Monic ∧ f.natDegree = r ∧ f.coeff 0 ≠ 0
  let c : GL (Fin r) (ZMod g) → {f // P f} := fun x =>
    ⟨(x : Matrix (Fin r) (Fin r) (ZMod g)).charpoly, Matrix.charpoly_monic _, by simp, by
      intro h
      have h2 := Matrix.det_eq_sign_charpoly_coeff (x : Matrix (Fin r) (Fin r) (ZMod g))
      rw [h, mul_zero] at h2
      exact x.det_ne_zero h2⟩
  have hc : Function.Surjective c := by
    rintro ⟨f, h1, h2, h3⟩
    obtain ⟨x, hx⟩ := exists_charpoly f h1 h2 h3
    exact ⟨x, Subtype.ext hx⟩
  haveI : Finite {f // P f} := Finite.of_surjective c hc
  haveI := Fintype.ofFinite {f // P f}
  obtain ⟨q, h1, h2, h3, h4, h5⟩ := exists_family c hc (fun x y => Subtype.ext (by
    simp only [c, Units.val_mul]; exact Matrix.charpoly_mul_comm _ _))
  let e : (ZMod g)[X] → MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) := fun f => if h : P f then q ⟨f, h⟩ else 0
  have hi : ∀ f, e f * e f = e f := by
    intro f; by_cases h : P f <;> simp [e, h, h1]
  have hce : ∀ f a, e f * a = a * e f := by
    intro f a; by_cases h : P f <;> simp [e, h, h2]
  refine ⟨e, hi, hce, fun f f' hf => ?_, fun f => ?_, ⟨Finset.univ.map (Function.Embedding.subtype P), fun f => ?_, ?_⟩,
    fun f x => coeff_mem hN hG _ (hi f) (hce f) x⟩
  · by_cases h : P f
    · by_cases h' : P f'
      · simp only [e, dif_pos h, dif_pos h']
        exact h3 _ _ (fun hh => hf (congrArg Subtype.val hh))
      · simp [e, h']
    · simp [e, h]
  · change e f = 0 ↔ ¬ P f
    by_cases h : P f <;> simp [e, h, h4]
  · change _ ↔ P f
    simp
  · rw [Finset.sum_map, ← h5]
    exact Finset.sum_congr rfl fun s _ => by simp [e, s.2]

end GlobalTheory.MemN.SerInhab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentThetaData
section
noncomputable section
namespace GlobalTheory.MemN
open Formalism.BasicNotions GlobalTheory.Mem NumberField IsDedekindDomain

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {nd : NData R H what₂} (tw : NTw R H what₂ LL0 nd)

def nexpOfEmpty [IsEmpty tw.Tw] (e : G0g nd → ↥LL0) : NExp R H what₂ LL0 nd tw where
  U := ⊥
  eLL0 := e
  Fm := fun i => isEmptyElim i
  acgFm := fun i => isEmptyElim i
  modFmK := fun i => isEmptyElim i
  modFmO := fun i => isEmptyElim i
  towFm := fun i => isEmptyElim i
  fdFm := fun i => isEmptyElim i
  actG := fun i => isEmptyElim i
  psiU := fun i => isEmptyElim i
  eAlg := fun i => isEmptyElim i
  eAlg_def := fun i => isEmptyElim i
  eAlg_idem := fun i => isEmptyElim i
  eAlg_central := fun i => isEmptyElim i
  Bsup := fun i => isEmptyElim i
  Dat := fun i => isEmptyElim i
  th := fun i => isEmptyElim i
  lev := fun i => isEmptyElim i
  thPsi := fun i => isEmptyElim i
  thPsi_one := fun i => isEmptyElim i
  thU := fun i => isEmptyElim i
  twPsi := fun i => isEmptyElim i
  twPsi_one := fun i => isEmptyElim i
  twDel := fun i => isEmptyElim i
  delU := fun i => isEmptyElim i
  delU_unr := fun i => isEmptyElim i
  delU_l := fun i => isEmptyElim i
  delU_anti := fun i => isEmptyElim i
  delU_open := fun i => isEmptyElim i
  delU_res := fun i => isEmptyElim i
  delU_conj := fun i => isEmptyElim i
  MtV := fun i => isEmptyElim i
  acgMt := fun i => isEmptyElim i
  modMtK := fun i => isEmptyElim i
  modMtO := fun i => isEmptyElim i
  towMt := fun i => isEmptyElim i
  fdMt := fun i => isEmptyElim i
  MtLat := fun i => isEmptyElim i
  MtLat_fg := fun i => isEmptyElim i
  MtLat_span := fun i => isEmptyElim i
  thP := fun i => isEmptyElim i
  hkF := fun i => isEmptyElim i
  embB := fun i => isEmptyElim i
  embB_inj := fun i => isEmptyElim i
  eH := fun i => isEmptyElim i
  eH_idem := fun i => isEmptyElim i

def nthOfEmpty [IsEmpty tw.Tw] (Y : NExp R H what₂ LL0 nd tw) : NTh R H what₂ LL0 nd tw Y where
  iC := fun i => isEmptyElim i
  iC_int := fun i => isEmptyElim i
  aL := fun i => isEmptyElim i
  aL_g := fun i => isEmptyElim i
  aL_off := fun i => isEmptyElim i
  Pt := fun i => isEmptyElim i
  ev := fun i => isEmptyElim i
  ev_smul := fun i => isEmptyElim i
  ev_inj := fun i => isEmptyElim i
  Lt := fun i => isEmptyElim i
  acgLt := fun i => isEmptyElim i
  modLt := fun i => isEmptyElim i
  freeLt := fun i => isEmptyElim i
  finLt := fun i => isEmptyElim i
  Let := fun i => isEmptyElim i
  finLet := fun i => isEmptyElim i
  Harm := fun i => isEmptyElim i
  Ctr := fun i => isEmptyElim i
  ctrC := fun i => isEmptyElim i
  Harm_def := fun i => isEmptyElim i
  thV := fun i => isEmptyElim i
  thV_add := fun i => isEmptyElim i
  thV_smul := fun i => isEmptyElim i
  thV_addP := fun i => isEmptyElim i
  thV_smulP := fun i => isEmptyElim i
  datPhi := fun i => isEmptyElim i
  datP := fun i => isEmptyElim i
  recDet := fun i => isEmptyElim i
  Kq := fun i => isEmptyElim i
  grpKq := fun i => isEmptyElim i
  actK := fun i => isEmptyElim i
  actK_one := fun i => isEmptyElim i
  actK_mul := fun i => isEmptyElim i
  recDetq := fun i => isEmptyElim i
  recDetq_mem := fun i => isEmptyElim i
  recDet_act := fun i => isEmptyElim i
  recDetq_act := fun i => isEmptyElim i
  hkIdx := fun i => isEmptyElim i
  finHk := fun i => isEmptyElim i
  hkMove := fun i => isEmptyElim i
  hkU := fun i => isEmptyElim i
  hk_ev := fun i => isEmptyElim i
  MaximalUnramifiedExtension := fun i => isEmptyElim i
  FmUr := fun i => isEmptyElim i
  FmUr_smul := fun i => isEmptyElim i
  FmUr_span := fun i => isEmptyElim i
  Bsup_def := fun i => isEmptyElim i

end

theorem exists_nexp_nth_of_isEmpty (B : Base) (C : Cols B) (W : RowsRest B C) (nd : NData B.R B.host W.what₂)
    (tw : NTw B.R B.host W.what₂ B.LL0 nd) (h : IsEmpty tw.Tw) (e : G0g nd → ↥B.LL0) :
    ∃ Y : NExp B.R B.host W.what₂ B.LL0 nd tw, Y.eLL0 = e ∧ Nonempty (NTh B.R B.host W.what₂ B.LL0 nd tw Y) :=
  ⟨nexpOfEmpty tw e, rfl, ⟨nthOfEmpty tw _⟩⟩

end GlobalTheory.MemN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeStabilizerConjFiniteAdeleGLIntegralStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_stabilizer_conj_finiteAdeleGL_integral : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), ∃ Λ : Submodule (𝓞 F) (Fin n → F), Submodule.IsFullLattice F Λ ∧ ∀ γ : GL (Fin n) F, (∀ y, (γ : Matrix (Fin n) (Fin n) F) *ᵥ y ∈ Λ ↔ y ∈ Λ) → s⁻¹ * PIW.ClassFinD.glIncl F n γ * s ∈ PIW.ClassFinD.KGL F n := by
  intro F _ _ n s
  let Λ := GlobalTheory.StabLat.lat F s
  have hΛ : Submodule.IsFullLattice F Λ :=
    { toIsLattice := Submodule.IsLattice.of_fg F (GlobalTheory.StabLat.lat_fg s)
      span_eq_top := GlobalTheory.StabLat.lat_span s }
  refine ⟨Λ, hΛ, fun γ hγ => ⟨GlobalTheory.StabLat.matInt_conj s γ fun y hy => (hγ y).2 hy, ?_⟩⟩
  have hinv : (s⁻¹ * PIW.ClassFinD.glIncl F n γ * s)⁻¹ =
      s⁻¹ * PIW.ClassFinD.glIncl F n γ⁻¹ * s := by
    rw [map_inv]; group
  rw [hinv]
  refine GlobalTheory.StabLat.matInt_conj s γ⁻¹ fun y hy => ?_
  rw [← hγ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  exact hy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothVectorsModerateGrowthSmoothFrechetRepStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vectors_moderate_growth_smooth_frechet_rep : ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (ρ : Mx n → (E →L[ℂ] E)), ModRep ε ρ → IsClosed (Fam ε ρ : Set (List (lie (Jm ε)) → E)) ∧ ∃ (p : ℕ → Seminorm ℂ (Fam ε ρ)) (π dπ : Mx n → (Fam ε ρ →L[ℂ] Fam ε ρ)), IsSmoothModRep ε p π dπ ∧ (∀ (g : Mx n) (hg : g ∈ UJset ε) (v : Fam ε ρ) (l : List (lie (Jm ε))), (π g v).1 l = ρ g (v.1 (l.map (adInv hg)))) ∧ (∀ (X : lie (Jm ε)) (v : Fam ε ρ) (l : List (lie (Jm ε))), (dπ (X : Mx n) v).1 l = v.1 (l ++ [X])) ∧ ∀ v : Fam ε ρ, ‖v.1 []‖ ≤ p 0 v := by
  first | exact @GlobalTheory.TypeSum.SmoothFrechet.smooth_frechet_rep | exact GlobalTheory.TypeSum.SmoothFrechet.smooth_frechet_rep | (intros; apply GlobalTheory.TypeSum.SmoothFrechet.smooth_frechet_rep <;> assumption)
end

