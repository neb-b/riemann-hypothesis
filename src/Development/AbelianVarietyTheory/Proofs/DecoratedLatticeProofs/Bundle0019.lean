module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelsCommuteTwisted
section
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity GlobalTheory.PairOp

noncomputable section
namespace GlobalTheory.KernelCommTw

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]

def IsTwEquiv (l' l : kˣ →* ℂˣ) (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V)
    (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V) : Prop :=
  ∀ (g : GL n' k) (h : GL n k) (v : V') (Ψ Ψ' : SB (Matrix n n' k)),
    (∀ x, Ψ'.1 x = (l' (Matrix.GeneralLinearGroup.det g) : ℂ) * (l (Matrix.GeneralLinearGroup.det h) : ℂ) *
      Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (π' g v) Ψ' = π h (θ v Ψ)

variable {l' l : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}

theorem unram_val {χ : kˣ →* ℂˣ} (hχ : IsUnram χ) (u z : kˣ) (hz : valuation k ((z * u : kˣ) : k) = 1) :
    (χ z : ℂ) = (χ u : ℂ)⁻¹ := by
  have := congrArg (fun w : ℂˣ => (w : ℂ)) (hχ _ hz)
  simp only [map_mul, Units.val_mul, Units.val_one] at this
  exact eq_inv_of_mul_eq_one_left this

theorem theta_mem (hl : IsUnram l) (hθ : IsTwEquiv l' l π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n) (v : V') :
    θ v (phiOneSB P₀ Q₀) ∈ levelVec π Q₀ := fun h hh => by
  have hv := valuation_det_of_fix Q₀.lat (h := h) (by rw [← Pair.smul_lat, hh])
  have := hθ 1 h v (phiOneSB P₀ Q₀) (phiOneSB P₀ Q₀) fun x => by
    have e := phiOne_smul (x := x) (P := P₀) (Q := Q₀) 1 h
    rw [one_smul, hh] at e
    simp only [phiOneSB, map_one, hl _ hv, Units.val_one, one_mul]
    simpa using e
  simpa using this.symm

variable (hl : IsUnram l) (hθ : IsTwEquiv l' l π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n)

def KK : Form k n' V' →ₗ[ℂ] Form k n V :=
  (EqForm π).subtype ∘ₗ (evalEquiv π Q₀).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict _ (θ.flip (phiOneSB P₀ Q₀) ∘ₗ LinearMap.proj P₀) fun φ => theta_mem hl hθ P₀ Q₀ (φ P₀)

theorem KK_mem (φ : Form k n' V') : KK hl hθ P₀ Q₀ φ ∈ EqForm π := formOf_mem _ _ _

theorem KK_smul (φ : Form k n' V') (h : GL n k) :
    KK hl hθ P₀ Q₀ φ (h • Q₀) = π h (θ (φ P₀) (phiOneSB P₀ Q₀)) := formOf_smul π Q₀ _ h

theorem KK_move (hl' : IsUnram l') {φ : Form k n' V'} (hφ : φ ∈ EqForm π') (u : kˣ) (g : GL n' k) (h : GL n k)
    (hg : valuation k ((Matrix.GeneralLinearGroup.det g * u : kˣ) : k) = 1)
    (hh : valuation k ((Matrix.GeneralLinearGroup.det h * u : kˣ) : k) = 1) :
    KK hl hθ P₀ Q₀ φ (h • Q₀) = ((l' u : ℂ) * (l u : ℂ))⁻¹ • θ (φ (g • P₀)) (phiOneSB (g • P₀) (h • Q₀)) := by
  rw [KK_smul, hφ g, ← map_smul]
  refine (hθ g h _ _ _ fun x => ?_).symm
  simp only [phiOneSB, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, phiOne_smul, unram_val hl' u _ hg,
    unram_val hl u _ hh]
  rw [mul_inv]

theorem KK_same (hl' : IsUnram l') {φ : Form k n' V'} (hφ : φ ∈ EqForm π') {P : Pair k n'} {Q : Pair k n}
    (hP : P.lat = P₀.lat) (hQ : Q.lat = Q₀.lat) : KK hl hθ P₀ Q₀ φ Q = θ (φ P) (phiOneSB P Q) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n' k) P₀ P
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [KK_move hl hθ P₀ Q₀ hl' hφ 1 g h (by simpa only [mul_one] using valuation_det_of_fix _ hP)
    (by simpa only [mul_one] using valuation_det_of_fix _ hQ)]
  simp

theorem KK_up (hl' : IsUnram l') (q : Unif k) {φ : Form k n' V'} (hφ : φ ∈ EqForm π') {P : Pair k n'}
    {Q : Pair k n} (hP : P.ker = P₀.lat) (hQ : Q.ker = Q₀.lat) :
    KK hl hθ P₀ Q₀ φ Q = ((l' q.unit : ℂ) * (l q.unit : ℂ))⁻¹ • θ (φ P) (phiOneSB P Q) := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n' k) P₀ P
  obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) Q₀ Q
  rw [Pair.smul_ker] at hP hQ
  exact KK_move hl hθ P₀ Q₀ hl' hφ q.unit g h (GlobalTheory.KernelComm.valuation_det q _ hP)
    (GlobalTheory.KernelComm.valuation_det q _ hQ)

theorem U_KK (hl' : IsUnram l') (q : Unif k) {φ : Form k n' V'} (hφ : φ ∈ EqForm π') :
    U q (KK hl hθ P₀ Q₀ φ) = ((l' q.unit : ℂ) * (l q.unit : ℂ))⁻¹ • KK hl hθ P₀ Q₀ (U q φ) := by
  classical
  refine GlobalTheory.KernelComm.eq_of_base Q₀ (U_mem_EqForm q (KK_mem hl hθ P₀ Q₀ φ))
    (Submodule.smul_mem _ _ (KK_mem hl hθ P₀ Q₀ _)) ?_
  have h1 : ∀ P₁ ∈ withKer P₀.lat, U q (KK hl hθ P₀ Q₀ φ) Q₀ =
      ((l' q.unit : ℂ) * (l q.unit : ℂ))⁻¹ •
        ∑ P ∈ withLat P₀.lat, if cross q P₁ P = 1 then θ (φ P₁) (phiOneSB P Q₀) else 0 := fun P₁ hP => by
    rw [mem_withKer] at hP
    set_option synthInstance.maxHeartbeats 100000 in
      rw [U_apply, Finset.sum_congr rfl fun Q₁ hQ =>
      KK_up hl hθ P₀ Q₀ hl' q hφ hP (mem_withKer.1 (Finset.mem_filter.1 hQ).1), ← Finset.smul_sum,
      ← Finset.sum_filter, ← map_sum, ← map_sum, ← hP]
    congr 2
    refine Subtype.ext (funext fun x => ?_)
    simp only [Submodule.coe_sum, Finset.sum_apply, phiOneSB]
    have htarget {e₁ : n' → k} (he : P₁.HasVal e₁ 1) (Q : Pair k n) (x : Matrix n n' k) :
        ∑ Q₁ ∈ withKer Q.lat with cross q Q₁ Q = 1, phiOne P₁ Q₁ x = midInd q P₁.ker e₁ Q x := by
      have hm : ∀ Q₁ : Pair k n, Maps P₁ Q₁ x ↔ (∀ y ∈ P₁.ker, x *ᵥ y ∈ Q₁.ker) ∧ Q₁.HasVal (x *ᵥ e₁) 1 := fun Q₁ => by
        rw [maps_iff_glue he Q₁.hasVal_vec, Pair.hasVal_one_iff Q₁.hasVal_vec]
      rw [midInd, mulVec_smul]
      split_ifs with h
      · have hg : IsGlue Q.lat (x *ᵥ e₁) := (isGlue_iff q).2 ⟨Q.isLat, fun h0 =>
          one_ne_zero (h.2.unique (Pair.mem_ker.1 (Pair.smul_mem_ker q.mem_max h0))), h.2.mem⟩
        rw [Finset.sum_eq_single_of_mem (glue hg)]
        · exact if_pos ((hm _).2 ⟨by rw [glue_ker]; exact h.1, glue_hasVal hg⟩)
        · exact Finset.mem_filter.2 ⟨mem_withKer.2 (glue_ker hg),
            (cross_hasVal q (glue_ker hg).symm (glue_hasVal hg)).unique h.2⟩
        · exact fun Q₁ h1 h2 => if_neg fun h3 =>
            h2 ((eq_glue_iff hg).2 ⟨mem_withKer.1 (Finset.mem_filter.1 h1).1, ((hm _).1 h3).2⟩)
      · refine Finset.sum_eq_zero fun Q₁ h1 => if_neg fun h3 => h ?_
        obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h1
        rw [mem_withKer] at h1
        exact ⟨h1 ▸ ((hm _).1 h3).1, h2 ▸ cross_hasVal q h1.symm ((hm _).1 h3).2⟩
    
    have hsource {e₁ : n' → k} (he : P₁.HasVal e₁ 1) (Q : Pair k n) (x : Matrix n n' k) :
        midInd q P₁.ker e₁ Q x = ∑ P ∈ withLat P₁.ker with cross q P₁ P = 1, phiOne P Q x := by
      rw [midInd]
      have hq : q.1 • e₁ ∈ P₁.ker := Pair.smul_mem_ker q.mem_max he.mem
      split_ifs with h
      · let f : P₁.ker →ₗ[𝒪[k]] 𝓀[k] := Q.fn ∘ₗ ((Matrix.mulVecLin x).restrictScalars 𝒪[k]).restrict h.1
        have hf : ∀ y : P₁.ker, Q.HasVal (x *ᵥ y) (f y) := fun y => ⟨h.1 y y.2, rfl⟩
        have h1 : f ⟨_, hq⟩ = 1 := (hf ⟨_, hq⟩).unique h.2
        let R : Pair k n' := ⟨P₁.ker, P₁.ker_isLat, f, fun h0 => by simp [h0] at h1⟩
        have hR : Maps R Q x := ⟨h.1, fun _ => rfl⟩
        rw [Finset.sum_eq_single_of_mem R]
        · exact (if_pos hR).symm
        · exact Finset.mem_filter.2 ⟨mem_withLat.2 rfl, (cross_hasVal q (P := R) rfl he).unique ⟨hq, h1⟩⟩
        · refine fun P hP h2 => if_neg fun h3 => h2 (Pair.ext fun y a => ?_)
          have hl : P.lat = R.lat := mem_withLat.1 (Finset.mem_filter.1 hP).1
          rw [maps_iff_hasVal] at hR h3
          constructor
          · intro hy
            have h4 := R.hasVal_fn ⟨y, hl ▸ hy.mem⟩
            exact (hR _ _ h4).unique (h3 _ _ hy) ▸ h4
          · intro hy
            have h4 := P.hasVal_fn ⟨y, hl ▸ hy.mem⟩
            exact (h3 _ _ h4).unique (hR _ _ hy) ▸ h4
      · refine (Finset.sum_eq_zero fun P h1 => if_neg fun h3 => h ?_).symm
        obtain ⟨h1, h2⟩ := Finset.mem_filter.1 h1
        rw [mem_withLat] at h1
        exact ⟨h1 ▸ h3.1, maps_iff_hasVal.1 h3 _ _ (h2 ▸ cross_hasVal q h1 he)⟩
    exact (htarget P₁.hasVal_vec Q₀ x).trans (hsource P₁.hasVal_vec Q₀ x)
  have h2 : ∀ P ∈ withLat P₀.lat, KK hl hθ P₀ Q₀ (U q φ) Q₀ =
      ∑ P₁ ∈ withKer P₀.lat, if cross q P₁ P = 1 then θ (φ P₁) (phiOneSB P Q₀) else 0 := fun P hP => by
    rw [mem_withLat] at hP
    set_option synthInstance.maxHeartbeats 100000 in
      rw [KK_same hl hθ P₀ Q₀ hl' (U_mem_EqForm q hφ) hP rfl, U_apply, map_sum, LinearMap.sum_apply, hP,
      Finset.sum_filter]
  have h3 := Finset.sum_congr rfl h1
  rw [← Finset.smul_sum, Finset.sum_comm, ← Finset.sum_congr rfl h2, Finset.sum_const, Finset.sum_const,
    GlobalTheory.KernelComm.card_withKer q, smul_comm, ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at h3
  refine smul_right_injective V ?_ h3
  exact_mod_cast (Finset.card_pos.2 ⟨P₀, mem_withLat.2 rfl⟩).ne'

theorem KK_dia (hl' : IsUnram l') (s : 𝓀[k]ˣ) {φ : Form k n' V'} (hφ : φ ∈ EqForm π') :
    KK hl hθ P₀ Q₀ (dia s φ) = dia s (KK hl hθ P₀ Q₀ φ) := by
  refine GlobalTheory.KernelComm.eq_of_base Q₀ (KK_mem hl hθ P₀ Q₀ _) (dia_mem_EqForm s (KK_mem hl hθ P₀ Q₀ φ)) ?_
  rw [dia_apply, KK_same hl hθ P₀ Q₀ hl' hφ (P := s • P₀) (Q := s • Q₀) rfl rfl,
    KK_same hl hθ P₀ Q₀ hl' (dia_mem_EqForm s hφ) rfl rfl, dia_apply]
  congr 1
  exact Subtype.ext (phiOne_dia s).symm

theorem KK_ram (hl' : IsUnram l') {φ : Form k n' V'} (hφ : φ ∈ EqForm π') (h : φ ∈ Mram k n' V') :
    KK hl hθ P₀ Q₀ φ ∈ Mram k n V := by
  have : Nm (KK hl hθ P₀ Q₀ φ) = KK hl hθ P₀ Q₀ (Nm φ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Nm, LinearMap.sum_apply, map_sum, KK_dia hl hθ P₀ Q₀ hl' _ hφ]
  rw [show Nm φ = 0 from h, map_zero] at this
  exact this

theorem FFStar_KK (hl' : IsUnram l') (q : Unif k) (χ : AddChar 𝓀[k] ℂ) {φ : Form k n' V'} (hφ : φ ∈ EqForm π')
    (h : φ ∈ Mram k n' V') :
    FFStar q χ (KK hl hθ P₀ Q₀ φ) = ((l' q.unit : ℂ) * (l q.unit : ℂ))⁻¹ • KK hl hθ P₀ Q₀ (FFStar q χ φ) := by
  have h1 : GsStar χ (KK hl hθ P₀ Q₀ φ) = KK hl hθ P₀ Q₀ (GsStar χ φ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GsStar, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, KK_dia hl hθ P₀ Q₀ hl' _ hφ]
  have h2 : GsStar χ φ ∈ EqForm π' := by
    simp only [GsStar, LinearMap.sum_apply, LinearMap.smul_apply]
    exact sum_mem fun c _ => Submodule.smul_mem _ _ (dia_mem_EqForm _ hφ)
  rw [FFStar_eq_U_GsStar q χ h, FFStar_eq_U_GsStar q χ (KK_ram hl hθ P₀ Q₀ hl' hφ h), h1,
    U_KK hl hθ P₀ Q₀ hl' q h2]

theorem KK_FFStar (hl' : IsUnram l') (q : Unif k) (χ : AddChar 𝓀[k] ℂ) {φ : Form k n' V'} (hφ : φ ∈ EqForm π')
    (h : φ ∈ Mram k n' V') :
    KK hl hθ P₀ Q₀ (FFStar q χ φ) = ((l' q.unit : ℂ) * (l q.unit : ℂ)) • FFStar q χ (KK hl hθ P₀ Q₀ φ) := by
  rw [FFStar_KK hl hθ P₀ Q₀ hl' q χ hφ h, smul_smul, mul_inv_cancel₀ (mul_ne_zero (Units.ne_zero _)
    (Units.ne_zero _)), one_smul]

end GlobalTheory.KernelCommTw

namespace GlobalTheory.KernelCommTw

theorem kernelsCommuteTwisted : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (q : Unif k) (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (l' l : kˣ →* ℂˣ), IsUnram l' → IsUnram l → ∀ (P₀ : Pair k n') (Q₀ : Pair k n), ∃ c : ℂ, c ≠ 0 ∧ ∀ (V' V : Type) [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V] (π' : Representation ℂ (GL n' k) V') (π : Representation ℂ (GL n k) V) (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V), (∀ (g : GL n' k) (h : GL n k) (v : V') (Ψ Ψ' : SB (Matrix n n' k)), (∀ x, Ψ'.1 x = (l' (Matrix.GeneralLinearGroup.det g) : ℂ) * (l (Matrix.GeneralLinearGroup.det h) : ℂ) * Ψ.1 ((h⁻¹ : GL n k).val * x * g.val)) → θ (π' g v) Ψ' = π h (θ v Ψ)) → ∃ K : EqForm π' →ₗ[ℂ] EqForm π, (∀ φ, (K φ).1 Q₀ = θ (φ.1 P₀) (phiOneSB P₀ Q₀)) ∧ (∀ (s : 𝓀[k]ˣ) φ, (K ⟨dia s φ.1, dia_mem_EqForm s φ.2⟩).1 = dia s (K φ).1) ∧ ∀ φ : EqForm π', φ.1 ∈ Mram k n' V' → (K φ).1 ∈ Mram k n V ∧ (K ⟨FFStar q (resChar ψ hψ q) φ.1, FFStar_mem_EqForm q _ φ.2⟩).1 = c • FFStar q (resChar ψ hψ q) (K φ).1 := by
  intro k _ _ _ _ n n' _ _ _ _ q ψ hψ l' l hl' hl P₀ Q₀
  refine ⟨(l' q.unit : ℂ) * (l q.unit : ℂ), mul_ne_zero (Units.ne_zero _) (Units.ne_zero _), ?_⟩
  intro V' V _ _ _ _ π' π θ hθ
  refine ⟨LinearMap.codRestrict (EqForm π) (KK hl hθ P₀ Q₀ ∘ₗ (EqForm π').subtype)
    fun φ => KK_mem hl hθ P₀ Q₀ φ.1, fun φ => ?_, fun s φ => KK_dia hl hθ P₀ Q₀ hl' s φ.2, fun φ h =>
      ⟨KK_ram hl hθ P₀ Q₀ hl' φ.2 h, KK_FFStar hl hθ P₀ Q₀ hl' q _ φ.2 h⟩⟩
  show KK hl hθ P₀ Q₀ φ.1 Q₀ = _
  simpa using KK_smul hl hθ P₀ Q₀ φ.1 1

end GlobalTheory.KernelCommTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section
namespace GlobalTheory.SymPattern
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

section Field
variable {F : Type} [Field F] {κ l : ℕ}

theorem mul_fromBlocks_inl (M : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) (C : Matrix (Fin κ) (Fin κ) F)
    (a : Fin κ ⊕ Fin l) (j : Fin κ) :
    (M * (fromBlocks C 0 0 1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) : Matrix _ _ F) a (Sum.inl j) = ∑ t, M a (Sum.inl t) * C t j := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type]

theorem mul_fromBlocks_inr (M : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) (C : Matrix (Fin κ) (Fin κ) F)
    (a : Fin κ ⊕ Fin l) (j : Fin l) :
    (M * (fromBlocks C 0 0 1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) F) : Matrix _ _ F) a (Sum.inr j) = M a (Sum.inr j) := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem pat_of_mul (ρ : ℕ) (u : GL (Fin κ ⊕ Fin l) F) (hu : InN (ρ + 1) u) (γ : GL (Fin κ) F)
    (hγ : IsUpperUnip Fin.val γ.val) :
    ∀ a b, ¬ FreeTop ρ a b → (u * embX l γ).val a b = (1 : Matrix _ _ F) a b := by
  intro a b hab
  have hv : (u * embX l γ).val = u.val * fromBlocks γ.val 0 0 1 := by
    rw [Units.val_mul, Radical.embX_val]
  rw [hv]
  rcases a with i | i <;> rcases b with j | j <;> simp only [FreeTop, not_lt] at hab
  · rw [mul_fromBlocks_inl]
    have hu' : ∀ t, u.val (Sum.inl i) (Sum.inl t) = if i = t then 1 else 0 := fun t => by
      rw [hu (Sum.inl i) (Sum.inl t) le_rfl, Matrix.one_apply]; simp
    simp only [hu', ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hγ i j (by exact_mod_cast hab)]
    simp [Matrix.one_apply]
  · rw [mul_fromBlocks_inr, hu (Sum.inl i) (Sum.inr j) (Nat.succ_le_succ hab)]
  · rw [mul_fromBlocks_inl]
    have hu' : ∀ t, u.val (Sum.inr i) (Sum.inl t) = 0 := fun t => by
      rw [hu (Sum.inr i) (Sum.inl t) (Nat.succ_le_succ hab)]; simp
    simp [hu']
  · rw [mul_fromBlocks_inr, hu (Sum.inr i) (Sum.inr j) (Nat.succ_le_succ hab)]

theorem exists_of_pat (ρ : ℕ) (gb : GL (Fin κ ⊕ Fin l) F)
    (h : ∀ a b, ¬ FreeTop ρ a b → gb.val a b = (1 : Matrix _ _ F) a b) :
    ∃ u : GL (Fin κ ⊕ Fin l) F, InN (ρ + 1) u ∧ ∃ γ : GL (Fin κ) F,
      IsUpperUnip Fin.val γ.val ∧ gb = u * embX l γ := by
  have hU : IsUpperUnip Fin.val gb.val.toBlocks₁₁ := fun r t hrt => by
    have := h (Sum.inl r) (Sum.inl t) (by simp only [FreeTop, not_lt]; exact hrt)
    simpa [Matrix.toBlocks₁₁, Matrix.one_apply] using this
  have hdet : gb.val.toBlocks₁₁.det = 1 := Radical.Uni.det (b := Fin.val) hU
  let γ : GL (Fin κ) F := ⟨gb.val.toBlocks₁₁, gb.val.toBlocks₁₁⁻¹,
    Matrix.mul_nonsing_inv _ (by rw [hdet]; exact isUnit_one),
    Matrix.nonsing_inv_mul _ (by rw [hdet]; exact isUnit_one)⟩
  refine ⟨gb * (embX l γ)⁻¹, ?_, γ, hU, (inv_mul_cancel_right gb _).symm⟩
  have hv : (gb * (embX l γ)⁻¹).val = gb.val * fromBlocks (γ⁻¹).val 0 0 1 := by
    rw [Units.val_mul, ← map_inv, Radical.embX_val]
  intro r t hrt
  rw [hv]
  rcases r with i | i <;> rcases t with j | j
  · rw [mul_fromBlocks_inl]
    have hm : ∑ q, gb.val (Sum.inl i) (Sum.inl q) * (γ⁻¹).val q j =
        (1 : Matrix (Fin κ) (Fin κ) F) i j := by
      have := congrFun (congrFun γ.mul_inv i) j
      rw [Matrix.mul_apply] at this
      exact this
    rw [hm]
    simp [Matrix.one_apply]
  · have hrt' : j.val + 1 ≤ ρ + 1 := hrt
    rw [mul_fromBlocks_inr]
    exact h _ _ (by simp only [FreeTop, not_lt]; omega)
  · have hrt' : ρ + 1 ≤ i.val + 1 := hrt
    rw [mul_fromBlocks_inl]
    have hz : ∀ q, gb.val (Sum.inr i) (Sum.inl q) = 0 := fun q => by
      have := h (Sum.inr i) (Sum.inl q) (by simp only [FreeTop, not_lt]; omega)
      simpa [Matrix.one_apply] using this
    simp [hz]
  · have hrt' : j.val + 1 ≤ i.val + 1 := hrt
    rw [mul_fromBlocks_inr]
    exact h _ _ (by simp only [FreeTop, not_lt]; exact Fin.le_def.mpr (by omega))

end Field

section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

private theorem valuation_lt_one_iff_residue_eq_zero (y : 𝒪[k]) :
    valuation k (y : k) < 1 ↔ IsLocalRing.residue 𝒪[k] y = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.symm

theorem entry_lt_iff (g₀ : GL ι 𝒪[k]) (a b : ι) :
    valuation k ((Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀).val a b - (1 : Matrix ι ι k) a b) < 1 ↔
      (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀).val a b = (1 : Matrix ι ι 𝓀[k]) a b := by
  have e1 : (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) g₀).val a b - (1 : Matrix ι ι k) a b =
      ((g₀.val a b - (1 : Matrix ι ι 𝒪[k]) a b : 𝒪[k]) : k) := by
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab] <;> rfl
  have e2 : (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀).val a b -
      (1 : Matrix ι ι 𝓀[k]) a b = IsLocalRing.residue 𝒪[k] (g₀.val a b - (1 : Matrix ι ι 𝒪[k]) a b) := by
    by_cases hab : a = b <;> simp [Matrix.one_apply, hab]
  rw [e1, valuation_lt_one_iff_residue_eq_zero, ← e2, sub_eq_zero]

end Local

end GlobalTheory.SymPattern

theorem GlobalTheory.SymChain.SymData.mem_J_iff_pattern :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ)
      (S : SymData k s κ) (g : GL (Fin κ ⊕ Fin (s + 1)) k),
      g ∈ S.P.J ↔ g ∈ KO k _ ∧ ∀ a b, ¬ FreeTop S.ρ a b →
        valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1 := by
  intro k _ _ _ _ s κ S g
  rw [S.sym.1 g]
  constructor
  · rintro ⟨u, hu, γ, hγ, g₀, hg₀, hgb⟩
    refine ⟨⟨g₀, hg₀⟩, fun a b hab => ?_⟩
    rw [← hg₀, SymPattern.entry_lt_iff, hgb]
    exact SymPattern.pat_of_mul S.ρ u ((Radical.mem_N_iff u).mp hu) γ hγ a b hab
  · rintro ⟨⟨g₀, hg₀⟩, hpat⟩
    obtain ⟨u, hu, γ, hγ, he⟩ := SymPattern.exists_of_pat S.ρ
      (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k]) g₀) (fun a b hab => by
        rw [← SymPattern.entry_lt_iff, hg₀]; exact hpat a b hab)
    exact ⟨u, (Radical.mem_N_iff u).mpr hu, γ, hγ, g₀, hg₀, he⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RelIndexScaledMaxIdeal
section
open ValuativeRel GlobalTheory.SplitWeil

namespace GlobalTheory.ScaledIdealIndex

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem relIndex_comap_mulLeft (a : kˣ) (H K : AddSubgroup k) :
    (H.comap (AddMonoidHom.mulLeft (a : k))).relIndex (K.comap (AddMonoidHom.mulLeft (a : k))) =
      H.relIndex K := by
  have hs : Function.Surjective (AddMonoidHom.mulLeft (a : k)) := fun y =>
    ⟨((a⁻¹ : kˣ) : k) * y, by simp [← mul_assoc]⟩
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hs]

theorem relIndex_maxIdeal (L : AddSubgroup k) (hL : ∀ x, x ∈ L ↔ valuation k x < 1) :
    L.relIndex (𝒪[k]).toAddSubgroup = resCard k := by
  let f : 𝒪[k] →+ k := (𝒪[k]).subtype.toAddMonoidHom
  have hr : f.range = (𝒪[k]).toAddSubgroup := by
    ext x; simp [f]
  let g : 𝒪[k] →+ 𝓀[k] := (IsLocalRing.residue 𝒪[k]).toAddMonoidHom
  have hk : L.comap f = g.ker := by
    ext y
    simp only [AddSubgroup.mem_comap, AddMonoidHom.mem_ker, g, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one, hL]
    rfl
  have hs : Function.Surjective g := Ideal.Quotient.mk_surjective
  rw [← hr, ← AddSubgroup.index_comap, hk, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hs]
  simp [resCard]

section
variable (L : AddSubgroup k) (hL : ∀ x, x ∈ L ↔ valuation k x < 1)
include hL

theorem mem_comap_mulLeft (a : kˣ) (x : k) :
    x ∈ L.comap (AddMonoidHom.mulLeft (a : k)) ↔ valuation k ((a : k) * x) < 1 := by
  simp [hL]

theorem comap_mulLeft_one : L.comap (AddMonoidHom.mulLeft ((1 : kˣ) : k)) = L := by
  ext x; simp [hL]

theorem comap_mulLeft_mul (a b : kˣ) :
    L.comap (AddMonoidHom.mulLeft ((a * b : kˣ) : k)) =
      (L.comap (AddMonoidHom.mulLeft (a : k))).comap (AddMonoidHom.mulLeft (b : k)) := by
  ext x; simp [hL, mul_assoc]

theorem comap_mulLeft_le_pow (ϖ : kˣ) (hϖ : valuation k (ϖ : k) ≤ 1) (a : kˣ) (j : ℕ) :
    L.comap (AddMonoidHom.mulLeft (a : k)) ≤ L.comap (AddMonoidHom.mulLeft ((ϖ ^ j * a : kˣ) : k)) := by
  intro x hx
  rw [mem_comap_mulLeft L hL] at hx ⊢
  rw [Units.val_mul, Units.val_pow_eq_pow_val, mul_assoc, map_mul, map_pow]
  exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le' (pow_le_one₀ zero_le' hϖ)) hx

theorem relIndex_unif (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) :
    (L.comap (AddMonoidHom.mulLeft ((ϖ⁻¹ : kˣ) : k))).relIndex L = resCard k := by
  have hpos : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have e : L = (𝒪[k]).toAddSubgroup.comap (AddMonoidHom.mulLeft ((ϖ⁻¹ : kˣ) : k)) := by
    ext x
    rw [hL]
    simp only [AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft, Subring.mem_toAddSubgroup,
      Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
    rw [inv_mul_le_iff₀ hpos, mul_one, hϖ, le_uniformizer_iff]
  calc (L.comap (AddMonoidHom.mulLeft ((ϖ⁻¹ : kˣ) : k))).relIndex L
      = (L.comap (AddMonoidHom.mulLeft ((ϖ⁻¹ : kˣ) : k))).relIndex
          ((𝒪[k]).toAddSubgroup.comap (AddMonoidHom.mulLeft ((ϖ⁻¹ : kˣ) : k))) := by rw [← e]
    _ = resCard k := by rw [relIndex_comap_mulLeft, relIndex_maxIdeal L hL]

theorem relIndex_unif_pow (ϖ : kˣ) (hϖ : valuation k (ϖ : k) = uniformizer k) (n : ℕ) :
    (L.comap (AddMonoidHom.mulLeft ((ϖ ^ (-(n : ℤ)) : kˣ) : k))).relIndex L = resCard k ^ n := by
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ ▸ uniformizer_lt_one.le
  induction n with
  | zero => rw [Nat.cast_zero, neg_zero, zpow_zero, comap_mulLeft_one L hL, pow_zero, AddSubgroup.relIndex_self]
  | succ n ih =>
    have ea : ϖ ^ (-((n + 1 : ℕ) : ℤ)) = ϖ⁻¹ * ϖ ^ (-(n : ℤ)) := by
      rw [← zpow_neg_one, ← zpow_add]; congr 1; push_cast; ring
    have eb : ϖ ^ (-(n : ℤ)) = ϖ ^ (1 : ℕ) * ϖ ^ (-((n + 1 : ℕ) : ℤ)) := by
      rw [ea, pow_one, ← mul_assoc, mul_inv_cancel, one_mul]
    have hle : L.comap (AddMonoidHom.mulLeft ((ϖ ^ (-((n + 1 : ℕ) : ℤ)) : kˣ) : k)) ≤
        L.comap (AddMonoidHom.mulLeft ((ϖ ^ (-(n : ℤ)) : kˣ) : k)) := by
      rw [eb]; exact comap_mulLeft_le_pow L hL ϖ h1 _ 1
    have hle2 : L.comap (AddMonoidHom.mulLeft ((ϖ ^ (-(n : ℤ)) : kˣ) : k)) ≤ L := by
      have := comap_mulLeft_le_pow L hL ϖ h1 (ϖ ^ (-(n : ℤ))) n
      rwa [← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero, comap_mulLeft_one L hL] at this
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle hle2, ih, pow_succ, mul_comm]
    congr 1
    have e1 : L.comap (AddMonoidHom.mulLeft ((ϖ ^ (-(n : ℤ)) : kˣ) : k)) =
        L.comap (AddMonoidHom.mulLeft (((1 : kˣ) * ϖ ^ (-(n : ℤ)) : kˣ) : k)) := by rw [one_mul]
    rw [ea, e1, comap_mulLeft_mul L hL, comap_mulLeft_mul L hL, relIndex_comap_mulLeft,
      comap_mulLeft_one L hL, relIndex_unif L hL ϖ hϖ]

end

end GlobalTheory.ScaledIdealIndex

namespace GlobalTheory.ScaledIdealIndex

theorem relIndex_scaled_maxIdeal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k →
    ∀ (c : ℤ) (L P : AddSubgroup k), (∀ x, x ∈ L ↔ valuation k x < 1) →
      (∀ x, x ∈ P ↔ valuation k (((ϖ ^ c : kˣ) : k) * x) < 1) →
      (P ⊓ L).relIndex P * (P ⊓ L).relIndex L = resCard k ^ c.natAbs := by
  intro k _ _ _ _ ϖ hϖ c L P hL hP
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ ▸ uniformizer_lt_one.le
  have hPe : P = L.comap (AddMonoidHom.mulLeft ((ϖ ^ c : kˣ) : k)) := by
    ext x; rw [hP, mem_comap_mulLeft L hL]
  rw [AddSubgroup.inf_relIndex_left, AddSubgroup.inf_relIndex_right]
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · have hLP : L ≤ P := by
      have := comap_mulLeft_le_pow L hL ϖ h1 1 n
      rwa [mul_one, comap_mulLeft_one L hL, ← zpow_natCast, ← hPe] at this
    rw [AddSubgroup.relIndex_eq_one.2 hLP, mul_one, Int.natAbs_natCast]
    have eL : L = L.comap (AddMonoidHom.mulLeft (((ϖ ^ (-(n : ℤ)) * ϖ ^ (n : ℤ) : kˣ)) : k)) := by
      rw [← zpow_add, neg_add_cancel, zpow_zero, comap_mulLeft_one L hL]
    have eP : P = L.comap (AddMonoidHom.mulLeft ((((1 : kˣ) * ϖ ^ (n : ℤ) : kˣ)) : k)) := by
      rw [one_mul, hPe]
    calc L.relIndex P
        = (L.comap (AddMonoidHom.mulLeft (((ϖ ^ (-(n : ℤ)) * ϖ ^ (n : ℤ) : kˣ)) : k))).relIndex
            (L.comap (AddMonoidHom.mulLeft ((((1 : kˣ) * ϖ ^ (n : ℤ) : kˣ)) : k))) := by
          rw [← eL, ← eP]
      _ = resCard k ^ n := by
          rw [comap_mulLeft_mul L hL, comap_mulLeft_mul L hL, relIndex_comap_mulLeft,
            comap_mulLeft_one L hL, relIndex_unif_pow L hL ϖ hϖ n]
  · have hPL : P ≤ L := by
      have := comap_mulLeft_le_pow L hL ϖ h1 (ϖ ^ (-(n : ℤ))) n
      rwa [← zpow_natCast, ← zpow_add, add_neg_cancel, zpow_zero, comap_mulLeft_one L hL, ← hPe] at this
    rw [AddSubgroup.relIndex_eq_one.2 hPL, one_mul, Int.natAbs_neg, Int.natAbs_natCast, hPe,
      relIndex_unif_pow L hL ϖ hϖ n]

end GlobalTheory.ScaledIdealIndex
end

