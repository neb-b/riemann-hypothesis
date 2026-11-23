module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0004
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.KIface
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CIface
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CJDefs
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

variable {n : ℕ} (G : Grp k n)

def HasEtaVec {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) W) :
    Prop :=
  ∃ y : W, y ≠ 0 ∧ ∀ m ∈ leviK k (m := fun a : Fin G.s => Fin (G.d a)), ρ m y = G.eta m • y

def JacquetModuleFiniteProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible → IsSmooth (jacU G.e π) ∧ HasFiniteLength (jacU G.e π)

def SubquotientProp : Prop :=
  ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) W),
    IsSmooth ρ → HasFiniteLength ρ → G.HasEtaVec ρ →
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module ℂ X) (σ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) X),
      IsSmooth σ ∧ σ.IsIrreducible ∧ IsSubquotient σ ρ ∧ G.HasEtaVec σ

def TensorProductProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ (Levi k fun a : Fin G.s => Fin (G.d a)) X),
    IsSmooth σ → σ.IsIrreducible → G.HasEtaVec σ →
    ∃ (Y : Fin G.s → Type) (_ : ∀ a, AddCommGroup (Y a)) (_ : ∀ a, Module ℂ (Y a))
      (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
      (∀ a, IsSmooth (τ a)) ∧ (∀ a, (τ a).IsIrreducible) ∧ (∀ a, HasDetVec (τ a) (G.μ a)) ∧
        Nonempty (σ.Equiv (piTensor τ))

def SupportOfProductProp : Prop :=
  GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    IsSmooth π → π.IsIrreducible →
    ∀ (Y : Fin G.s → Type) [∀ a, AddCommGroup (Y a)] [∀ a, Module ℂ (Y a)] (τ : ∀ a, Representation ℂ (GL (Fin (G.d a)) k) (Y a)),
      (∀ a, IsSmooth (τ a)) → (∀ a, (τ a).IsIrreducible) → (∀ a, HasDetVec (τ a) (G.μ a)) →
      IsSubquotient (piTensor τ) (jacU G.e π) → IsTwSphProd π G.d G.hd G.μ

def ExistsGroupElementProp : Prop :=
  ∀ (n : ℕ) (χ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (χ i)) →
    ∃ (G : Grp k n) (σ : Equiv.Perm (Fin n)), ∀ i, res (χ (σ i)) = res (G.chi i)

end Grp

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CharacterConductor
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace Grp

namespace CharacterConductor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def CS (ψ : 𝒪[k]ˣ →* ℂˣ) : Set ℕ :=
  {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → ψ u = 1}

theorem cond_eq (ψ : 𝒪[k]ˣ →* ℂˣ) : cond ψ = sInf (CS ψ) := rfl

theorem CS_mono (ψ : 𝒪[k]ˣ →* ℂˣ) {c d : ℕ} (hc : c ∈ CS ψ) (hcd : c ≤ d) : d ∈ CS ψ := by
  intro u hu
  exact hc u (Ideal.pow_le_pow_right hcd hu)

theorem CS_inv (ψ : 𝒪[k]ˣ →* ℂˣ) : CS ψ⁻¹ = CS ψ := by
  ext c
  simp only [CS, Set.mem_setOf_eq, MonoidHom.inv_apply, inv_eq_one]

theorem cond_one : cond (1 : 𝒪[k]ˣ →* ℂˣ) = 0 := by
  rw [cond_eq]
  apply Nat.sInf_eq_zero.mpr
  left
  intro u _
  rfl

theorem res_div_swap {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b : Fin s) :
    res (μ b / μ a) = (res (μ a / μ b))⁻¹ := by
  ext u
  simp [res, MonoidHom.div_apply, MonoidHom.inv_apply, inv_div]

theorem res_div_mul {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b c : Fin s) (u : 𝒪[k]ˣ) :
    res (μ a / μ c) u = res (μ a / μ b) u * res (μ b / μ c) u := by
  simp [res, MonoidHom.div_apply, div_mul_div_cancel₀]

theorem cc_self {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a : Fin s) : cc μ a a = 0 := by
  unfold cc
  rw [div_self']
  exact cond_one

theorem cc_comm {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b : Fin s) : cc μ a b = cc μ b a := by
  unfold cc
  rw [res_div_swap μ a b, cond_eq, cond_eq, CS_inv]

theorem cc_ultra {s : ℕ} (μ : Fin s → kˣ →* ℂˣ) (a b c : Fin s)
    (hab : (CS (res (μ a / μ b))).Nonempty) (hbc : (CS (res (μ b / μ c))).Nonempty) :
    cc μ a c ≤ max (cc μ a b) (cc μ b c) := by
  have h1 : cc μ a b ∈ CS (res (μ a / μ b)) := Nat.sInf_mem hab
  have h2 : cc μ b c ∈ CS (res (μ b / μ c)) := Nat.sInf_mem hbc
  have h3 : max (cc μ a b) (cc μ b c) ∈ CS (res (μ a / μ c)) := by
    intro u hu
    rw [res_div_mul μ a b c u,
      CS_mono _ h1 (le_max_left _ _) u hu, CS_mono _ h2 (le_max_right _ _) u hu, one_mul]
  exact Nat.sInf_le h3

theorem step_ccBasic_of_cond :
    ∀ (s : ℕ) (μ : Fin s → kˣ →* ℂˣ),
      (∀ a b : Fin s, ∃ c : ℕ, ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c →
        res (μ a / μ b) u = 1) →
      ∀ a b c : Fin s, cc μ a a = 0 ∧ cc μ a b = cc μ b a ∧ cc μ a c ≤ max (cc μ a b) (cc μ b c) := by
  intro s μ hμ a b c
  refine ⟨cc_self μ a, cc_comm μ a b, cc_ultra μ a b c ?_ ?_⟩
  · obtain ⟨c0, h⟩ := hμ a b
    exact ⟨c0, h⟩
  · obtain ⟨c0, h⟩ := hμ b c
    exact ⟨c0, h⟩

end CharacterConductor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step_ccBasic : CompactConductorBasicProp (k := k) :=
  CharacterConductor.step_ccBasic_of_cond

end Grp

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CharacterConductorBound
section
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace Grp

namespace CharacterConductorBound

def Lv (ψ : 𝒪[k]ˣ →* ℂˣ) : Set ℕ :=
  {c | ∀ u : 𝒪[k]ˣ, (u : 𝒪[k]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ c → ψ u = 1}

theorem exists_level (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) : (Lv (res μ)).Nonempty := by
  have hopen : IsOpen (μ.ker : Set kˣ) := hμ
  obtain ⟨V, hVo, hV⟩ := (Units.isEmbedding_val₀ (G₀ := k)).isInducing.isOpen_iff.mp hopen
  have h1 : (1 : k) ∈ V := by
    have : (1 : kˣ) ∈ (Units.val ⁻¹' V) := by rw [hV]; exact μ.ker.one_mem
    simpa using this
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_iff' (R := k)).mp (hVo.mem_nhds h1)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have hlt : valuation k (algebraMap 𝒪[k] k ϖ) < 1 :=
    (Valuation.integer.integers (valuation k)).valuation_irreducible_lt_one hϖ
  have : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨c, hc⟩ := exists_pow_lt₀ hlt γ
  refine ⟨c, fun u hu => ?_⟩
  have hm : IsLocalRing.maximalIdeal 𝒪[k] = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hu
  obtain ⟨t, ht⟩ := hu
  have e : ((u : 𝒪[k]) : k) - 1 = (algebraMap 𝒪[k] k ϖ) ^ c * algebraMap 𝒪[k] k t := by
    have := congrArg (algebraMap 𝒪[k] k) ht
    simp only [map_sub, map_mul, map_pow, map_one] at this
    exact this
  have ht1 : valuation k (algebraMap 𝒪[k] k t) ≤ 1 := t.2
  have hv : valuation k (((u : 𝒪[k]) : k) - 1) < γ := by
    rw [e, map_mul, map_pow]
    calc valuation k (algebraMap 𝒪[k] k ϖ) ^ c * valuation k (algebraMap 𝒪[k] k t)
        ≤ valuation k (algebraMap 𝒪[k] k ϖ) ^ c * 1 := by gcongr
      _ < γ := by rw [mul_one]; exact hc
  have hmem : unitIncl k u ∈ (Units.val ⁻¹' V : Set kˣ) := hγ hv
  rw [hV] at hmem
  exact (MonoidHom.mem_ker).mp hmem

theorem max_mem (μ ν : kˣ →* ℂˣ) {c c' : ℕ} (hc : c ∈ Lv (res μ)) (hc' : c' ∈ Lv (res ν)) :
    max c c' ∈ Lv (res (μ / ν)) := by
  intro u hu
  have h1 := hc u (Ideal.pow_le_pow_right (le_max_left c c') hu)
  have h2 := hc' u (Ideal.pow_le_pow_right (le_max_right c c') hu)
  simp only [MonoidHom.comp_apply, MonoidHom.div_apply] at h1 h2 ⊢
  rw [h1, h2, div_one]

theorem cond_mem (ψ : 𝒪[k]ˣ →* ℂˣ) (h : (Lv ψ).Nonempty) : cond ψ ∈ Lv ψ := Nat.sInf_mem h

variable {n : ℕ} (G : Grp k n)

theorem lv_a (a : Fin G.s) : cond (res (G.μ a)) ∈ Lv (res (G.μ a)) :=
  cond_mem _ (exists_level _ (G.smooth a))

theorem lv_ab (a b : Fin G.s) :
    max (cond (res (G.μ a))) (cond (res (G.μ b))) ∈ Lv (res (G.μ a / G.μ b)) :=
  max_mem _ _ (lv_a G a) (lv_a G b)

theorem cc_le (a b : Fin G.s) : cc G.μ a b ≤ max (cond (res (G.μ a))) (cond (res (G.μ b))) :=
  Nat.sInf_le (lv_ab G a b)

theorem cc_mem (a b : Fin G.s) : cc G.μ a b ∈ Lv (res (G.μ a / G.μ b)) :=
  Nat.sInf_mem ⟨_, lv_ab G a b⟩

theorem cond_le_sum (a : Fin G.s) : cond (res (G.μ a)) ≤ ∑ b, cond (res (G.μ b)) :=
  Finset.single_le_sum (f := fun b => cond (res (G.μ b))) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem one_le_cc (a b : Fin G.s) (hab : a ≠ b) : 1 ≤ cc G.μ a b := by
  by_contra h0
  have h0' : cc G.μ a b = 0 := by omega
  have hm := cc_mem G a b
  rw [h0'] at hm
  apply G.dist a b hab
  ext u
  have := hm u (by simp)
  simp only [MonoidHom.comp_apply, MonoidHom.div_apply, div_eq_one] at this
  simp only [MonoidHom.comp_apply, this]

end CharacterConductorBound

theorem step_ccBound {n : ℕ} (G : Grp k n) : CompactConductorBoundProp G := by
  have hlev : G.lev = 1 + ∑ b, cond (res (G.μ b)) := rfl
  refine ⟨fun a b hab => CharacterConductorBound.one_le_cc G a b hab, fun a b => ?_, fun a => ?_,
    fun a b u hu => CharacterConductorBound.cc_mem G a b u hu⟩
  · have h1 := CharacterConductorBound.cc_le G a b
    have h2 := CharacterConductorBound.cond_le_sum G a
    have h3 := CharacterConductorBound.cond_le_sum G b
    rw [hlev]
    omega
  · have h2 := CharacterConductorBound.cond_le_sum G a
    rw [hlev]
    omega

end Grp

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.CuspidalSupport2
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.CuspidalSupport₂

variable {k : Type} [Field k]

theorem twist_detRep_one (χ η : kˣ →* ℂˣ) :
    twist (detRep (Fin 1) χ) (detChar (Fin 1) η) = detRep (Fin 1) (η * χ) := by
  have h : GlobalTheory.SmGL.detChar (Fin 1) η * GlobalTheory.SmGL.detChar (Fin 1) χ =
      GlobalTheory.SmGL.detChar (R := k) (Fin 1) (η * χ) := by
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.mul_apply, GlobalTheory.SmGL.detChar_apply]
  unfold GlobalTheory.SmGL.detRep GlobalTheory.SmGL.ofChar
  rw [GlobalTheory.SmGL.twist_twist, h]

theorem twist_twist_inv {d : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (σ : Representation ℂ (GL (Fin d) k) X) (η : kˣ →* ℂˣ) :
    twist (twist σ (detChar (Fin d) η⁻¹)) (detChar (Fin d) η) = σ := by
  have h : GlobalTheory.SmGL.detChar (Fin d) η * GlobalTheory.SmGL.detChar (Fin d) η⁻¹ =
      (1 : GL (Fin d) k →* ℂˣ) := by
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.mul_apply, GlobalTheory.SmGL.detChar_apply, MonoidHom.inv_apply,
      mul_inv_cancel, MonoidHom.one_apply]
  rw [GlobalTheory.SmGL.twist_twist, h, GlobalTheory.SmGL.twist_one]

end UpperTheory.TNZ.CuspidalSupport₂

namespace UpperTheory.TNZ

open CuspidalSupport₂ in
theorem step_cuspSupp : CuspidalSupportProp := by
  intro hL k _ _ _ _ d X _ _ σ hs hi η hη hdv
  obtain ⟨v, hv0, hv⟩ := hdv
  set τ := twist σ (detChar (Fin d) η⁻¹) with hτ
  have hτs : IsSmooth τ := isSmooth_twist hs hη.inv.detChar
  have hτi : τ.IsIrreducible := isIrreducible_twist hi _
  have hadm : IsAdmissible τ := (hL.bz k).1 (Fin d) X τ hτs hτi
  have hI : fixed τ (iwahori k (Fin d)) ≠ ⊥ := by
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    have hg := hv h.1 (iwahori_le_KO k _ h.2)
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    show (detChar (Fin d) η⁻¹ h.1 : ℂ) • σ h.1 v = v
    rw [hg, smul_smul, detChar_apply, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_smul]
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm hτi hI
  let χ : Fin d → kˣ →* ℂˣ := fun i => unrChar k (α i)
  have h1 := hα.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k d χ)
  have h2 := isSubquotient_twist h1 (detChar (Fin d) η)
  rw [hτ, twist_twist_inv] at h2
  have hχs : ∀ i, IsSmoothChar (χ i) := fun i => isSmoothChar_of_isUnram (isUnram_unrChar (k := k) (α i))
  let φ := multiProdTwistEquiv (Equiv.sigmaUnique (Fin d) fun _ => Fin 1)
    (fun i => detRep (Fin 1) (χ i)) hη
  have h3 := h2.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have hfam : (fun i => twist (detRep (Fin 1) (χ i)) (detChar (Fin 1) η)) =
      fun i => detRep (Fin 1) (η * χ i) := funext fun i => twist_detRep_one _ _
  rw [hfam] at h3
  refine ⟨fun j => η * χ j, fun j => ⟨hη.mul (hχs j), fun u hu => ?_⟩, hi,
    fun j => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hη.mul (hχs j))⟩, _, h3⟩
  show η u * unrChar k (α j) u = η u
  rw [isUnram_unrChar (k := k) (α j) u hu, mul_one]

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.DeterminantVector
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace DeterminantVector

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem mem_fixed_iff {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (K : Subgroup (GL (Fin N) k)) (v : V) :
    v ∈ fixed ρ K ↔ ∀ g ∈ K, ρ g v = v := by
  constructor
  · intro h g hg
    simpa using h ⟨g, hg⟩
  · intro h g
    simpa using h g g.2


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem hasDetVec_twist {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (η : kˣ →* ℂˣ) (h : IsSpherical ρ) :
    HasDetVec (twist ρ (detChar (Fin N) η)) η := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h
  refine ⟨v, hv0, fun g hg => ?_⟩
  rw [twist_apply, detChar_apply, (mem_fixed_iff ρ _ v).1 hv g hg]


omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem isSpherical_twist {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin N) k) V) (η : kˣ →* ℂˣ) (h : HasDetVec ρ η) :
    IsSpherical (twist ρ (detChar (Fin N) η⁻¹)) := by
  obtain ⟨v, hv0, hv⟩ := h
  refine (Submodule.ne_bot_iff _).2 ⟨v, ?_, hv0⟩
  refine (mem_fixed_iff _ _ v).2 fun g hg => ?_
  rw [twist_apply, detChar_apply, hv g hg, smul_smul, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul]

end DeterminantVector

theorem step_detVec : DeterminantVectorProp := by
  intro k _ _ _ _ N V _ _ ρ η
  exact ⟨DeterminantVector.hasDetVec_twist ρ η, DeterminantVector.isSpherical_twist ρ η⟩

end UpperTheory.TNZ
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.FiniteDimensionalTranslationCoordinates
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.NonzeroTypeTheory

def Need_CMain : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ρ.IsIrreducible →
    (∃ x : V, x ≠ 0 ∧ ∀ g ∈ G.JSet, ρ g x = G.lam g • x) → IsTwSphProd ρ G.d G.hd G.μ

def Need_CProps : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n),
    G.JSet ⊆ KO k (Fin n) ∧ (1 : GL (Fin n) k) ∈ G.JSet ∧
    (∀ g ∈ G.JSet, ∀ g' ∈ G.JSet, g * g' ∈ G.JSet ∧ G.lam (g * g') = G.lam g * G.lam g') ∧
    (∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) ∧ (∀ g ∈ G.JSet, G.lam g ≠ 0) ∧
    IsOpen (KC k n G.lev) ∧ (1 : GL (Fin n) k) ∈ KC k n G.lev ∧ KC k n G.lev ⊆ G.JSet ∧ (∀ g ∈ KC k n G.lev, G.lam g = 1) ∧
    (∀ φ ∈ G.V0sp, ∀ k' : ↥(KO k (Fin n)), rightReg ℂ ↥(KO k (Fin n)) ℂ k' φ ∈ G.V0sp) ∧ FiniteDimensional ℂ G.V0sp ∧
    G.v0 ∈ G.V0sp ∧ G.v0 ≠ 0 ∧
    ∀ j : ↥(KO k (Fin n)), (j : GL (Fin n) k) ∈ G.JSet → rightReg ℂ ↥(KO k (Fin n)) ℂ j G.v0 = G.lam j • G.v0

def Need_Grp : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (μ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (μ i)) →
    ∃ (G : Grp k n) (σ : Fin n ≃ Fin n), ∀ i, res (G.chi i) = res (μ (σ i))

def ArtinTransferDecompositionCharacter : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
    ∀ (n : ℕ) (χ : Fin n → Dec (F := E) A →* ℂˣ), (∀ i, IsOpen ((χ i).ker : Set (Dec (F := E) A))) →
      ∃ μ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ, (∀ i, IsSmoothChar (μ i)) ∧
        ∀ i (σ : Weil h), χ i (Subgroup.inclusion (Weil_le_Dec h) σ) = μ i (a σ)

def LocalArtinCharacterProduct : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
    ∀ (n : ℕ) (χ : Fin n → Dec (F := E) A →* ℂˣ) (ho : ∀ i, IsOpen ((χ i).ker : Set (Dec (F := E) A)))
      (μ : Fin n → (w.adicCompletion E)ˣ →* ℂˣ), (∀ i (σ : Weil h), χ i (Subgroup.inclusion (Weil_le_Dec h) σ) = μ i (a σ)) →
      ∀ (G : Grp (w.adicCompletion E) n) (σ : Fin n ≃ Fin n), (∀ i, res (G.chi i) = res (μ (σ i))) →
        ∀ s : ↥(Ine (F := E) A), (xOf h χ ho).charPol (ineIncl h s) =
          ∏ b, (X - C (((G.μ b (a (ineIncl h s))) : ℂˣ) : ℂ)) ^ G.d b

def FiniteDimensionalTranslationCoordinates : Prop :=
  ∀ (K : Type) [Group K] [TopologicalSpace K] (W : Submodule ℂ (K → ℂ)), FiniteDimensional ℂ W →
    (∀ φ ∈ W, ∀ k : K, rightReg ℂ K ℂ k φ ∈ W) → (∀ φ ∈ W, IsOpen {k : K | rightReg ℂ K ℂ k φ = φ}) →
    ∃ (m : ℕ) (V0 : Representation ℂ K (Fin m → ℂ)) (e : (Fin m → ℂ) →ₗ[ℂ] (K → ℂ)),
      Function.Injective e ∧ LinearMap.range e = W ∧ (∀ k v, e (V0 k v) = rightReg ℂ K ℂ k (e v)) ∧ IsSmooth V0

def TwistedSphericalRepresentative : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V) (h1 : IsSmooth ρ) (h2 : ρ.IsIrreducible)
    (s : ℕ) (d : Fin s → ℕ) (hd : ∑ a, d a = n) (η : Fin s → kˣ →* ℂˣ),
    IsTwSphProd (IrrGL.of ρ h1 h2).rep d hd η ↔ IsTwSphProd ρ d hd η

def DistinctOnUnitsDistinctOnInertia : Prop :=
  ArtinInertiaProp →
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a →
    ∀ (n : ℕ) (G : Grp (w.adicCompletion E) n) (b c : Fin G.s), b ≠ c →
      ∃ t : ↥(Ine (F := E) A), G.μ b (a (ineIncl h t)) ≠ G.μ c (a (ineIncl h t))

def SmoothVectorsFixedByCongruence : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (G : Grp k n),
    IsOpen (KC k n G.lev) → (1 : GL (Fin n) k) ∈ KC k n G.lev →
    ∀ φ ∈ G.V0sp, IsOpen {k' : ↥(KO k (Fin n)) | rightReg ℂ ↥(KO k (Fin n)) ℂ k' φ = φ}

end UpperTheory.NonzeroTypeTheory
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PTwistRc
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.TNZ

theorem step_twistRc : TwistRestrictionProp := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc H d X _ _ σ hs hi η hη
  refine ⟨isSmooth_twist hs hη.detChar, isIrreducible_twist hi _, ?_⟩
  rw [← IrrGL.tw_of (hχ := hη), H.twist, H.one]

end UpperTheory.TNZ
end
end

