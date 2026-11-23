module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmStar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0121
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0122

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdditiveFamilyFunctionDeterminedConstituents
section
noncomputable section

open scoped TensorProduct
open GlobalTheory.PRep GlobalTheory.JHMult

namespace GlobalTheory.SmGL

namespace AdditiveExpand

variable {G : Type} [Group G] [TopologicalSpace G]


open Classical in
theorem jhMult_rep_rep (c d : IrrCl G) : jhMult c.rep.ρ d.rep.ρ = if c = d then 1 else 0 := by
  split_ifs with h
  · subst h; exact jhMult_self c.rep.irr
  · by_contra h0
    obtain ⟨φ⟩ := (jhMult_ne_zero_iff.1 h0).nonempty_equiv c.rep.irr d.rep.irr
    exact h (c.cl_rep.symm.trans ((IrrRep.cl_eq_iff.2 ⟨φ.symm⟩).trans d.cl_rep))

variable (φ : SmRep G → ℕ∞) (h0 : ∀ B : SmRep G, Subsingleton B.V → φ B = 0)
  (hadd : ∀ (B B₁ B₂ : SmRep G) (ι : B₁.ρ.IntertwiningMap B.ρ) (p : B.ρ.IntertwiningMap B₂.ρ),
    Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) →
      (∀ v, p v = 0 → ∃ u, ι u = v) → φ B = φ B₁ + φ B₂)

variable [IsTopologicalGroup G]

def sub (B : SmRep G) (S : Subrepresentation B.ρ) : SmRep G :=
  ⟨S.toSubmodule, S.toRepresentation,
    IsSubquotient.isSmooth ⟨S, .id _, Function.surjective_id⟩ B.smooth⟩

def quo (B : SmRep G) (S T : Subrepresentation B.ρ) : SmRep G :=
  ⟨_, subQuot S T, IsSubquotient.isSmooth
    ⟨S, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.Quotient.mk_surjective _⟩ B.smooth⟩

include h0 hadd

theorem congr_equiv {B B' : SmRep G} (e : B.ρ.Equiv B'.ρ) : φ B = φ B' := by
  have hs : Subsingleton (sub B ⊥).V := inferInstanceAs (Subsingleton (⊥ : Submodule ℂ B.V))
  have := hadd B (sub B ⊥) B' ⟨Submodule.subtype _, fun _ => rfl⟩ e.toIntertwiningMap
    Subtype.val_injective e.surjective
    (fun u => by rw [Subsingleton.elim u 0, map_zero, map_zero])
    (fun v hv => ⟨0, by
      rw [map_zero]
      exact (e.injective (hv.trans (map_zero e).symm)).symm⟩)
  rw [this, h0 _ hs, zero_add]

theorem one_coord₂ (B : SmRep G) (h : HasFiniteLength B.ρ) (T : Finset (IrrCl G))
    (hT : ∀ c ∉ T, jhMult c.rep.ρ B.ρ = 0) :
    φ B = ∑ c ∈ T, jhMult c.rep.ρ B.ρ * φ (SmRep.ofIrr c.rep) := by
  classical
  have ψ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := B.ρ)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  have : WellFoundedGT (Subrepresentation B.ρ) := ψ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation B.ρ) := ψ.toOrderEmbedding.wellFoundedLT
  have key : ∀ S : Subrepresentation B.ρ, (∀ c ∉ T, jhMult c.rep.ρ S.toRepresentation = 0) →
      φ (sub B S) = ∑ c ∈ T, jhMult c.rep.ρ S.toRepresentation * φ (SmRep.ofIrr c.rep) := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    intro hS'
    rcases eq_or_ne S ⊥ with rfl | hS
    · have hs : Subsingleton (⊥ : Subrepresentation B.ρ).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ B.V))
      rw [h0 _ hs]
      exact (Finset.sum_eq_zero fun c _ => by
        rw [jhMult_of_subsingleton c.rep.irr, zero_mul]).symm
    obtain ⟨R, -, hR⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hS)
    let σ : IrrRep G := ⟨_, subQuot S R, (quo B S R).smooth, isIrreducible_subQuot hR⟩
    obtain ⟨e⟩ := σ.nonempty_equiv_rep
    have hm : ∀ c : IrrCl G, jhMult c.rep.ρ S.toRepresentation =
        jhMult c.rep.ρ R.toRepresentation + if c = σ.cl then 1 else 0 := fun c => by
      rw [jhMult_of_le c.rep.irr hR.le, ← jhMult_rep_rep, jhMult_congr_right _ e]
    have hp : ∀ v : S.toSubmodule, (Submodule.Quotient.mk v : (quo B S R).V) = 0 ↔
        v.1 ∈ R.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have h1 := hadd (sub B S) (sub B R) (quo B S R) ⟨Submodule.inclusion hR.le, fun _ => rfl⟩
      ⟨Submodule.mkQ _, fun _ => rfl⟩ (Submodule.inclusion_injective hR.le)
      (Submodule.Quotient.mk_surjective _) (fun u => (hp _).2 u.2)
      fun v hv => ⟨⟨v.1, (hp v).1 hv⟩, rfl⟩
    have h2 : φ (quo B S R) = φ (SmRep.ofIrr σ.cl.rep) :=
      (congr_equiv φ h0 hadd (B := SmRep.ofIrr σ.cl.rep) (B' := quo B S R) e).symm
    have h3 : σ.cl ∈ T := by
      by_contra hn
      have := hS' _ hn
      rw [hm] at this
      simp at this
    rw [h1, h2, ih R hR.lt fun c hc => (add_eq_zero.1 ((hm c).symm.trans (hS' c hc))).1]
    simp only [hm, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', if_pos h3]
  have h4 := key ⊤ (by simpa only [jhMult_congr_right _ (topEquiv B.ρ)] using hT)
  rw [← congr_equiv φ h0 hadd (B := sub B ⊤) (B' := B) (topEquiv B.ρ), h4]
  simp only [jhMult_congr_right _ (topEquiv B.ρ)]

end AdditiveExpand


open AdditiveExpand in
theorem additive_family_expand : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ i, Group (Γ i)] [∀ i, TopologicalSpace (Γ i)] [∀ i, IsTopologicalGroup (Γ i)] (Φ : (∀ i, GlobalTheory.SmGL.SmRep (Γ i)) → ℕ∞), (∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α), Subsingleton (A i).V → Φ A = 0) → (∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α) (B B₁ B₂ : GlobalTheory.SmGL.SmRep (Γ i)) (ι : B₁.ρ.IntertwiningMap B.ρ) (p : B.ρ.IntertwiningMap B₂.ρ), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → Φ (Function.update A i B) = Φ (Function.update A i B₁) + Φ (Function.update A i B₂)) → ∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)), (∀ i, GlobalTheory.SmGL.HasFiniteLength (A i).ρ) → ∀ T : Finset (∀ i, GlobalTheory.SmGL.IrrCl (Γ i)), (∀ t ∉ T, ∃ i, GlobalTheory.SmGL.jhMult (t i).rep.ρ (A i).ρ = 0) → Φ A = ∑ t ∈ T, (∏ i, GlobalTheory.SmGL.jhMult (t i).rep.ρ (A i).ρ) * Φ (fun i => GlobalTheory.SmGL.SmRep.ofIrr (t i).rep) := by
  intro α _ _ Γ _ _ _ Φ h0 hadd
  classical
  have key : ∀ s : Finset α, ∀ A : ∀ i, SmRep (Γ i),
      (∀ i ∉ s, ∃ c : IrrCl (Γ i), A i = SmRep.ofIrr c.rep) → (∀ i, HasFiniteLength (A i).ρ) →
      ∀ T : Finset (∀ i, IrrCl (Γ i)), (∀ t ∉ T, ∃ i, jhMult (t i).rep.ρ (A i).ρ = 0) →
      Φ A = ∑ t ∈ T, (∏ i, jhMult (t i).rep.ρ (A i).ρ) * Φ (fun i => SmRep.ofIrr (t i).rep) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro A hA _ T hT
      choose c hc using fun i => hA i (Finset.notMem_empty i)
      obtain rfl : A = fun i => SmRep.ofIrr (c i).rep := funext hc
      have hm : ∀ t : ∀ i, IrrCl (Γ i),
          (∏ i, jhMult (t i).rep.ρ (SmRep.ofIrr (c i).rep).ρ) = if t = c then 1 else 0 := fun t => by
        have : ∀ i, jhMult (t i).rep.ρ (SmRep.ofIrr (c i).rep).ρ = if t i = c i then 1 else 0 :=
          fun i => jhMult_rep_rep _ _
        simp only [this, Finset.prod_ite_zero, Finset.prod_const_one, Finset.mem_univ,
          forall_const, funext_iff]
      have h3 : c ∈ T := by
        by_contra hn
        obtain ⟨i, hi⟩ := hT c hn
        exact one_ne_zero ((jhMult_self (c i).rep.irr).symm.trans hi)
      simp only [hm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', if_pos h3]
    | insert i s his ih =>
      intro A hA hl T hT
      let μ : ∀ j, IrrCl (Γ j) → SmRep (Γ j) → ℕ∞ := fun j c B => jhMult c.rep.ρ B.ρ
      have hC := finite_constituents (hl i)
      have h1 := one_coord₂ (fun B => Φ (Function.update A i B))
        (fun B hB => h0 _ i (by rw [Function.update_self]; exact hB)) (hadd A i) (A i) (hl i)
        hC.toFinset (fun c hc => by simpa using hc)
      simp only [Function.update_eq_self] at h1
      have h2 : ∀ c ∈ hC.toFinset, Φ (Function.update A i (SmRep.ofIrr c.rep)) =
          ∑ t ∈ T, ((if t i = c then 1 else 0) * ∏ j ∈ Finset.univ.erase i, μ j (t j) (A j)) *
            Φ (fun i => SmRep.ofIrr (t i).rep) := by
        intro c hc
        rw [ih (Function.update A i (SmRep.ofIrr c.rep)) ?_ ?_ T ?_]
        · refine Finset.sum_congr rfl fun t _ => ?_
          congr 1
          change ∏ j, μ j (t j) (Function.update A i (SmRep.ofIrr c.rep) j) = _
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
          congr 1
          · exact jhMult_rep_rep _ _
          · exact Finset.prod_congr rfl fun j hj => by
              rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        · intro j hj
          rcases eq_or_ne j i with rfl | hji
          · exact ⟨c, Function.update_self ..⟩
          · rw [Function.update_of_ne hji]
            exact hA j (by simp [hji, hj])
        · intro j
          rcases eq_or_ne j i with rfl | hji
          · rw [Function.update_self]; exact c.rep.hasFiniteLength
          · rw [Function.update_of_ne hji]; exact hl j
        · intro t ht
          obtain ⟨j, hj⟩ := hT t ht
          refine ⟨j, ?_⟩
          change μ j (t j) (Function.update A i (SmRep.ofIrr c.rep) j) = 0
          rcases eq_or_ne j i with rfl | hji
          · rw [Function.update_self]
            refine (jhMult_rep_rep _ _).trans (if_neg ?_)
            rintro rfl
            exact (hC.mem_toFinset.1 hc) hj
          · rw [Function.update_of_ne hji]; exact hj
      rw [h1, Finset.sum_congr rfl fun c hc => by rw [h2 c hc, Finset.mul_sum], Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      change _ = (∏ j, μ j (t j) (A j)) * _
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq]
      split_ifs with h
      · exact (mul_assoc _ _ _).symm
      · have : μ i (t i) (A i) = 0 := by simpa using h
        rw [this, zero_mul, zero_mul]
  exact fun A hl T hT => key Finset.univ A (fun i hi => absurd (Finset.mem_univ i) hi) hl T hT

end GlobalTheory.SmGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrientedHeis

theorem compAt_mt_of_mem_GfC {D : D7} (θ : InfFam D) (V : HSp D) {k : GA D V} (hk : k ∈ GfC V) (τ : D.what₂.Tau) :
    compAt θ τ (Formalism.L2.Theta.mt V k) = 1 := by
  rw [GfC, MonoidHom.mem_ker] at hk
  unfold compAt Formalism.L2.Theta.mt
  unfold infHom at hk
  unfold infPart
  rw [MonoidHom.comp_apply] at hk
  have e := congrArg (fun g => (Units.val g).map (θ τ)) hk
  simp only [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)] at e
  rw [← e]
  rfl

theorem om_fin_pureTensorO : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ κ ∈ GfC S, ∀ κ' ∈ GfC T, ∀ sS sT BS BT f P, IsThetaFunO ψ S T f → om (κ, κ') (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS sT BS BT (om (κ, κ') f) P := by
  intro D ψ S T χS χT om hW θ hθ κ hκ κ' hκ' sS sT BS BT f P hf
  have h1 := fun τ => compAt_mt_of_mem_GfC θ S hκ τ
  have h2 := fun τ => compAt_mt_of_mem_GfC θ T hκ' τ
  have := (om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT κ κ' (fun τ => by rw [h1 τ, one_mul, mul_one]) (fun τ => by rw [h2 τ, one_mul, mul_one]) (fun τ => by rw [h1 τ, one_mul]) (fun τ => by rw [h2 τ, one_mul]) f hf P).2
  exact this

end GlobalTheory.OrientedHeis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpace
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjMult

section Rep

variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

def realEquiv (c : H' ≃ₗᵢ⋆[ℂ] H) : H' ≃L[ℝ] H where
  toFun := c
  invFun := c.symm
  map_add' := map_add c
  map_smul' r x := by
    rw [← Complex.coe_smul, map_smulₛₗ]
    simp
  left_inv := c.symm_apply_apply
  right_inv := c.apply_symm_apply
  continuous_toFun := c.continuous
  continuous_invFun := c.symm.continuous

theorem expProd_mem (hJ : IsUnit J.det) {k : ℕ} {Xs : Fin k → Matrix (Fin n) (Fin n) ℂ}
    (hX : ∀ i, (Xs i)ᴴ * J + J * Xs i = 0) (t : Fin k → ℝ) :
    (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod ∈ Formalism.QuantumDeterminants.UH J := by
  refine List.prod_induction _ (fun a b => mul_mem_UH J) (one_mem_UH J) fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact GlobalTheory.SmoothAutCheck.exp_mem_UH hJ (hX i) _

theorem smoothVec_conj (hJ : IsUnit J.det) (c : H' ≃ₗᵢ⋆[ℂ] H)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, c (σ' g w) = σ g (c w)) {w : H'}
    (hw : SmoothVec {X | Xᴴ * J + J * X = 0} σ' w) : SmoothVec {X | Xᴴ * J + J * X = 0} σ (c w) := by
  intro k Xs hX
  have := (realEquiv c).contDiff.comp (hw k Xs hX)
  convert this using 2 with t
  exact (hc _ (expProd_mem hJ hX t) w).symm

theorem span_conj (hJ : IsUnit J.det) (c : H' ≃ₗᵢ⋆[ℂ] H)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, c (σ' g w) = σ g (c w)) {w : H'}
    (hw : w ∈ Submodule.span ℂ {w | SmoothVec {X | Xᴴ * J + J * X = 0} σ' w}) :
    c w ∈ Submodule.span ℂ {w | SmoothVec {X | Xᴴ * J + J * X = 0} σ w} := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (smoothVec_conj hJ c hc hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

theorem dRep_conj (hJ : IsUnit J.det) (c : H' ≃ₗᵢ⋆[ℂ] H)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, c (σ' g w) = σ g (c w)) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : Xᴴ * J + J * X = 0) (w : H') : dRep σ X (c w) = c (dRep σ' X w) := by
  have e : (fun t : ℝ => σ (NormedSpace.exp (t • X)) (c w)) =
      realEquiv c ∘ fun t : ℝ => σ' (NormedSpace.exp (t • X)) w :=
    funext fun t => (hc _ (GlobalTheory.SmoothAutCheck.exp_mem_UH hJ hX t) w).symm
  rw [dRep, e, deriv, ContinuousLinearEquiv.comp_fderiv]
  rfl

theorem sobCont_conj (hJ : IsUnit J.det) (c : H' ≃ₗᵢ⋆[ℂ] H)
    (hc : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ w, c (σ' g w) = σ g (c w)) {ℓ : H →ₗ[ℂ] ℂ}
    (h : Sobolev₂ {X | Xᴴ * J + J * X = 0} σ ℓ) :
    ∃ ℓ' : H' →ₗ[ℂ] ℂ, Sobolev₂ {X | Xᴴ * J + J * X = 0} σ' ℓ' ∧ ∀ w, ℓ' w = star (ℓ (c w)) := by
  obtain ⟨S, C, hS, hC⟩ := h
  refine ⟨{ toFun := fun w => star (ℓ (c w))
            map_add' := fun x y => by simp
            map_smul' := fun a x => by rw [map_smulₛₗ, map_smul]; simp }, ⟨S, C, hS, fun w hw => ?_⟩, fun _ => rfl⟩
  have e : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, Xᴴ * J + J * X = 0) →
      l.foldr (dRep σ) (c w) = c (l.foldr (dRep σ') w) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons X l ih =>
      intro hl
      rw [List.foldr_cons, ih fun Y hY => hl Y (List.mem_cons_of_mem _ hY), dRep_conj hJ c hc (hl X List.mem_cons_self),
        List.foldr_cons]
  have h1 := hC _ (smoothVec_conj hJ c hc hw)
  have h2 : (S.map fun l => ‖l.foldr (dRep σ) (c w)‖) = S.map fun l => ‖l.foldr (dRep σ') w‖ :=
    List.map_congr_left fun l hl => by rw [e l (hS l hl), c.norm_map]
  rw [h2] at h1
  exact (norm_star _).trans_le h1

theorem prod_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g.det) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    l.prod * g = g * (l.map fun a => g⁻¹ * a * g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, mul_assoc, ih]
    simp only [mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hg]

theorem smoothVec_act (hJ : IsUnit J.det)
    (hm : ∀ g ∈ Formalism.QuantumDeterminants.UH J, ∀ g' ∈ Formalism.QuantumDeterminants.UH J, ∀ w, σ (g * g') w = σ g (σ g' w))
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH J) {w : H}
    (hw : SmoothVec {X | Xᴴ * J + J * X = 0} σ w) : SmoothVec {X | Xᴴ * J + J * X = 0} σ (σ g w) := by
  intro k Xs hX
  have hu := isUnit_of_UH hJ hg
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hi : (g⁻¹)ᴴ * J * g⁻¹ = J := by
    have : (hu.unit⁻¹).1 ∈ Formalism.QuantumDeterminants.UH J := (UG J).inv_mem (x := hu.unit) hg
    rwa [Matrix.coe_units_inv] at this
  have hg' : gᴴ * J * g = J := hg
  have hX' : ∀ i, (g⁻¹ * Xs i * g)ᴴ * J + J * (g⁻¹ * Xs i * g) = 0 := fun i => by
    have h1 : (g⁻¹)ᴴ * J = J * g := by
      conv_rhs => rw [← hi]
      rw [Matrix.nonsing_inv_mul_cancel_right _ _ hd]
    have h2 : J * g⁻¹ = gᴴ * J := by
      conv_lhs => rw [← hg']
      rw [Matrix.mul_nonsing_inv_cancel_right _ _ hd]
    have h3 : (Xs i)ᴴ * J + J * Xs i = 0 := hX i
    calc _ = gᴴ * (Xs i)ᴴ * ((g⁻¹)ᴴ * J) + J * g⁻¹ * Xs i * g := by
          simp only [Matrix.conjTranspose_mul, mul_assoc]
      _ = gᴴ * ((Xs i)ᴴ * J + J * Xs i) * g := by rw [h1, h2]; simp only [mul_add, add_mul, mul_assoc]
      _ = 0 := by rw [h3, mul_zero, zero_mul]
  have := ((σ g).restrictScalars ℝ).contDiff.comp (hw k _ hX')
  convert this using 2 with t
  change _ = σ g (σ _ w)
  rw [← hm _ (expProd_mem hJ hX t) _ hg, ← hm _ hg _ (expProd_mem hJ hX' t), prod_conj hd, List.map_ofFn]
  congr 5
  funext i
  rw [Function.comp_apply, ← Matrix.exp_conj' _ _ hu, mul_smul_comm, smul_mul_assoc]

end Rep

variable {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar}

theorem rep_one (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ) : M.rep τ 1 w = w := by
  have h1 : M.σ τ 1 = 1 := (M.ds τ).2.2.1.1.1
  rw [DSModel.rep, mul_one, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)), h1]
  rfl

theorem rep_mul (M : DSModel V S) (τ : D.what₂.Tau) : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
    ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, M.rep τ (g * g') w = M.rep τ g (M.rep τ g' w) := by
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have key : ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ UJset (M.ε τ) := fun g hg => by
    have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
    rw [← M.fr_gram τ] at hg'
    change _ * _ * _ = _
    calc _ = ((M.fr τ)⁻¹)ᴴ * (gᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * g) * (M.fr τ)⁻¹ := by
          simp only [Matrix.conjTranspose_mul, mul_assoc]
      _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          rw [hg']; simp only [Matrix.conjTranspose_mul, mul_assoc]
      _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp
  intro g hg g' hg' w
  have h := (M.ds τ).2.2.1.1.2 _ (key g hg) _ (key g' hg')
  have e : M.fr τ * (g * g') * (M.fr τ)⁻¹ = (M.fr τ * g * (M.fr τ)⁻¹) * (M.fr τ * g' * (M.fr τ)⁻¹) := by
    simp only [mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hd]
  rw [DSModel.rep, e, h]
  rfl

theorem rep_mem_sm (M : DSModel V S) (τ : D.what₂.Tau) {g : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) {w : M.H τ} (hw : w ∈ M.sm τ) : M.rep τ g w ∈ M.sm τ := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    exact Submodule.subset_span (smoothVec_act (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (rep_mul M τ) hg hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem value_mem_homFun {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} {T : MMap M}
    (h : IsMultMap θ M J χ T) (v : M.Vec) : T v ∈ homFun θ V := by
  classical
  have h1 : ∀ y ∈ realMon θ V, ∀ v, ∃ v', ∀ x, T v (x * y) = T v' x := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem y hy =>
      obtain ⟨τ, g, hg, rfl⟩ := hy
      intro v
      exact ⟨_, fun x => (congrFun (h.equiv τ g hg v ⟨_, rep_mem_sm M τ hg (v τ).2⟩ rfl) x).symm⟩
    | one => exact fun v => ⟨v, fun x => by rw [mul_one]⟩
    | mul a b _ _ ha hb =>
      intro v
      obtain ⟨v₁, h₁⟩ := hb v
      obtain ⟨v₂, h₂⟩ := ha v₁
      exact ⟨v₂, fun x => by rw [← mul_assoc, h₁, h₂]⟩
  intro y hy τ x
  obtain ⟨u, hu⟩ := h1 y hy v
  simp only [hu]
  refine ⟨?_, fun g hg g' hg' => ?_⟩
  · have := congrFun (h.equiv τ 1 (one_mem_UH _) u (u τ) (rep_one M τ _).symm) x
    rw [Function.update_eq_self] at this
    exact this.symm
  · have a1 := congrFun (h.equiv τ g' hg' u ⟨_, rep_mem_sm M τ hg' (u τ).2⟩ rfl) (x * atTau θ V τ g)
    have a2 := congrFun (h.equiv τ (g * g') (mul_mem_UH _ hg hg') u ⟨_, rep_mem_sm M τ (mul_mem_UH _ hg hg') (u τ).2⟩ rfl) x
    have a3 := congrFun (h.equiv τ g hg (Function.update u τ ⟨_, rep_mem_sm M τ hg' (u τ).2⟩)
      ⟨_, rep_mem_sm M τ (mul_mem_UH _ hg hg') (u τ).2⟩ (by rw [Function.update_self]; exact rep_mul M τ g hg g' hg' _)) x
    rw [Function.update_idem] at a3
    exact a1.symm.trans (a3.symm.trans a2)

theorem conj_mult : ∀ {D : D7} {V : HSp D} {S S' : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (M' : DSModel V S') (c : ∀ τ, M'.H τ ≃ₗᵢ⋆[ℂ] M.H τ), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ w, c τ (M'.rep τ g w) = M.rep τ g (c τ w)) → (∀ τ (w : M'.H τ), w ∈ M'.sm τ ↔ c τ w ∈ M.sm τ) ∧ ∀ J χ, ∀ T ∈ Mult θ M J χ, ∃ T' ∈ Mult θ M' J (fun k => star (χ k)), ∀ (v' : M'.Vec) (v : M.Vec), (∀ τ, (v τ : M.H τ) = c τ (v' τ)) → ∀ g, T' v' g = star (T v g) := by
  intro D V S S' θ M M' c hc
  classical
  have hs : ∀ τ {w : M'.H τ}, w ∈ M'.sm τ → c τ w ∈ M.sm τ := fun τ _ hw =>
    span_conj (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (c τ) (hc τ) hw
  refine ⟨fun τ w => ⟨hs τ, fun hw => ?_⟩, fun J χ T hT => ?_⟩
  · have := span_conj (σ := M'.rep τ) (σ' := M.rep τ) (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (c τ).symm
      (fun g hg w => (c τ).injective (by rw [hc τ g hg, (c τ).apply_symm_apply, (c τ).apply_symm_apply])) hw
    rwa [(c τ).symm_apply_apply] at this
  have h := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ T).1 hT
  let cs : ∀ τ, M'.sm τ → M.sm τ := fun τ w => ⟨c τ w, hs τ w.2⟩
  let cv : M'.Vec → M.Vec := fun v τ => cs τ (v τ)
  have hup : ∀ [DecidableEq D.what₂.Tau] (v : M'.Vec) τ w, cv (Function.update v τ w) = Function.update (cv v) τ (cs τ w) :=
    fun v τ w => funext fun ρ => Function.apply_update cs v τ w ρ
  let T' : MMap M' :=
    { toFun := fun v => star (T (cv v))
      map_update_add' := fun v τ x y => by
        have : cs τ (x + y) = cs τ x + cs τ y := Subtype.ext (map_add (c τ) _ _)
        rw [hup, hup, hup, this, T.map_update_add, star_add]
      map_update_smul' := fun v τ a x => by
        have : cs τ (a • x) = star a • cs τ x := Subtype.ext (map_smulₛₗ (c τ) _ _)
        rw [hup, hup, this, T.map_update_smul, star_smul]
        simp only [RingHom.id_apply, star_star] }
  have hT' : ∀ v, T' v = star (T (cv v)) := fun _ => rfl
  refine ⟨T', Submodule.subset_span ⟨fun v => isAutFunSm_star (h.aut _) (value_mem_homFun h _), fun v => ?_,
    fun v k hk g => ?_, fun τ g hg v w hw => ?_, fun τ v x => ?_⟩, fun v' v hv g => ?_⟩
  · intro r C hC μ 𝓕 hμ h𝓕 g
    have := h.cusp (cv v) r C hC μ 𝓕 hμ h𝓕 g
    change ∫ n in 𝓕, starRingEnd ℂ (T (cv v) ((n : GA D V) * g)) ∂μ = 0
    rw [integral_conj, this, map_zero]
  · rw [hT', Pi.star_apply, Pi.star_apply, h.lev _ k hk, star_mul']
  · rw [hT', hT', hup, h.equiv τ g hg (cv v) (cs τ w) (by change c τ w = _; rw [hw, hc τ g hg])]
    rfl
  · obtain ⟨ℓ, h1, h2⟩ := h.cont τ (cv v) x
    obtain ⟨ℓ', h3, h4⟩ := sobCont_conj (GlobalTheory.SmoothAutCheck.gramAt_unit V τ) (c τ) (hc τ) h1
    refine ⟨ℓ', h3, fun w => ?_⟩
    rw [h4, hT', hup, Pi.star_apply, ← h2]
  · have : cv v' = v := funext fun τ => Subtype.ext (hv τ).symm
    rw [hT', this, Pi.star_apply]

end GlobalTheory.ConjMult

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjStableInverseDifferentAndNormIdealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) ((D.host.ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ * D.host.AA * D.host.AAbar) := by
  first | exact @GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal | exact GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal | (intros; apply GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLineDecompositionsOfBaseSpaceProofStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normLineDecompositionsOfBaseSpace_proof : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RecordDecSt D := by
  first | exact @GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec | exact GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec | (intros; apply GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec <;> assumption)
end

