module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodLatticeCountable
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0025
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087

@[expose] public section

noncomputable section
namespace GlobalTheory.OneEmbeddingProbe
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem invFun_relab_injective (c : Coeff l) (σ : c.F →+* ℂ) :
    Function.Injective (Function.invFun (relab (E := E) c σ)) := by
  have hi : Function.Injective (relab (E := E) c σ) := by
    intro τ τ' h
    ext a
    have := σ.injective (RingHom.congr_fun h a)
    exact congrArg Subtype.val this
  exact (Function.rightInverse_invFun (Finite.injective_iff_surjective.1 hi)).injective

theorem conjEmb_inj {τ τ' : E →+* ℂ} (h : conjEmb τ = conjEmb τ') : τ = τ' := by
  ext a
  exact (starRingEnd ℂ).injective (RingHom.congr_fun h a)


open Classical in
def step (ρ : E →+* ℂ) (m : ℕ) : (E →+* ℂ) × ℕ → ℕ := fun p => if p.1 = ρ ∧ p.2 < m then 1 else 0

theorem dom_step (ρ : E →+* ℂ) (m : ℕ) : Dom (step ρ m) 0 := by
  refine ⟨fun τ i j hij => ?_, by simp⟩
  simp only [step]
  split_ifs with h1 h2 <;> first | omega | exact absurd ⟨h1.1, by omega⟩ h2

theorem chi_eq_one (U : Unf Xo c σ r)
    (h : ∀ a n, Dom a n → ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1)
    (k : U.Comp) (la : Wt (U.X k).Ψ r) (γ) (hγ : γ ∈ (U.X k).Γ) : (U.X k).χ la γ = 1 := by
  classical
  have hne : ∀ la, (U.X k).χ la γ ≠ 0 := fun la e => by
    obtain ⟨n, hn, h1⟩ := (U.X k).χ_fin la
    have := h1 γ hγ
    rw [e, zero_pow hn.ne'] at this
    exact zero_ne_one this
  have h0 : (U.X k).χ 0 γ = 1 := by
    have := (U.X k).χ_add 0 0 γ hγ
    rw [add_zero] at this
    exact (mul_eq_left₀ (hne 0)).1 this.symm
  let S : AddSubgroup (Wt (U.X k).Ψ r) :=
    { carrier := {la | (U.X k).χ la γ = 1}
      zero_mem' := h0
      add_mem' := fun {a b} ha hb => by
        show _ = _
        rw [(U.X k).χ_add a b γ hγ, ha, hb, one_mul]
      neg_mem' := fun {a} ha => by
        have := (U.X k).χ_add a (-a) γ hγ
        rw [add_neg_cancel, h0, show (U.X k).χ a γ = 1 from ha, one_mul] at this
        exact this.symm }
  have hst : ∀ ρ m, laU U (step ρ m) 0 k ∈ S := fun ρ m => h _ _ (dom_step ρ m) k γ hγ
  have hI := invFun_relab_injective (E := E) c σ
  have hcn : ∀ τ τ' : (U.X k).Ψ, conjEmb τ.1 ≠ τ'.1 := fun τ τ' e =>
    ((U.X k).cmType τ.1).1 τ.2 (by
      show conjEmb τ.1 ∈ _
      rw [e]; exact τ'.2)
  have hsing : ∀ (τ0 : (U.X k).Ψ) (j0 : Fin r), (Pi.single τ0 (Pi.single j0 1) : Wt (U.X k).Ψ r) ∈ S := by
    intro τ0 j0
    by_cases hj : (U.X k).p0 ≤ (j0 : ℕ)
    · have e : (Pi.single τ0 (Pi.single j0 1) : Wt (U.X k).Ψ r) =
          laU U (step (Function.invFun (relab c σ) τ0.1) (j0 - (U.X k).p0 + 1)) 0 k -
            laU U (step (Function.invFun (relab c σ) τ0.1) (j0 - (U.X k).p0)) 0 k := by
        funext τ j
        simp only [Pi.sub_apply, laU, step, hI.eq_iff, hcn τ τ0, false_and, if_false, Subtype.val_inj]
        by_cases ht : τ = τ0
        · subst ht
          simp only [Pi.single_eq_same, Pi.single_apply, true_and, Fin.ext_iff]
          split_ifs <;> simp <;> omega
        · simp [ht]
      rw [e]; exact S.sub_mem (hst _ _) (hst _ _)
    · have e : (Pi.single τ0 (Pi.single j0 1) : Wt (U.X k).Ψ r) =
          laU U (step (Function.invFun (relab c σ) (conjEmb τ0.1)) ((U.X k).p0 - 1 - j0)) 0 k -
            laU U (step (Function.invFun (relab c σ) (conjEmb τ0.1)) ((U.X k).p0 - j0)) 0 k := by
        funext τ j
        simp only [Pi.sub_apply, laU, step, hI.eq_iff, (hcn τ0 τ).symm, false_and, if_false]
        by_cases ht : τ = τ0
        · subst ht
          simp only [Pi.single_eq_same, Pi.single_apply, true_and, Fin.ext_iff]
          split_ifs <;> simp <;> omega
        · have : conjEmb τ.1 ≠ conjEmb τ0.1 := fun e => ht (Subtype.ext (conjEmb_inj e))
          simp [ht, this]
      rw [e]; exact S.sub_mem (hst _ _) (hst _ _)
  have e : la = ∑ τ, ∑ j, la τ j • (Pi.single τ (Pi.single j 1) : Wt (U.X k).Ψ r) := by
    funext τ j
    simp [Finset.sum_apply, Pi.single_apply, ite_apply]
  show la ∈ S
  rw [e]
  exact S.sum_mem fun τ _ => S.sum_mem fun j _ => S.zsmul_mem (hsing τ j) _

section Adelic
variable (U : Unf Xo c σ r) {V : HSp D} {dict : GA D V → Σ k, Frame (U.X k).Ψ r} {mu : GA D V → ℂ}
  {Kf : Subgroup (GA D V)} {th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}

theorem adelAut_of_dominant
    (hχ : ∀ a n, Dom a n → ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (laU U a n k) γ = 1)
    (hd : DictIsUnif V dict Kf th hr) (hm : MuUnit V dict mu) (hc : Continuous mu)
    (hL : ∀ g₀ : GA D V, ∃ N ∈ 𝓝 g₀, ∃ (k : U.Comp) (x : GA D V → Frame (U.X k).Ψ r), ContinuousOn x N ∧
      ∀ g ∈ N, x g ∈ (U.X k).dom ∧ ∃ γ ∈ (U.X k).Γ, dict g = ⟨k, lact γ (x g)⟩) : AdelAut V dict mu := by
  intro la P hP
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · obtain ⟨γ', hγ', he⟩ := hd.1 γ hγ g
    have hE := (hP (dict g).1).1.1.2.2 γ' hγ' (dict g).2 (hd.2.2.2.1 g)
    show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
    rw [he, hm.1, hm.2.2.1 γ hγ, one_mul]
    show mu g * P (dict g).1 (lact γ' (dict g).2) = _
    rw [hE, chi_eq_one U hχ _ _ _ hγ', one_mul]
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨N, hN, k, x, hx, hs⟩ := hL g₀
    have hsec : (U.X k).IsSec (la k) (P k) := (hP k).1.1
    have hc' : ContinuousOn (fun g => mu g * P k (x g)) N :=
      hc.continuousOn.mul (hsec.1.continuousOn.comp hx fun g hg => (hs g hg).1)
    have heq : (fun g => mu g * P k (x g)) =ᶠ[𝓝 g₀] adel V dict mu P := by
      filter_upwards [hN] with g hg
      obtain ⟨hd, γ, hγ, he⟩ := hs g hg
      show mu g * P k (x g) = mu g * P (dict g).1 (dict g).2
      rw [he]
      show mu g * P k (x g) = mu g * P k (lact γ (x g))
      rw [hsec.2.2 γ hγ (x g) hd, chi_eq_one U hχ _ _ _ hγ, one_mul]
    exact (hc'.continuousAt hN).congr heq

end Adelic
end GlobalTheory.OneEmbeddingProbe
