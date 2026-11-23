module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeCombinationsCommuteFixedVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SphLabelComm

section Abstract

variable {G : Type} [Group G]

theorem isDC_of_reps {K : Subgroup G} {x : G} {A : Finset G} (h : GlobalTheory.SphLabelOps.Reps K x A) :
    Formalism.IndefR.Bridge.IsDC K x A := by
  refine ⟨fun a ha => ?_, fun g hg => h.2 g ?_⟩
  · obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := h.1 a ha
    exact ⟨⟨k₁, h₁⟩, ⟨k₂, h₂⟩, rfl⟩
  · obtain ⟨k₁, k₂, rfl⟩ := hg
    exact ⟨k₁, k₁.2, k₂, k₂.2, rfl⟩

theorem sum_comm_of_antiInv (K L : Subgroup G) (hKL : K ≤ L) (θ : G → G)
    (t1 : ∀ g ∈ L, θ g ∈ L) (t2 : ∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) (t3 : ∀ x ∈ L, θ (θ x) = x)
    (t4 : ∀ k ∈ K, θ k ∈ K) (t5 : ∀ g ∈ L, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b)
    {x y : G} (hx : x ∈ L) (hy : y ∈ L) {A B A' : Finset G}
    (hA : GlobalTheory.SphLabelOps.Reps K x A) (hB : GlobalTheory.SphLabelOps.Reps K y B) (hA' : GlobalTheory.SphLabelOps.Reps K x⁻¹ A')
    {M : Type} [AddCommGroup M] [Module ℂ M] (π : G →* Module.End ℂ M) (u : M) (hu : ∀ k ∈ K, π k u = u) :
    ∑ a ∈ A, π a (∑ b ∈ B, π b u) = ∑ b ∈ B, π b (∑ a ∈ A, π a u) := by
  have memL : ∀ {z : G} {R : Finset G}, GlobalTheory.SphLabelOps.Reps K z R → z ∈ L → ∀ a ∈ R, a ∈ L := by
    intro z R hR hz a ha
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hR.1 a ha
    exact mul_mem (mul_mem (hKL h₁) hz) (hKL h₂)
  have hθ : ∃ θ : G → G, (∀ g ∈ L, θ g ∈ L) ∧ (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧
      (∀ x ∈ L, θ (θ x) = x) ∧ (∀ k ∈ K ⊓ L, θ k ∈ K) ∧ ∀ g ∈ L, ∃ a ∈ K ⊓ L, ∃ b ∈ K ⊓ L, θ g = a * g * b := by
    refine ⟨θ, t1, t2, t3, fun k hk => t4 k hk.1, fun g hg => ?_⟩
    obtain ⟨a, ha, b, hb, e⟩ := t5 g hg
    exact ⟨a, ⟨ha, hKL ha⟩, b, ⟨hb, hKL hb⟩, e⟩
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have hF : ∀ (k : K) (h : G), (fun g => φ (π g u)) (h * k) = ((1 : K →* ℂˣ) k : ℂ) • (fun g => φ (π g u)) h := by
    intro k h
    simp [map_mul, Module.End.mul_apply, hu k k.2]
  have key := (GlobalTheory.DoubleCosetComm.dcOp_comm_and_card (W := ℂ) K L 1 x y A B A' (fun g => φ (π g u))
    (fun k hk => ⟨k, hk, 1, one_mem _, hKL hk, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun k _ => rfl) hθ (memL hA hx) (memL hB hy) (memL hA' (inv_mem hx)) (isDC_of_reps hA) (isDC_of_reps hB)
    (isDC_of_reps hA') hF).1
  have e := congrFun key 1
  simp only [Formalism.IndefR.Bridge.dcOp, one_mul, map_mul, Module.End.mul_apply] at e
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sub, map_sum, LinearMap.zero_apply]
  rw [sub_eq_zero]
  exact e

theorem comb_comm {ι M : Type} [AddCommGroup M] [Module ℂ M] (S : ι → Module.End ℂ M) (u : M)
    (h : ∀ i j, S i (S j u) = S j (S i u)) (c c' : ι →₀ ℂ) :
    (c.sum fun i z => z • S i) ((c'.sum fun i z => z • S i) u) =
      (c'.sum fun i z => z • S i) ((c.sum fun i z => z • S i) u) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [h i j, smul_comm]

end Abstract


open GlobalTheory.IdemSupport in
theorem label_ops_comm : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ c c', ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π P c (opOf π P c' u) = opOf π P c' (opOf π P c u) := by
  intro D V P c c' M _ _ π u hu
  obtain ⟨K, hK⟩ := GlobalTheory.SphLabelOps.exists_hyp V P
  obtain ⟨e, f, h⟩ := (supported_group_and_prime_idempotents V).2.1 P
  have h0 := (supported_group_and_prime_idempotents V).2.2.1 P e f h
  obtain ⟨L, hL⟩ := ((supported_group_and_prime_idempotents V).1 f h0.1 h0.2.1).1
  have memK : ∀ k, k ∈ K ↔ k ∈ KsphC V ∅ ∧ SuppF V f k := fun k => by
    rw [← SetLike.mem_coe, ← hK, GlobalTheory.SphLabelOps.hyp_eq h]
    rfl
  have hKL : K ≤ L := fun k hk => (hL k).2 ((memK k).1 hk).2
  obtain ⟨θ, t1, t2, t3, t4, t5⟩ : ∃ θ : GA D V → GA D V, (∀ g ∈ L, θ g ∈ L) ∧
      (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧ (∀ x ∈ L, θ (θ x) = x) ∧ (∀ k ∈ K, θ k ∈ K) ∧
      ∀ g ∈ L, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b := by
    rcases id h with ⟨hs, rfl⟩ | ⟨rfl, -⟩
    · obtain ⟨θ, s1, s2, s3, s4, s5⟩ := (GlobalTheory.SplitPlace.split_local V P e hs).1
      refine ⟨θ, fun g hg => (hL _).2 (s1 g ((hL g).1 hg)), fun x hx y hy => s2 x y ((hL x).1 hx) ((hL y).1 hy),
        fun x hx => s3 x ((hL x).1 hx), fun k hk => ?_, fun g hg => ?_⟩
      · have hk' := (memK k).1 hk
        exact (memK _).2 ⟨s4 k hk', s1 k hk'.2⟩
      · obtain ⟨a, ha, b, hb, eq⟩ := s5 g ((hL g).1 hg)
        exact ⟨a, (memK a).2 ha, b, (memK b).2 hb, eq⟩
    · refine ⟨fun g => g⁻¹, fun g hg => inv_mem hg, fun x _ y _ => mul_inv_rev x y, fun x _ => inv_inv x,
        fun k hk => inv_mem hk, fun g hg => ?_⟩
      obtain ⟨a, b, ha, ha', hb, hb', eq⟩ := (GlobalTheory.InertDoubleCoset.inert_double_cosets V P _ h
        (GlobalTheory.SphLabelOps.exists_real_unif D P) g ((hL g).1 hg)).1
      exact ⟨a, (memK a).2 ⟨ha, ha'⟩, b, (memK b).2 ⟨hb, hb'⟩, eq⟩
  have reps : ∀ d, IsLab V P d → ∃ x ∈ L, GlobalTheory.SphLabelOps.Reps K x (rep V P d) ∧
      ∃ A', GlobalTheory.SphLabelOps.Reps K x⁻¹ A' := by
    intro d hd
    have hR := GlobalTheory.SphLabelOps.sphOp_rep hd
    obtain ⟨e', f', ϖ, α, -, h', h1, h2, -, -, -, hα, hD, -⟩ := id hR
    obtain ⟨rfl, rfl⟩ := h0.2.2.2.1 e' f' h'
    have hαL : α ∈ L := (hL α).2 hα
    refine ⟨α, hαL, GlobalTheory.SphLabelOps.reps_of_sphOp hK h' h1 h2 hα hD hR, ?_⟩
    obtain ⟨R', hR', -⟩ := GlobalTheory.SphLabelOps.exists_dual hR
    have he := (GlobalTheory.HeckeDual.idem_of_isPrimeIdem h').1
    exact ⟨R', GlobalTheory.SphLabelOps.reps_of_sphOp hK h' h1 h2 ((hL _).1 (inv_mem hαL))
      (GlobalTheory.DivDual.divAt_inv_and_mul V _ _ d α he (GlobalTheory.SphLabelOps.unif_ne_zero h2) hD).1 hR'⟩
  have key : ∀ d d', (∑ γ ∈ rep V P d, π γ) ((∑ δ ∈ rep V P d', π δ) u) =
      (∑ δ ∈ rep V P d', π δ) ((∑ γ ∈ rep V P d, π γ) u) := by
    intro d d'
    by_cases hd : IsLab V P d
    swap
    · simp [Hk3.rep, dif_neg hd]
    by_cases hd' : IsLab V P d'
    swap
    · simp [Hk3.rep, dif_neg hd']
    obtain ⟨x, hx, rA, A', rA'⟩ := reps d hd
    obtain ⟨y, hy, rB, -⟩ := reps d' hd'
    simp only [LinearMap.sum_apply]
    exact sum_comm_of_antiInv K L hKL θ t1 t2 t3 t4 t5 hx hy rA rB rA' π u
      (fun k hk => hu k (by rw [hK]; exact hk))
  exact comb_comm (fun d => ∑ γ ∈ rep V P d, π γ) u key c c'

end GlobalTheory.SphLabelComm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead ValuativeRel

namespace GlobalTheory.SatakeExists

theorem exists_eigenform {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) (hcomm : ∀ a b : G, a * b = b * a)
    (hn : ∀ g, MonoidHom.id G g ∈ Subgroup.normalizer (H : Set G))
    [FiniteDimensional ℂ (fixed ρ H)] [Nontrivial (fixed ρ H)] :
    ∃ (χ : G →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ g v, l (ρ g v) = (χ g : ℂ) * l v) ∧
      ∀ h ∈ H, χ h = 1 := by
  have hc := LocGL.isCompl_fixed_twKer hρ hH
  let T : Subrepresentation ρ := ⟨twKer ρ H 1, fun g _ hv => twKer_le_comap ρ H g (hn g) hv⟩
  let σ := onFixed ρ H (MonoidHom.id G) hn
  let p : ρ.IntertwiningMap σ :=
    ⟨Submodule.projectionOnto _ _ hc, fun g => LinearMap.ext fun v => by
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
      have e1 := Submodule.projectionOnto_apply_left hc ⟨a, ha⟩
      have e2 := Submodule.projectionOnto_apply_right hc ⟨b, hb⟩
      have e3 := Submodule.projectionOnto_apply_left hc (σ g ⟨a, ha⟩)
      have e4 := Submodule.projectionOnto_apply_right hc ⟨ρ g b, T.apply_mem_toSubmodule g hb⟩
      simp only [LinearMap.comp_apply, map_add (f := _)]
      rw [e1, e2, e4, map_zero]
      exact congrArg (· + 0) e3⟩
  have hp : ∀ x : fixed ρ H, p x.1 = x := fun x => Submodule.projectionOnto_apply_left hc x
  obtain ⟨ψ, m, hm0, hm⟩ := GlobalTheory.exists_character_eigenvector_of_commute ℂ G _ σ.dual fun a b => by
    rw [← map_mul, hcomm, map_mul]
  have hm' : ∀ g x, m (σ g x) = ((ψ g)⁻¹ : ℂˣ) * m x := fun g x => by
    have := LinearMap.congr_fun (hm g⁻¹) x
    simpa [Representation.dual_apply, Module.Dual.transpose_apply] using this
  obtain ⟨x₀, hx₀⟩ : ∃ x, m x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hm0 (LinearMap.ext fun x => by simpa using h x)
  refine ⟨ψ⁻¹, m ∘ₗ p.toLinearMap, fun h => hx₀ ?_, fun g v => ?_, fun h hh => ?_⟩
  · have := LinearMap.congr_fun h x₀.1
    simpa [hp] using this
  · show m (p (ρ g v)) = _
    rw [p.isIntertwining, hm']
    rfl
  · have h1 : σ h x₀ = x₀ := by
      apply Subtype.ext
      show ρ h x₀.1 = x₀.1
      simpa using x₀.2 ⟨h, hh⟩
    have h2 := hm' h x₀
    rw [h1] at h2
    have h3 : (((ψ h)⁻¹ : ℂˣ) : ℂ) = 1 := by
      have := mul_right_cancel₀ hx₀ (show (1 : ℂ) * m x₀ = (((ψ h)⁻¹ : ℂˣ) : ℂ) * m x₀ by rw [one_mul]; exact h2)
      exact this.symm
    exact Units.ext (by simpa using h3)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_eq_torusChar {n : ℕ} (μ : (Fin n → kˣ) →* ℂˣ) (hμ : ∀ t ∈ torusO k (Fin n), μ t = 1) :
    ∃ α : Fin n → ℂˣ, torusChar (fun i => unrChar k (α i)) = μ := by
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
    obtain ⟨c, hc⟩ := valuation_surjective (uniformizer k)
    refine ⟨Units.mk0 c fun h => ?_, hc⟩
    rw [h, map_zero] at hc
    exact IwahoriInj.unif_pos.ne hc
  let c : Fin n → kˣ →* ℂˣ := fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i)
  have hc : ∀ i, IsUnram (c i) := fun i x hx => hμ _ fun j => by
    by_cases h : j = i
    · subst h; simpa using hx
    · simp [Pi.mulSingle_eq_of_ne h]
  refine ⟨fun i => c i ϖ, MonoidHom.ext fun t => ?_⟩
  rw [torusChar_apply]
  simp only [← GlobalTheory.SmGL.eq_unrChar (hc _) hϖ]
  conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
  rfl

theorem isSubquotient_of_eigenform {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (hπ : IsSmooth π) (hirr : π.IsIrreducible)
    (μ : (Fin n → kˣ) →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ) (hl0 : l ≠ 0)
    (hl : ∀ t x, l (jacB π t x) = (μ t : ℂ) * l x) :
    IsSubquotient π (indB (ofChar μ)) := by
  let ρ : Representation ℂ (Levi k fun _ : Fin n => Unit) ℂ :=
    (ofChar μ).comp (leviTorus k (Fin n)).symm.toMonoidHom
  let φ : (jac (points (Fin n)) π).IntertwiningMap ρ :=
    ⟨l, fun g => LinearMap.ext fun x => by
      obtain ⟨t, rfl⟩ := (leviTorus k (Fin n)).surjective g
      have e : (ρ (leviTorus k (Fin n) t)) (l x) = (μ t : ℂ) * l x := by
        show ofChar μ ((leviTorus k (Fin n)).symm (leviTorus k (Fin n) t)) _ = _
        rw [MulEquiv.symm_apply_apply, ofChar_apply]
      exact (hl t x).trans e.symm⟩
  obtain ⟨f, hf⟩ := (GlobalTheory.SmGL.Model.evalOne_bijective (points (Fin n)) hπ ρ).2 φ
  have hne : ∃ v, f v ≠ 0 := by
    by_contra h
    push_neg at h
    refine hl0 (LinearMap.ext fun x => ?_)
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : φ (Submodule.Quotient.mk v) = (f v).1.1 1 := by rw [← hf]; rfl
    have h2 : l (Submodule.Quotient.mk v) = φ (Submodule.Quotient.mk v) := rfl
    rw [h2, h1, h v]
    rfl
  refine IsSubquotient.of_injective f ((injective_iff_map_eq_zero f.toLinearMap).2 ?_)
  let K : Subrepresentation π := ⟨LinearMap.ker f.toLinearMap, fun g v hv => by
    show f (π g v) = 0
    rw [f.isIntertwining]
    have : f v = 0 := hv
    rw [this, map_zero]⟩
  haveI := hirr
  rcases eq_bot_or_eq_top K with h | h
  · intro v hv
    have : v ∈ K.toSubmodule := hv
    rw [h] at this
    exact (Submodule.mem_bot ℂ).1 this
  · obtain ⟨v, hv⟩ := hne
    exact absurd (show v ∈ K.toSubmodule by rw [h]; trivial) hv

theorem exists_eigenform_jacBU {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (hadm : IsAdmissible π)
    (hI : fixed π (iwahori k (Fin n)) ≠ ⊥) :
    ∃ (χ : (Fin n → kˣ) →* ℂˣ) (l : Jacquet π (unipB k (Fin n)) →ₗ[ℂ] ℂ), l ≠ 0 ∧
      (∀ g v, l (jacBU π g v) = (χ g : ℂ) * l v) ∧ ∀ h ∈ torusO k (Fin n), χ h = 1 := by
  haveI := hadm.2 _ (SmGL.IwahoriOnto.isOpen_iwahori k (Fin n))
    (SmGL.IwahoriOnto.isCompact_iwahori k (Fin n))
  have hb := GlobalTheory.Published.BorelCasselman_holds k (Fin n) V π hadm
  haveI : FiniteDimensional ℂ (fixed (jacBU π) (torusO k (Fin n))) :=
    Module.Finite.of_surjective _ hb.2
  haveI : Nontrivial (fixed π (iwahori k (Fin n))) := Submodule.nontrivial_iff_ne_bot.2 hI
  haveI : Nontrivial (fixed (jacBU π) (torusO k (Fin n))) := hb.1.nontrivial
  exact exists_eigenform (isSmooth_jacBU hadm.1) (SmGL.UnramFixed.isCompact_torusO k (Fin n)) mul_comm
    fun _ => by rw [Subgroup.normalizer_eq_top]; trivial

theorem exists_isSubquotient_prinSeries {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin n) k) V} (hadm : IsAdmissible π) (hirr : π.IsIrreducible)
    (hI : fixed π (iwahori k (Fin n)) ≠ ⊥) :
    ∃ α : Fin n → ℂˣ, IsSubquotient π (prinSeries fun i => unrChar k (α i)) := by
  obtain ⟨χ, l, hl0, hl, hχ⟩ := exists_eigenform_jacBU hadm hI
  let δ : (Fin n → kˣ) →* ℂˣ :=
    (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom
  obtain ⟨α, hα⟩ := exists_eq_torusChar (χ * δ⁻¹) fun t ht => by
    have : δ t = 1 := SmGL.UnramFixed.deltaHalf_torusO k ht
    simp [hχ t ht, this]
  refine ⟨α, ?_⟩
  have key := isSubquotient_of_eigenform hadm.1 hirr (χ * δ⁻¹) l hl0 fun t x => by
    rw [SmGL.UnramFixed.jacB_apply, map_smul, hl, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul,
      MonoidHom.inv_apply]
    ring
  rw [← hα] at key
  exact key

theorem main : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n), IsSpherical π.π → ∃ α : Fin n → ℂˣ, HasSatake π.π α := by
  intro hBZ k _ _ _ _ n π hs
  have hadm : IsAdmissible π.π := (hBZ k).1 (Fin n) π.V π.π π.smooth π.irr
  have hI : fixed π.π (iwahori k (Fin n)) ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hs
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    exact hv ⟨h.1, iwahori_le_KO k _ h.2⟩
  obtain ⟨α, hα⟩ := exists_isSubquotient_prinSeries hadm π.irr hI
  exact ⟨α, π.irr, hs, hα⟩

end GlobalTheory.SatakeExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedDirectSum
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Module

namespace GlobalTheory.WeilDeligne

section ProdLin

variable {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem inl_absSpace_le (f : End ℂ V) (g : End ℂ V') (r : ℝ) :
    (absSpace f r).map (LinearMap.inl ℂ V V') ≤ absSpace (f.prodMap g : End ℂ (V × V')) r :=
  map_absSpace_le (f := f) (g := (f.prodMap g : End ℂ (V × V'))) (LinearMap.inl ℂ V V')
    (fun x => Prod.ext rfl (map_zero g).symm) r

theorem inr_absSpace_le (f : End ℂ V) (g : End ℂ V') (r : ℝ) :
    (absSpace g r).map (LinearMap.inr ℂ V V') ≤ absSpace (f.prodMap g : End ℂ (V × V')) r :=
  map_absSpace_le (f := g) (g := (f.prodMap g : End ℂ (V × V'))) (LinearMap.inr ℂ V V')
    (fun x => Prod.ext (map_zero f).symm rfl) r

theorem mem_absSpace_prodMap (f : End ℂ V) (g : End ℂ V') (r : ℝ) (v : V × V') :
    v ∈ absSpace (f.prodMap g : End ℂ (V × V')) r ↔ v.1 ∈ absSpace f r ∧ v.2 ∈ absSpace g r := by
  constructor
  · intro hv
    exact ⟨map_absSpace_le (LinearMap.fst ℂ V V') (fun _ => rfl) r ⟨v, hv, rfl⟩,
      map_absSpace_le (LinearMap.snd ℂ V V') (fun _ => rfl) r ⟨v, hv, rfl⟩⟩
  · rintro ⟨h1, h2⟩
    have e : v = LinearMap.inl ℂ V V' v.1 + LinearMap.inr ℂ V V' v.2 := by simp
    rw [e]
    exact add_mem (inl_absSpace_le f g r ⟨_, h1, rfl⟩) (inr_absSpace_le f g r ⟨_, h2, rfl⟩)

theorem IsPurePair.prodMap {q : ℝ} {f N : End ℂ V} {g M : End ℂ V'} (hf : IsPurePair q f N)
    (hg : IsPurePair q g M) :
    IsPurePair q (f.prodMap g : End ℂ (V × V')) (N.prodMap M) := by
  have hpow : ∀ i : ℕ, (N.prodMap M : End ℂ (V × V')) ^ i = (N ^ i).prodMap (M ^ i) :=
    fun i => (map_pow (LinearMap.prodMapRingHom ℂ V V') (N, M) i).symm
  refine ⟨eq_top_iff.mpr fun v _ => ?_, fun i => ?_⟩
  · have h1 : v.1 ∈ ⨆ i : ℤ, absSpace f (q ^ ((i : ℝ) / 2)) := hf.1 ▸ Submodule.mem_top
    have h2 : v.2 ∈ ⨆ i : ℤ, absSpace g (q ^ ((i : ℝ) / 2)) := hg.1 ▸ Submodule.mem_top
    have hl : (⨆ i : ℤ, absSpace f (q ^ ((i : ℝ) / 2))).map (LinearMap.inl ℂ V V') ≤
        ⨆ i : ℤ, absSpace (f.prodMap g : End ℂ (V × V')) (q ^ ((i : ℝ) / 2)) := by
      rw [Submodule.map_iSup]
      exact iSup_mono fun i => inl_absSpace_le f g _
    have hr : (⨆ i : ℤ, absSpace g (q ^ ((i : ℝ) / 2))).map (LinearMap.inr ℂ V V') ≤
        ⨆ i : ℤ, absSpace (f.prodMap g : End ℂ (V × V')) (q ^ ((i : ℝ) / 2)) := by
      rw [Submodule.map_iSup]
      exact iSup_mono fun i => inr_absSpace_le f g _
    have e : v = LinearMap.inl ℂ V V' v.1 + LinearMap.inr ℂ V V' v.2 := by simp
    rw [e]
    exact add_mem (hl ⟨_, h1, rfl⟩) (hr ⟨_, h2, rfl⟩)
  · rw [hpow]
    refine ⟨fun v hv => ?_, fun v hv v' hv' hvv => ?_, fun v hv => ?_⟩
    · rw [SetLike.mem_coe, mem_absSpace_prodMap] at hv ⊢
      exact ⟨(hf.2 i).1 hv.1, (hg.2 i).1 hv.2⟩
    · rw [SetLike.mem_coe, mem_absSpace_prodMap] at hv hv'
      have := Prod.ext_iff.mp hvv
      exact Prod.ext ((hf.2 i).2.1 hv.1 hv'.1 this.1) ((hg.2 i).2.1 hv.2 hv'.2 this.2)
    · rw [SetLike.mem_coe, mem_absSpace_prodMap] at hv
      obtain ⟨u, hu, e1⟩ := (hf.2 i).2.2 hv.1
      obtain ⟨u', hu', e2⟩ := (hg.2 i).2.2 hv.2
      exact ⟨(u, u'), (mem_absSpace_prodMap _ _ _ _).mpr ⟨hu, hu'⟩, Prod.ext e1 e2⟩

end ProdLin

theorem WDRep.Tempered.sum {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {h : IsPlaceOver A w} {V V' : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] {a : WDRep h V} {b : WDRep h V'}
    (ha : a.Tempered) (hb : b.Tempered) : (a.sum b).Tempered :=
  fun φ hφ => (ha φ hφ).prodMap (hb φ hφ)

theorem WD.tempered_lpSum : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E))
    (h : IsPlaceOver A w) (x y : WD h), x.tempered → y.tempered → (x.lpSum y).tempered := by
  intro E Ω _ _ _ _ _ A w h x y hx hy
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP m b =>
      rw [WD.tempered_mk] at hx hy
      rw [WD.lpSum_mk, WD.tempered_mk]
      exact hx.sum hy

end GlobalTheory.WeilDeligne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLtOneOfResidue
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.PointStabilizer

def stab {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (v : V) :
    Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    have ha' : ρ a v = v := ha
    have hb' : ρ b v = v := hb
    show ρ (a * b) v = v
    rw [map_mul, Module.End.mul_apply, hb', ha']
  inv_mem' := by
    intro a ha
    have ha' : ρ a v = v := ha
    show ρ a⁻¹ v = v
    conv_lhs => rw [← ha']
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_lt_one_of_residue {x : 𝒪[k]} (hx : IsLocalRing.residue 𝒪[k] x = 0) :
    valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one] at hx
  exact lt_of_le_of_ne x.2 hx

theorem entry_of_mem_KOne {n : ℕ} {g : GL (Fin n) k} (hg : g ∈ KOne k (Fin n)) (i j : Fin n) :
    valuation k (g.val i j - (1 : Matrix (Fin n) (Fin n) k) i j) < 1 := by
  obtain ⟨h, hh, rfl⟩ := hg
  have h1 : Matrix.GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue 𝒪[k]) h = 1 := hh
  have h2 : IsLocalRing.residue 𝒪[k] (h.val i j) = (1 : Matrix (Fin n) (Fin n) _) i j := by
    have := congrArg (fun u : GL (Fin n) _ => u.val i j) h1
    simpa using this
  have h3 : IsLocalRing.residue 𝒪[k] (h.val i j - (1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) = 0 := by
    rw [map_sub, h2]
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  have h4 := val_lt_one_of_residue h3
  rw [map_sub] at h4
  have h5 : algebraMap 𝒪[k] k ((1 : Matrix (Fin n) (Fin n) 𝒪[k]) i j) = (1 : Matrix (Fin n) (Fin n) k) i j := by
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  rw [h5] at h4
  exact h4

def pts (n : ℕ) : (Σ _ : Fin n, Fin 1) ≃ Fin n := Equiv.sigmaUnique (Fin n) fun _ => Fin 1

theorem unipRad_pts (n : ℕ) : unipRad k (pts n) = unipB k (Fin n) :=
  GlobalTheory.SmGL.EmptyBlocks.unipRad_eq k (pts n) (fun _ _ h => h)

theorem mk_ne_zero (H : GlobalTheory.Published.DepthZeroJacquetInjective) (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : GlobalTheory.SplitRead.Irr k n) (v : π.V)
    (θ : Fin n → kˣ →* ℂˣ) (hv : v ≠ 0) (hI : GlobalTheory.TameIwahori.IsIwVec θ π.π v) :
    Submodule.Quotient.mk v ≠ (0 : π.V ⧸ twKer π.π (unipB k (Fin n)) 1) := by
  intro h0
  have hle : KOne k (Fin n) ⊔ (unipRad k (pts n) ⊓ KO k (Fin n)) ≤ stab π.π v := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · refine hI.1 g (iwahori_le_KO k (Fin n) (KOne_le_iwahori k (Fin n) hg)) (fun i j hij => ?_) (fun i => ?_)
      · simpa [Matrix.one_apply_ne hij.ne'] using entry_of_mem_KOne hg i j
      · simpa using entry_of_mem_KOne hg i i
    · have hu := (mem_unipB k).1 (unipRad_pts (k := k) n ▸ hg.1)
      refine hI.1 g hg.2 (fun i j hij => ?_) (fun i => ?_)
      · rw [hu.1 i j hij]; simp
      · rw [hu.2 i]; simp
  refine hv (H k n n (fun _ => 1) (pts n) π v (fun g => ?_) ?_)
  · have : π.π g v = v := hle g.2
    simpa using this
  · rw [Submodule.Quotient.mk_eq_zero] at h0 ⊢
    rw [unipRad_pts]
    exact h0

end GlobalTheory.PointStabilizer
end
end

