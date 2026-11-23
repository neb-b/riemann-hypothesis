module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0872
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0896
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfCommutingFiniteAlgebraJointEi
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory Filter Topology

namespace GlobalTheory.FinEig

open Polynomial

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem fd_inf_ker_mul (N : Submodule ℂ M) (f g : Module.End ℂ M) (hf : ∀ v ∈ N, f v ∈ N)
    (h1 : FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker f)) (h2 : FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker g)) :
    FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (g * f)) := by
  rw [← Submodule.fg_iff_finiteDimensional]
  apply Submodule.fg_of_fg_map_of_fg_inf_ker f
  · have hle : (N ⊓ LinearMap.ker (g * f)).map f ≤ N ⊓ LinearMap.ker g := by
      rintro _ ⟨v, ⟨hvN, hv⟩, rfl⟩
      exact ⟨hf v hvN, by simpa [LinearMap.mem_ker] using hv⟩
    haveI := Submodule.finiteDimensional_of_le hle
    exact (Submodule.fg_iff_finiteDimensional _).2 inferInstance
  · have hle : N ⊓ LinearMap.ker (g * f) ⊓ LinearMap.ker f ≤ N ⊓ LinearMap.ker f :=
      fun v hv => ⟨hv.1.1, hv.2⟩
    haveI := Submodule.finiteDimensional_of_le hle
    exact (Submodule.fg_iff_finiteDimensional _).2 inferInstance

theorem adjoin_preserves (N : Submodule ℂ M) (s : Set (Module.End ℂ M)) (hs : ∀ u ∈ s, ∀ v ∈ N, u v ∈ N)
    {b : Module.End ℂ M} (hb : b ∈ Algebra.adjoin ℂ s) : ∀ v ∈ N, b v ∈ N := by
  induction hb using Algebra.adjoin_induction with
  | mem x hx => exact hs x hx
  | algebraMap r => intro v hv; simpa [Module.algebraMap_end_apply] using N.smul_mem r hv
  | add x y _ _ hx hy => intro v hv; exact N.add_mem (hx v hv) (hy v hv)
  | mul x y _ _ hx hy => intro v hv; exact hx _ (hy v hv)

theorem fd_inf_ker_aeval (N : Submodule ℂ M) (t : Module.End ℂ M) (ht : ∀ v ∈ N, t v ∈ N)
    (h : ∀ μ : ℂ, FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (t - algebraMap ℂ (Module.End ℂ M) μ))) :
    ∀ n : ℕ, ∀ q : ℂ[X], q.natDegree = n → q ≠ 0 → FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (aeval t q)) := by
  intro n
  induction n with
  | zero =>
    intro q hq hq0
    rw [Polynomial.eq_C_of_natDegree_eq_zero hq] at hq0 ⊢
    have ha : q.coeff 0 ≠ 0 := fun e => hq0 (by rw [e, map_zero])
    have hle : N ⊓ LinearMap.ker (aeval t (C (q.coeff 0))) ≤ ⊥ := by
      intro v hv
      have h2 := hv.2
      simp only [LinearMap.mem_ker, aeval_C, Module.algebraMap_end_apply] at h2
      simpa [Submodule.mem_bot] using (smul_eq_zero.1 h2).resolve_left ha
    exact Submodule.finiteDimensional_of_le hle
  | succ n ih =>
    intro q hq hq0
    have hdeg : 0 < q.degree := by
      rw [Polynomial.degree_eq_natDegree hq0, hq]; exact_mod_cast Nat.succ_pos n
    obtain ⟨μ, hμ⟩ := Complex.exists_root hdeg
    have hfac := (Polynomial.mul_divByMonic_eq_iff_isRoot (a := μ) (p := q)).2 hμ
    set q' := q /ₘ (X - C μ) with hq'
    have hq'0 : q' ≠ 0 := by
      intro e; apply hq0; rw [← hfac, e, mul_zero]
    have hq'deg : q'.natDegree = n := by
      rw [hq', Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C μ), hq, Polynomial.natDegree_X_sub_C]; rfl
    have hmul : aeval t q = (t - algebraMap ℂ (Module.End ℂ M) μ) * aeval t q' := by
      conv_lhs => rw [← hfac]
      simp [map_mul, map_sub, aeval_X, aeval_C]
    rw [hmul]
    apply fd_inf_ker_mul N _ _ _ (ih q' hq'deg hq'0) (h μ)
    exact adjoin_preserves N {t} (by simpa using ht) (Polynomial.aeval_mem_adjoin_singleton ℂ t)

theorem fd_of_finset (T : Finset (Module.End ℂ M)) (hc : ∀ u ∈ T, ∀ w ∈ T, u * w = w * u)
    (ha : ∀ u ∈ T, ∃ q : ℂ[X], q ≠ 0 ∧ aeval u q = 0) :
    ∀ N : Submodule ℂ M, (∀ u ∈ T, ∀ v ∈ N, u v ∈ N) →
      (∀ c : Module.End ℂ M → ℂ,
        FiniteDimensional ℂ ↥(N ⊓ ⨅ u ∈ T, LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) (c u)))) →
      FiniteDimensional ℂ ↥N := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro N _ h
    haveI := h 0
    refine Submodule.finiteDimensional_of_le (S₂ := N ⊓ ⨅ u ∈ (∅ : Finset (Module.End ℂ M)),
      LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) ((0 : Module.End ℂ M → ℂ) u))) ?_
    intro v hv
    refine ⟨hv, ?_⟩
    rw [SetLike.mem_coe, Submodule.mem_iInf]
    intro u
    rw [Submodule.mem_iInf]
    intro hu
    simp at hu
  | insert t T htT ih =>
    intro N hN h
    obtain ⟨q, hq0, hq⟩ := ha t (Finset.mem_insert_self t T)
    have key : ∀ μ : ℂ, FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (t - algebraMap ℂ (Module.End ℂ M) μ)) := by
      intro μ
      apply ih (fun u hu w hw => hc u (Finset.mem_insert_of_mem hu) w (Finset.mem_insert_of_mem hw))
        (fun u hu => ha u (Finset.mem_insert_of_mem hu))
      · intro u hu v hv
        refine ⟨hN u (Finset.mem_insert_of_mem hu) v hv.1, ?_⟩
        have h2 : (t - algebraMap ℂ (Module.End ℂ M) μ) v = 0 := hv.2
        have hcom := hc t (Finset.mem_insert_self t T) u (Finset.mem_insert_of_mem hu)
        show (t - algebraMap ℂ (Module.End ℂ M) μ) (u v) = 0
        rw [LinearMap.sub_apply, Module.algebraMap_end_apply] at h2 ⊢
        rw [← Module.End.mul_apply, hcom, Module.End.mul_apply, ← map_smul, ← map_sub, h2, map_zero]
      · intro c
        haveI := h (Function.update c t μ)
        refine Submodule.finiteDimensional_of_le (S₂ := N ⊓ ⨅ u ∈ insert t T,
          LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) (Function.update c t μ u))) ?_
        intro v hv
        simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at hv ⊢
        obtain ⟨⟨hvN, hvt⟩, hvT⟩ := hv
        refine ⟨hvN, fun u hu => ?_⟩
        rcases Finset.mem_insert.1 hu with rfl | hu'
        · simpa using hvt
        · have hne : u ≠ t := fun e => htT (e ▸ hu')
          rw [Function.update_of_ne hne]
          exact hvT u hu'
    have := fd_inf_ker_aeval N t (hN t (Finset.mem_insert_self t T)) key _ q rfl hq0
    rwa [hq, LinearMap.ker_zero, inf_top_eq] at this

end GlobalTheory.FinEig

namespace GlobalTheory.AutGrowth

theorem finiteDimensional_of_commuting_finite_eigen :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (S : Set (Module.End ℂ M)), (∀ s ∈ S, ∀ t ∈ S, s * t = t * s) →
      FiniteDimensional ℂ (Algebra.adjoin ℂ S) →
      (∀ c : Module.End ℂ M → ℂ, FiniteDimensional ℂ ↥(⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ M) (c s)))) →
      FiniteDimensional ℂ M := by
  intro M _ _ S hS hB hE
  classical
  letI : IsMulCommutative (Algebra.adjoin ℂ S) :=
    Algebra.isMulCommutative_adjoin ℂ (fun x hx y hy _ => hS x hx y hy)
  have hcomm : ∀ x ∈ Algebra.adjoin ℂ S, ∀ y ∈ Algebra.adjoin ℂ S, x * y = y * x := by
    intro x hx y hy
    exact setLike_mul_comm hx hy
  obtain ⟨T, hT⟩ : (Algebra.adjoin ℂ S).FG :=
    Subalgebra.fg_of_fg_toSubmodule ((Submodule.fg_iff_finiteDimensional _).2 hB)
  have hTA : ∀ u ∈ T, u ∈ Algebra.adjoin ℂ S := fun u hu => hT ▸ Algebra.subset_adjoin hu
  have key := GlobalTheory.FinEig.fd_of_finset T (fun u hu w hw => hcomm u (hTA u hu) w (hTA w hw))
    (fun u hu => ((IsIntegral.of_finite ℂ (⟨u, hTA u hu⟩ : Algebra.adjoin ℂ S)).map
      (Algebra.adjoin ℂ S).val).isAlgebraic) ⊤ (fun _ _ _ _ => Submodule.mem_top) ?_
  · exact Module.Finite.equiv Submodule.topEquiv
  intro c
  have scal : ∀ b ∈ Algebra.adjoin ℂ S, ∃ μ : ℂ, ∀ v ∈ (⨅ u ∈ T, LinearMap.ker (u - algebraMap ℂ (Module.End ℂ M) (c u))), b v = μ • v := by
    intro b hb
    rw [← hT] at hb
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      refine ⟨c x, fun v hv => ?_⟩
      rw [Submodule.mem_iInf] at hv
      have h3 := hv x
      rw [Submodule.mem_iInf] at h3
      have h4 := h3 hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at h4
      exact h4
    | algebraMap r => exact ⟨r, fun v _ => by simp [Module.algebraMap_end_apply]⟩
    | add x y _ _ hx hy =>
      obtain ⟨μ₁, h₁⟩ := hx; obtain ⟨μ₂, h₂⟩ := hy
      exact ⟨μ₁ + μ₂, fun v hv => by rw [LinearMap.add_apply, h₁ v hv, h₂ v hv, add_smul]⟩
    | mul x y _ _ hx hy =>
      obtain ⟨μ₁, h₁⟩ := hx; obtain ⟨μ₂, h₂⟩ := hy
      exact ⟨μ₁ * μ₂, fun v hv => by
        rw [Module.End.mul_apply, h₂ v hv, map_smul, h₁ v hv, smul_smul, mul_comm]⟩
  let c' : Module.End ℂ M → ℂ := fun s => if h : s ∈ Algebra.adjoin ℂ S then Classical.choose (scal s h) else 0
  haveI := hE c'
  refine Submodule.finiteDimensional_of_le
    (S₂ := ⨅ s ∈ S, LinearMap.ker (s - algebraMap ℂ (Module.End ℂ M) (c' s))) ?_
  intro v hv
  replace hv := hv.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero]
  intro s hs
  have hsA : s ∈ Algebra.adjoin ℂ S := Algebra.subset_adjoin hs
  simp only [c', dif_pos hsA]
  exact Classical.choose_spec (scal s hsA) v hv

end GlobalTheory.AutGrowth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteKottwitzClassesPerMinpolyAEqOne
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LKCx.PeriodicClassFixedPoints

variable {p : ℕ} [Fact p.Prime]

theorem sh_mul' (G : HTGroup p) (a b : G.C) : sh G (a * b) = sh G b * sh G a := by
  simp only [sh, map_mul, MulOpposite.unop_mul]

theorem sh_one' (G : HTGroup p) : sh G 1 = 1 := by simp [sh]

theorem sh_mul_inv' (G : HTGroup p) (e : G.Cˣ) : sh G (e : G.C) * sh G ((e⁻¹ : G.Cˣ) : G.C) = 1 := by
  rw [← sh_mul', Units.inv_mul, sh_one']

theorem commute_ratio (G : HTGroup p) (β β₁ γ : G.Cˣ) (c : ℚ) (hc : c ≠ 0)
    (h : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c * β)
    (h₁ : (γ : G.C) * β₁ * sh G γ = algebraMap ℚ G.C c * β₁) :
    Commute ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) (γ : G.C) := by
  have hs : sh G γ = ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C c * β₁) := by
    rw [← h₁]; simp [mul_assoc]
  rw [hs, ← Algebra.smul_def, ← Algebra.smul_def] at h
  simp only [mul_smul_comm] at h
  have h2 : (γ : G.C) * β * (((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) * β₁) = β := smul_right_injective G.C hc h
  have h3 : (γ : G.C) * β * ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C) = β * ((β₁⁻¹ : G.Cˣ) : G.C) := by
    conv_rhs => rw [← h2]
    simp [mul_assoc]
  show (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * γ = γ * (β * ((β₁⁻¹ : G.Cˣ) : G.C))
  calc (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) * γ
      = ((γ : G.C) * β * ((β₁⁻¹ : G.Cˣ) : G.C) * ((γ⁻¹ : G.Cˣ) : G.C)) * γ := by rw [h3]
    _ = γ * (β * ((β₁⁻¹ : G.Cˣ) : G.C)) := by simp [mul_assoc]

theorem tau_ratio (G : HTGroup p) (β β₁ : G.Cˣ) (h : sh G β = β) (h₁ : sh G β₁ = β₁) :
    (β₁ : G.C) * sh G ((β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C)) * ((β₁⁻¹ : G.Cˣ) : G.C) =
      (β : G.C) * ((β₁⁻¹ : G.Cˣ) : G.C) := by
  have e : (β₁ : G.C) * sh G ((β₁⁻¹ : G.Cˣ) : G.C) = 1 := by
    conv_lhs => rw [← h₁]
    exact sh_mul_inv' G β₁
  rw [sh_mul', h, ← mul_assoc, e, one_mul]

theorem rel_of_same (G : HTGroup p) (β₁ γ₀ : G.Cˣ) (a₀ : G.C) (P Q : Pair G) (hP : P.γ = γ₀) (hQ : Q.γ = γ₀)
    (r r' : ℚˣ) (e e' : G.Cˣ) (he : Commute (e : G.C) γ₀) (he' : Commute (e' : G.C) γ₀)
    (hr : (0 < (r : ℚ)) ↔ (0 < (r' : ℚ)))
    (hPβ : (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * a₀ * β₁ * sh G (e : G.C)))
    (hQβ : (Q.β : G.C) = algebraMap ℚ G.C r' * ((e' : G.C) * a₀ * β₁ * sh G (e' : G.C))) : Pair.Rel P Q := by
  refine ⟨e' * e⁻¹, (r' : ℚ) / r, ?_, ?_, ?_⟩
  · rcases lt_or_gt_of_ne r.ne_zero with h | h
    · have hn : ¬ (0 < (r' : ℚ)) := fun h0 => absurd (hr.2 h0) (not_lt.2 h.le)
      exact div_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 hn) r'.ne_zero) h
    · exact div_pos (hr.1 h) h
  · rw [hQβ, hPβ, ← Algebra.smul_def, ← Algebra.smul_def, ← Algebra.smul_def]
    simp only [mul_smul_comm, smul_mul_assoc, smul_smul]
    have hrr : (r' : ℚ) / r * r = r' := by field_simp
    rw [hrr]
    congr 1
    rw [Units.val_mul, sh_mul']
    calc (e' : G.C) * a₀ * β₁ * sh G (e' : G.C)
        = (e' : G.C) * (((e⁻¹ : G.Cˣ) : G.C) * e) * a₀ * β₁ * (sh G (e : G.C) * sh G ((e⁻¹ : G.Cˣ) : G.C)) * sh G (e' : G.C) := by
          rw [Units.inv_mul, sh_mul_inv', mul_one, mul_one]
      _ = _ := by simp only [mul_assoc]
  · have hc : Commute ((e' * e⁻¹ : G.Cˣ) : G.C) (γ₀ : G.C) := by
      rw [Units.val_mul]; exact he'.mul_left he.units_inv_left
    ext
    rw [hP, hQ, Units.val_mul, Units.val_mul, hc.eq, mul_assoc, Units.mul_inv, mul_one]

theorem exists_point_of_term_ne_zero' {G : HTGroup p} (P : Pair G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (r : ℕ) (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) (h : P.term Kf f r K φ ≠ 0) :
    ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf),
      f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0 := by
  unfold Pair.term at h
  split_ifs at h with hd
  · unfold Pair.termAt pointSum at h
    obtain ⟨q, hq⟩ := not_forall.1 (fun hc => h (finsum_eq_zero_of_forall_eq_zero hc))
    refine ⟨_, _, P.trivAf.choose_spec.choose_spec, (Quotient.out q).1, fun h0 => hq ?_⟩
    rw [h0, zero_mul, mul_zero]
  · exact absurd rfl h

theorem finite_fixed (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ)
    (hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f) (hreg : ∀ g, f g ≠ 0 → RegAf G g)
    (γ₀ : G.Cˣ) (c₀ : ℚˣ) :
    {q : Cls G | ∃ P : Pair G, (Quot.mk Pair.Rel P : Cls G) = q ∧ P.γ = γ₀ ∧ P.c = c₀ ∧
      ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) (g : G.GAf),
        f (g⁻¹ * P.toAf x t hx P.self * g) ≠ 0}.Finite := by
  by_cases hne : ∃ P₁ : Pair G, P₁.γ = γ₀ ∧ P₁.c = c₀
  swap
  · refine Set.finite_empty.subset ?_
    rintro q ⟨P, -, hγ, hc, -⟩
    exact hne ⟨P, hγ, hc⟩
  obtain ⟨P₁, rfl, rfl⟩ := hne
  obtain ⟨S, hS⟩ := GlobalTheory.T.kottwitzPair_form_ratio_local_scalar_norm p G L f hf hreg P₁
  obtain ⟨A, hA⟩ := GlobalTheory.T.finite_fixed_unit_classes_centralizer_regular p G P₁.β P₁.sym P₁.γ P₁.c P₁.sim P₁.reg.2 P₁.reg.1 S
  let D : G.C × Bool → Pair G → Prop := fun ab P => P.γ = P₁.γ ∧ ∃ (r : ℚˣ) (e : G.Cˣ),
    Commute (e : G.C) P₁.γ ∧ decide (0 < (r : ℚ)) = ab.2 ∧
    (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * ab.1 * P₁.β * sh G (e : G.C))
  let ρ : G.C × Bool → Cls G := fun ab => if h : ∃ P, D ab P then Quot.mk _ h.choose else Quot.mk _ P₁
  refine (Finset.finite_toSet ((A ×ˢ (Finset.univ : Finset Bool)).image ρ)).subset ?_
  rintro q ⟨P, rfl, hγ, hc, x, t, hx, g, hg⟩
  have hcomm := commute_ratio G P.β P₁.β P₁.γ P₁.c P₁.c.ne_zero (by rw [← hγ, ← hc]; exact P.sim) P₁.sim
  have hτ := tau_ratio G P.β P₁.β P.sym P₁.sym
  have hu : IsUnit ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) := by
    simpa using (P.β * P₁.β⁻¹).isUnit
  obtain ⟨a₀, ha₀, r, e, he, hre⟩ := hA _ hu hcomm hτ (fun ℓ _ hℓ => hS P hγ hc x t hx g hg ℓ hℓ)
  have hβeq : (P.β : G.C) = algebraMap ℚ G.C r * ((e : G.C) * a₀ * P₁.β * sh G (e : G.C)) := by
    calc (P.β : G.C) = ((P.β : G.C) * ((P₁.β⁻¹ : G.Cˣ) : G.C)) * P₁.β := by simp [mul_assoc]
      _ = _ := by rw [hre]; simp [mul_assoc]
  have hex : ∃ P', D (a₀, decide (0 < (r : ℚ))) P' := ⟨P, hγ, r, e, he, rfl, hβeq⟩
  refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(a₀, decide (0 < (r : ℚ))),
    Finset.mem_product.2 ⟨ha₀, Finset.mem_univ _⟩, ?_⟩)
  have hρ : ρ (a₀, decide (0 < (r : ℚ))) = Quot.mk _ hex.choose := dif_pos hex
  rw [hρ]
  obtain ⟨hγ', r', e', he', hb', hβ'⟩ := hex.choose_spec
  refine Quot.sound (rel_of_same G P₁.β P₁.γ a₀ _ P hγ' hγ r' r e' e he' he ?_ hβ' hβeq)
  rw [← decide_eq_decide]; exact hb'

theorem finite_classes_of_pol_a_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ P0 : Polynomial G.F, {q : Cls G | (Quot.out q).pol = P0 ∧ (∃ μ, (Quot.out q).Mark μ) ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  intro p _ G _ L f hf hreg K' f' _ P0
  by_cases hne : {q : Cls G | (Quot.out q).pol = P0 ∧ (∃ μ, (Quot.out q).Mark μ) ∧
      (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Nonempty
  · obtain ⟨q₀, hq₀⟩ := hne
    refine ((finite_fixed G L f hf hreg (Quot.out q₀).γ (Quot.out q₀).c).union
      (finite_fixed G L f hf hreg (Quot.out q₀).γ (-(Quot.out q₀).c))).subset ?_
    intro q hq
    obtain ⟨x, t, hx, g, hg⟩ := exists_point_of_term_ne_zero' _ _ _ _ _ _ hq.2.2
    obtain ⟨y, hy⟩ := GlobalTheory.LKCx.ClsReg.units_conj_of_minpoly_eq_of_separable G (Quot.out q).γ (Quot.out q₀).γ
      (hq.1.trans hq₀.1.symm) (Quot.out q₀).reg.2 (Quot.out q₀).reg.1
    obtain ⟨P', hrel, hγ, -, htr⟩ := GlobalTheory.LKMid.Pair.exists_conj p G (Quot.out q) y⁻¹
    obtain ⟨x', hx', he⟩ := htr x t hx
    have hq' : (Quot.mk Pair.Rel P' : Cls G) = q := by
      rw [← Quot.sound hrel]; exact Quot.out_eq q
    have hγ' : P'.γ = (Quot.out q₀).γ := by
      rw [hγ]; ext
      rw [Units.val_mul, Units.val_mul, hy]
      simp [mul_assoc]
    have hg' : f (g⁻¹ * P'.toAf x' t hx' P'.self * g) ≠ 0 := by rw [he]; exact hg
    rcases GlobalTheory.LKMid.Pair.c_eq_or_eq_neg p G (Quot.out q₀) P' hγ' with hc | hc
    · exact Or.inl ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩
    · exact Or.inr ⟨P', hq', hγ', hc, x', t, hx', g, hg'⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne]; exact Set.finite_empty

end GlobalTheory.LKCx.PeriodicClassFixedPoints
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorOfCoordsEqSumMulLeftPderiv
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.CCRFock

theorem coefM_one (z : ℂ) : coefM z 1 = z := by
  simp [coefM, Complex.ext_iff]

theorem coefM_neg_one (z : ℂ) : coefM z (-1) = star z := by
  simp [coefM, Complex.ext_iff]

theorem coefD_one (z : ℂ) : coefD z 1 = -star z := by
  simp [coefD, Complex.ext_iff]

theorem coefD_neg_one (z : ℂ) : coefD z (-1) = -z := by
  simp [coefD, Complex.ext_iff]

theorem heisOp_eq_sum_mul_pderiv : ∀ {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ),
    heisOp c = ∑ l : Ix P Q × Ix R S,
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c l.1 l.2) (lineSign l.1 l.2)) •
          LinearMap.mulLeft ℂ (MvPolynomial.X l) +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c l.1 l.2) (lineSign l.1 l.2)) •
          (MvPolynomial.pderiv l).toLinearMap) := by
  intro P Q R S c
  unfold heisOp
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  rintro ⟨a, b⟩ -
  rcases a with a | a <;> rcases b with b | b <;>
    simp only [raiB, lowB, linePos, lineSign, coefM_one, coefM_neg_one, coefD_one, coefD_neg_one, if_true,
      Bool.false_eq_true, if_false] <;>
    module

end GlobalTheory.CCRFock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHeisenbergOperatorOfCoordsRealISmulSignConjO
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.HeisRot

theorem jm_eq (p q : ℕ) : Jm p q = Matrix.diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
  unfold Jm Formalism.UG.Jpq
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp

theorem jm_conj_apply {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (a : Ix P Q) (b : Ix R S) :
    (Jm P Q * c * Jm R S) a b = lineSign a b * c a b := by
  rw [jm_eq, jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem term_eq {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) (t : ℝ) (l : Ln P Q R S) :
    ((((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) l.1 l.2 • raiB l
      - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 *
          star ((((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) l.1 l.2)) • lowB l)
        (1 : Formalism.BasicNotions.TH.Pol P Q R S)
      = ((t : ℂ) * Complex.I) • ((c l.1 l.2 • raiB l
          - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 * star (c l.1 l.2)) • lowB l)
        (1 : Formalism.BasicNotions.TH.Pol P Q R S)) := by
  obtain ⟨a, b⟩ := l
  rw [Matrix.smul_apply, jm_conj_apply]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [raiB, lowB, linePos, lineSign, Complex.conj_ofReal, smul_smul] <;> ring_nf

theorem heisOp_rot_one (P Q R S : ℕ) (c : Matrix (Ix P Q) (Ix R S) ℂ) (t : ℝ) :
    heisOp (((t : ℂ) * Complex.I) • (Jm P Q * c * Jm R S)) 1 = ((t : ℂ) * Complex.I) • heisOp c 1 := by
  unfold heisOp
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sum_apply,
    Finset.sum_congr rfl (fun l _ => term_eq c t l), ← Finset.smul_sum, smul_comm]

end GlobalTheory.HeisRot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVectorIsThetaFunctionDefinitePair
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormDict

theorem fock_isThetaFunO : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  ∀ T, IsThetaFunO X.ψ X.A X.B (X.fock T) := by
  intro D cc δ t0 Q P X hX T
  exact Formalism.IndefR.Fin.ptStable D X.ψ X.θ hX.2.weil.std hX.2.inf X.A X.B (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) X.vac _ hX.2.vac_theta

end GlobalTheory.NormDict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussAbsEqISup
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice.BaseChange

theorem gaussAbs_eq_iSup {K ι : Type} [Field K] [NumberField K] (v : FinitePlace K) (g : MvPolynomial ι K)
    (s : Finset (ι →₀ ℕ)) (hs : g.support ⊆ s) (hne : s.Nonempty) :
    gaussAbs v g = ⨆ k : s, v (AddMonoidAlgebra.coeff g (k : ι →₀ ℕ)) := by
  classical
  have : Nonempty s := hne.to_subtype
  have hsup : (g.support.sup fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) = s.sup fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal := by
    refine le_antisymm (Finset.sup_mono hs) (Finset.sup_le fun m hm => ?_)
    by_cases hm' : m ∈ g.support
    · exact Finset.le_sup (f := fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) hm'
    · rw [MvPolynomial.notMem_support_iff.1 hm', map_zero, Real.toNNReal_zero]
      exact bot_le
  unfold gaussAbs
  rw [hsup]
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_sup s hne fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal
  rw [hkeq, Real.coe_toNNReal _ (apply_nonneg _ _)]
  refine le_antisymm (le_ciSup (f := fun k : s => v (AddMonoidAlgebra.coeff g (k : ι →₀ ℕ))) (Set.finite_range _).bddAbove ⟨k, hk⟩)
    (ciSup_le fun m => ?_)
  have h1 : (v (AddMonoidAlgebra.coeff g (m : ι →₀ ℕ))).toNNReal ≤ (v (AddMonoidAlgebra.coeff g k)).toNNReal := by
    rw [← hkeq]; exact Finset.le_sup (f := fun m => (v (AddMonoidAlgebra.coeff g m)).toNNReal) m.2
  have h2 := (Real.toNNReal_le_toNNReal_iff (apply_nonneg _ _)).1 h1
  exact h2

end GlobalTheory.HSChoice.BaseChange
end
end

