module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.KatoClassHeckeEulerFactorRelation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.AprojEqZeroOfUz
section
namespace UnipMove

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace AffineProjectionSplitting

variable {r : ℕ} (X : Data E r) (ξ : Fin r → E)

private lemma hermC_smul_left_dim {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E) (c : ℂ)
    (u v : Fin n → ℂ) : hermC τ G (c • u) v = c * hermC τ G u v := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private lemma hermC_sub_left_dim {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (u w v : Fin n → ℂ) : hermC τ G (u - w) v = hermC τ G u v - hermC τ G w v := by
  simp only [hermC, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma hermC_emb_emb_eq_herm {n : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) : hermC τ G (Data.emb τ x) (Data.emb τ y) = τ (herm G x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, herm, Data.emb, map_sum, map_mul, cc, IsCMField.complexEmbedding_complexConj]

lemma lineV_mem_Iperp (hξ : herm X.Gm ξ ξ = 0) (s : X.Ψ → ℂ) : X.lineV ξ s ∈ X.Iperp ξ := by
  simp only [Data.Iperp, Set.mem_setOf_eq]
  intro τ
  simp only [Data.lineV, hermC_smul_left_dim, hermC_emb_emb_eq_herm, hξ, map_zero, mul_zero]

lemma Iperp_sub {u w : X.Ψ → Fin r → ℂ} (hu : u ∈ X.Iperp ξ) (hw : w ∈ X.Iperp ξ) :
    u - w ∈ X.Iperp ξ := by
  simp only [Data.Iperp, Set.mem_setOf_eq] at hu hw ⊢
  intro τ
  rw [Pi.sub_apply, hermC_sub_left_dim, hu τ, hw τ, sub_zero]

lemma Iperp_smul (c : ℂ) {u : X.Ψ → Fin r → ℂ} (hu : u ∈ X.Iperp ξ) : c • u ∈ X.Iperp ξ := by
  simp only [Data.Iperp, Set.mem_setOf_eq] at hu ⊢
  intro τ
  rw [Pi.smul_apply, hermC_smul_left_dim, hu τ, mul_zero]

lemma aproj_eq_zero_of_Uz {x : Frame X.Ψ r} {u : X.Ψ → Fin r → ℂ} (hu : u ∈ X.Uz x ξ) :
    X.aproj x ξ u = 0 := by
  simp only [Data.Uz, Data.Iperp, Set.mem_setOf_eq] at hu
  obtain ⟨-, h2⟩ := hu
  funext τ
  have hH : X.Hf x τ (u τ) (Data.emb τ.1 ξ) = 0 := by
    have h3 := h2 τ
    simp only [Data.Jz, hermC_smul_left_dim] at h3
    rw [Data.Hf]
    exact (mul_eq_zero.mp h3).resolve_left Complex.I_ne_zero
  simp only [Data.aproj, Data.lineV, hH, zero_div, zero_smul, Pi.zero_apply]

private lemma ppos_const_smul (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (u : Fin r → ℂ) :
    X.ppos x τ (c • u) = c • X.ppos x τ u := by
  simp only [Data.ppos, hermC_smul_left_dim, Finset.smul_sum, smul_smul, Finset.mul_sum, mul_assoc]

lemma Hf_smul (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ (c • u) w = c * X.Hf x τ u w := by
  unfold Data.Hf
  rw [ppos_const_smul, smul_comm (2 : ℂ) c, ← smul_sub, hermC_smul_left_dim]

lemma aproj_smul (x : Frame X.Ψ r) (c : ℂ) (u : X.Ψ → Fin r → ℂ) :
    X.aproj x ξ (c • u) = c • X.aproj x ξ u := by
  funext τ
  simp only [Data.aproj, Data.lineV, Pi.smul_apply, Hf_smul, smul_smul, mul_div_assoc]

lemma ucomp_smul (x : Frame X.Ψ r) (c : ℂ) (u : X.Ψ → Fin r → ℂ) :
    X.ucomp x ξ (c • u) = c • X.ucomp x ξ u := by
  simp only [Data.ucomp, aproj_smul, smul_sub]

end AffineProjectionSplitting

lemma split_key {r : ℕ} {X : DataX E r} {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0)
    {z1 z : Frame X.Ψ r} {δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ}
    (hap : ∀ u ∈ X.Iperp ξ, X.aproj z ξ u = X.aproj z1 ξ u - X.lineV ξ (fun τ => δ τ (X.ucomp z1 ξ u τ)))
    (hJ : ∀ u ∈ X.Uz z1 ξ, X.ucomp z ξ (X.Jz z1 u) = X.Jz z (X.ucomp z ξ u))
    {v : X.Ψ → Fin r → ℂ} (hv : v ∈ X.Iperp ξ) (c : ℂ)
    (h1 : X.Jz z1 (X.ucomp z1 ξ v) = c • X.ucomp z1 ξ v) :
    X.Jz z (X.ucomp z ξ v) = c • X.ucomp z ξ v := by
  have hwI : X.ucomp z1 ξ v ∈ X.Iperp ξ :=
    AffineProjectionSplitting.Iperp_sub X.toData ξ hv (AffineProjectionSplitting.lineV_mem_Iperp X.toData ξ hξ _)
  have hUz : X.ucomp z1 ξ v ∈ X.Uz z1 ξ := by
    simp only [Data.Uz, Set.mem_setOf_eq]
    refine ⟨hwI, ?_⟩
    rw [h1]
    exact AffineProjectionSplitting.Iperp_smul X.toData ξ c hwI
  have h0 : X.aproj z1 ξ (X.ucomp z1 ξ v) = 0 := AffineProjectionSplitting.aproj_eq_zero_of_Uz X.toData ξ hUz
  have hu1 : X.ucomp z1 ξ (X.ucomp z1 ξ v) = X.ucomp z1 ξ v := by
    show X.ucomp z1 ξ v - X.aproj z1 ξ (X.ucomp z1 ξ v) = _
    rw [h0, sub_zero]
  have hEq : X.ucomp z ξ (X.ucomp z1 ξ v) = X.ucomp z ξ v := by
    have e1 := hap _ hwI
    have e2 := hap _ hv
    show X.ucomp z1 ξ v - X.aproj z ξ (X.ucomp z1 ξ v) = v - X.aproj z ξ v
    rw [e1, e2, h0, hu1]
    show v - X.aproj z1 ξ v - (0 - _) = v - (X.aproj z1 ξ v - _)
    abel
  have hJ1 := hJ _ hUz
  rw [h1, AffineProjectionSplitting.ucomp_smul, hEq] at hJ1
  exact hJ1.symm

theorem sSplit : SSplit E := by
  unfold SSplit
  intro r X ξ La z1 z lam δ hiso hsd hap hJ
  have hξ : herm X.Gm ξ ξ = 0 := by
    have h := hiso
    simp only [Data.IsIso] at h
    exact h.2.1
  unfold SplitData at hsd ⊢
  obtain ⟨hA, hB, hC, hD, hF, hG⟩ := hsd
  have hv : ∀ j, X.embV (lam j) ∈ X.Iperp ξ := fun j => by
    simp only [Data.Iperp, Set.mem_setOf_eq]
    intro τ
    simp only [Data.embV, AffineProjectionSplitting.hermC_emb_emb_eq_herm, (hA j).2, map_zero]
  refine ⟨hA, hB, hC, fun j hj => ⟨(hD j hj).1, ?_⟩, fun j hj => ⟨(hF j hj).1, ?_⟩, hG⟩
  · exact split_key hξ hap hJ (hv j) I (hD j hj).2
  · have h2 := split_key hξ hap hJ (hv j) (-I) (by rw [(hF j hj).2, neg_smul])
    rw [h2, neg_smul]

end

end UnipMove
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.HermLinApply
section
namespace UnipMove

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace DeltaValuation

def linF {r : ℕ} (c : Fin r → ℂ) : (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun v := ∑ a, v a * c a
  map_add' u v := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' k v := by simp [Finset.mul_sum, mul_assoc]

lemma linF_apply {r : ℕ} (c : Fin r → ℂ) (v : Fin r → ℂ) : linF c v = ∑ a, v a * c a := rfl

def hermLin {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (K : ℂ) (w : Fin r → ℂ) :
    (Fin r → ℂ) →ₗ[ℂ] ℂ where
  toFun v := K * hermC τ G v w
  map_add' u v := by rw [hermC_add_left]; ring
  map_smul' k v := by rw [hermC_smul_left]; simp only [smul_eq_mul, RingHom.id_apply]; ring

lemma hermLin_apply {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (K : ℂ) (w v : Fin r → ℂ) :
    hermLin τ G K w v = K * hermC τ G v w := rfl

lemma posPart_smul {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.posPart x τ (c • v) = Complex.normSq c * X.posPart x τ v := by
  unfold Data.posPart
  simp only [hermC_smul_left, map_mul]
  have e : ∀ p q m : ℂ, c * p * m * (conj c * conj q) = (Complex.normSq c : ℂ) * (p * m * conj q) := by
    intro p q m
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  simp only [e, ← Finset.mul_sum]
  rw [Complex.re_ofReal_mul]

lemma maj_smul {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.maj x τ (c • v) = Complex.normSq c * X.maj x τ v := by
  unfold Data.maj
  rw [posPart_smul, hermC_smul_left, hermC_smul_right]
  have e : c * (conj c * hermC τ.1 X.Gm v v) = (Complex.normSq c : ℂ) * hermC τ.1 X.Gm v v := by
    rw [Complex.normSq_eq_conj_mul_self]
    ring
  rw [e, Complex.re_ofReal_mul]
  ring

lemma O_smul {r : ℕ} (β : 𝓞 E) (v : Fin r → E) : β • v = (β : E) • v := rfl

end DeltaValuation

open DeltaValuation in
theorem sDelta_of (hemb : SEmb E) (hext : SExt E) (hdual : SDual E)
    (hP5 : IsotropicCoefficientSplitting (E := E)) (hP6 : NoShortVectorLowerBound (E := E)) : SDelta E := by
  intro r X ξ z1 ep n' hiso hep hn' hz1 hsep
  have hΛp : ∀ μ, μ ∈ X.Λp ξ ↔ μ ∈ X.Λ ∧ herm X.Gm μ ξ = 0 := fun μ => by
    simp only [Data.Λp, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker]
    rfl
  have hlin : ∀ (b : E) (x y : Fin r → E), herm X.Gm (b • x) y = b * herm X.Gm x y := by
    intro b x y
    simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  obtain ⟨f, hfΛ, hfadd, hfsmul, hfξ⟩ := hP5 r X.toData ξ hiso
  obtain ⟨F, hF⟩ := hext r X.toData ξ f hfadd hfsmul
  obtain ⟨cf, hFc⟩ : ∃ cf : Fin r → E, ∀ x, F x = ∑ a, x a * cf a :=
    ⟨fun a => F (fun j => if a = j then 1 else 0), fun x => by
      rw [LinearMap.pi_apply_eq_sum_univ F x]; simp only [smul_eq_mul]⟩
  have hFξ : F ξ = 1 := by
    have h1 : (1 : E) • ξ ∈ X.Λ := by rw [one_smul]; exact hiso.1
    have h2 : (1 : E) • ξ ∈ X.Λp ξ := (hΛp _).2 ⟨h1, by rw [one_smul]; exact hiso.2.1⟩
    have h3 := hF _ h2
    rw [hfξ 1 h1, one_smul] at h3
    exact h3
  have hn0 : (n' : ℂ) ≠ 0 := by exact_mod_cast hn'.ne'
  let δ₀ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ := fun τ => (-(n' : ℂ)) • linF (fun a => τ.1 (cf a))
  obtain ⟨μ₀, hμ₀, hbound⟩ := hP6 r X ξ ep hiso hep z1 hz1 hsep δ₀
  let δ' : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ := fun τ =>
    δ₀ τ - hermLin τ.1 X.Gm ((dE E : ℂ) * (-τ.1 X.ξ0)) (X.ucomp z1 ξ (X.embV μ₀) τ)
  refine ⟨fun τ => ((n' : ℂ)⁻¹) • δ' τ, ?_, ?_⟩
  · intro u hu τ
    have hb := hbound u hu τ
    have e1 : (((n' : ℂ)⁻¹ • δ' τ) (u τ)) • Data.emb τ.1 ξ = ((n' : ℂ)⁻¹) •
        ((δ₀ τ (u τ) - (dE E : ℂ) * (-τ.1 X.ξ0) *
          hermC τ.1 X.Gm (u τ) (X.ucomp z1 ξ (X.embV μ₀) τ)) • Data.emb τ.1 ξ) := by
      simp only [δ', LinearMap.smul_apply, LinearMap.sub_apply, hermLin_apply, smul_eq_mul, smul_smul]
    have hinv : ((n' : ℂ)⁻¹) = (((n' : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [e1, maj_smul, hinv, Complex.normSq_ofReal, div_pow]
    have hpos : (0 : ℝ) ≤ (n' : ℝ)⁻¹ * (n' : ℝ)⁻¹ := by positivity
    calc (n' : ℝ)⁻¹ * (n' : ℝ)⁻¹ * X.maj z1 τ ((δ₀ τ (u τ) - (dE E : ℂ) * (-τ.1 X.ξ0) *
          hermC τ.1 X.Gm (u τ) (X.ucomp z1 ξ (X.embV μ₀) τ)) • Data.emb τ.1 ξ)
        ≤ (n' : ℝ)⁻¹ * (n' : ℝ)⁻¹ *
          (frameIndexBound r (fdeg E) (dE E) (rdE E) X.NA X.NC ep ^ 2 * X.maj z1 τ (u τ)) :=
          mul_le_mul_of_nonneg_left hb hpos
      _ = _ := by ring
  · intro μ hμ
    obtain ⟨hμΛ, hμξ⟩ := (hΛp μ).1 hμ
    obtain ⟨hμ₀Λ, hμ₀ξ⟩ := (hΛp μ₀).1 hμ₀
    obtain ⟨α, hα⟩ := hdual (-X.ξ0 * herm X.Gm μ μ₀) (by
      intro a
      have ha : (a : E) • μ ∈ X.Λ := by rw [← O_smul]; exact X.Λ.smul_mem a hμΛ
      obtain ⟨k, hk⟩ := X.EF_int _ ha μ₀ hμ₀Λ
      refine ⟨k, ?_⟩
      rw [← hk, EFf, hlin]
      congr 1
      ring)
    refine ⟨(n' : E) * f μ + α, ?_, ?_⟩
    · rw [add_smul, mul_smul]
      refine X.Λ.add_mem ?_ ?_
      · rw [Nat.cast_smul_eq_nsmul]
        exact nsmul_mem (hfΛ μ hμ) n'
      · rw [← O_smul]
        exact X.Λ.smul_mem α hiso.1
    · funext τ
      have hu : ∀ ν : Fin r → E, X.ucomp z1 ξ (X.embV ν) τ = Data.emb τ.1 ν -
          (X.Hf z1 τ (Data.emb τ.1 ν) (Data.emb τ.1 ξ) / X.Hf z1 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)) •
            Data.emb τ.1 ξ := fun ν => rfl
      have h1 : hermC τ.1 X.Gm (Data.emb τ.1 μ) (Data.emb τ.1 μ₀) = τ.1 (herm X.Gm μ μ₀) :=
        hermC_emb _ _ _ _
      have h2 : hermC τ.1 X.Gm (Data.emb τ.1 μ) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hμξ, map_zero]
      have h3 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 μ₀) = 0 := by
        rw [← hermC_conj τ.1 X.Gm_herm, hermC_emb, hμ₀ξ, map_zero, map_zero]
      have h4 : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
        rw [hermC_emb, hiso.2.1, map_zero]
      have hherm : hermC τ.1 X.Gm (X.ucomp z1 ξ (X.embV μ) τ) (X.ucomp z1 ξ (X.embV μ₀) τ) =
          τ.1 (herm X.Gm μ μ₀) := by
        rw [hu, hu]
        simp only [hermC_sub_left, hermC_sub_right, hermC_smul_left, hermC_smul_right, h1, h2, h3, h4]
        ring
      have hl1 : linF (fun a => τ.1 (cf a)) (Data.emb τ.1 μ) = τ.1 (F μ) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [linF_apply, hFc, map_sum]
        simp only [Data.emb, map_mul]
      have hl2 : linF (fun a => τ.1 (cf a)) (Data.emb τ.1 ξ) = 1 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [linF_apply, show (1 : ℂ) = τ.1 (F ξ) by rw [hFξ, map_one], hFc, map_sum]
        simp only [Data.emb, map_mul]
      set co := X.Hf z1 τ (Data.emb τ.1 μ) (Data.emb τ.1 ξ) /
        X.Hf z1 τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with hco
      have hδ' : δ' τ (X.ucomp z1 ξ (X.embV μ) τ) =
          -(n' : ℂ) * (τ.1 (F μ) - co) - (dE E : ℂ) * (-τ.1 X.ξ0) * τ.1 (herm X.Gm μ μ₀) := by
        simp only [δ', δ₀, LinearMap.sub_apply, LinearMap.smul_apply, hermLin_apply, smul_eq_mul]
        rw [hherm, hu μ, map_sub, map_smul, hl1, hl2, smul_eq_mul, mul_one]
      have hL : ((n' : ℂ) • (X.aproj z1 ξ (X.embV μ) - X.lineV ξ (fun τ =>
          (((n' : ℂ)⁻¹) • δ' τ) (X.ucomp z1 ξ (X.embV μ) τ)))) τ =
          ((n' : ℂ) * (co - (n' : ℂ)⁻¹ * δ' τ (X.ucomp z1 ξ (X.embV μ) τ))) • Data.emb τ.1 ξ := by
        show (n' : ℂ) • (co • Data.emb τ.1 ξ -
          (((n' : ℂ)⁻¹) • δ' τ) (X.ucomp z1 ξ (X.embV μ) τ) • Data.emb τ.1 ξ) = _
        rw [LinearMap.smul_apply, smul_eq_mul, ← sub_smul, smul_smul]
      have hR : X.embV (((n' : E) * f μ + α) • ξ) τ = (τ.1 ((n' : E) * f μ + α)) • Data.emb τ.1 ξ := by
        funext a
        simp [Data.embV, Data.emb, map_mul]
      have hdE : ((dE E : ℝ) : ℂ) = (((NumberField.discr E).natAbs : ℕ) : ℂ) := by
        have : (((NumberField.discr E).natAbs : ℕ) : ℝ) = |((NumberField.discr E : ℤ) : ℝ)| := by
          rw [Nat.cast_natAbs, Int.cast_abs]
        rw [dE, ← this]
        push_cast
        rfl
      rw [hL, hR]
      congr 1
      rw [hδ', hF μ hμ, map_add (f := _), map_mul, map_natCast, hα, map_mul, map_natCast, map_mul, map_neg, hdE]
      field_simp
      ring

end

end UnipMove
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.HermSmulLeft
section
namespace UnipMove

open ReciprocityTheory.ChartRestriction.G.FD NumberField
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma herm_smul_left' {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem sExt : SExt E := by
  intro r X ξ f hadd hsm
  classical
  have hsmul_mem : ∀ (α : 𝓞 E) (x : Fin r → E), x ∈ X.Λp ξ → (α : E) • x ∈ X.Λp ξ := by
    intro α x hx
    simp only [Data.Λp, AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, AddMonoidHom.mem_ker] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    refine ⟨?_, ?_⟩
    · have h3 := X.Λ.smul_mem α h1
      rwa [algebra_compatible_smul E α x] at h3
    · change herm X.Gm ((α : E) • x) ξ = 0
      change herm X.Gm x ξ = 0 at h2
      rw [herm_smul_left', h2, mul_zero]
  let N0 : Submodule (𝓞 E) (Fin r → E) :=
    { carrier := X.Λp ξ
      add_mem' := fun ha hb => (X.Λp ξ).add_mem ha hb
      zero_mem' := (X.Λp ξ).zero_mem
      smul_mem' := fun α x hx => by
        rw [algebra_compatible_smul E α x]
        exact hsmul_mem α x hx }
  let fL : N0 →ₗ[𝓞 E] E :=
    { toFun := fun x => f x
      map_add' := fun x y => hadd x x.2 y y.2
      map_smul' := fun α x => by
        change f (α • (x : Fin r → E)) = α • f x
        rw [algebra_compatible_smul E α (x : Fin r → E), hsm α x x.2, Algebra.smul_def] }
  obtain ⟨s, hsM, hspan, hli⟩ := exists_linearIndependent E (X.Λp ξ : Set (Fin r → E))
  have hli' : LinearIndepOn E id s := hli
  let B := Module.Basis.extend (K := E) (s := s) hli'
  let F : (Fin r → E) →ₗ[E] E := B.constr E (fun v => if (v : Fin r → E) ∈ s then f v else 0)
  have hFs : ∀ v ∈ s, F v = f v := by
    intro v hv
    have hv' : v ∈ LinearIndepOn.extend hli' (Set.subset_univ s) := Module.Basis.subset_extend hli' hv
    have h1 := B.constr_basis E (fun v => if (v : Fin r → E) ∈ s then f v else 0) ⟨v, hv'⟩
    have h2 : B ⟨v, hv'⟩ = v := by simp [B, Module.Basis.coe_extend]
    rw [h2] at h1
    change B.constr E (fun v => if (v : Fin r → E) ∈ s then f v else 0) v = f v
    rw [h1]
    simp [hv]
  refine ⟨F, fun μ hμ => ?_⟩
  have hμs : μ ∈ Submodule.span E s := by
    rw [hspan]
    exact Submodule.subset_span hμ
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.1 hμs
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (𝓞 E)⁰ c
  have hd' : ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = (d : 𝓞 E) • c i := fun i =>
    RingHom.mem_rangeS.1 (hd i)
  choose a ha using hd'
  have hgM : ∀ i, ((g i : Fin r → E)) ∈ X.Λp ξ := fun i => hsM (g i).2
  have hdE : algebraMap (𝓞 E) E (d : 𝓞 E) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
  have hFμ : F μ = ∑ i, c i * f (g i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hFs _ (g i).2, smul_eq_mul]
  have hdμ : algebraMap (𝓞 E) E (d : 𝓞 E) • μ = ∑ i, algebraMap (𝓞 E) E (a i) • (g i : Fin r → E) := by
    rw [← hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha i, smul_smul, Algebra.smul_def (d : 𝓞 E) (c i)]
  have hmemd : algebraMap (𝓞 E) E (d : 𝓞 E) • μ ∈ N0 := hsmul_mem (d : 𝓞 E) μ hμ
  have hfd : f (algebraMap (𝓞 E) E (d : 𝓞 E) • μ) = ∑ i, algebraMap (𝓞 E) E (a i) * f (g i) := by
    have h1 : (⟨_, hmemd⟩ : N0) = ∑ i, a i • (⟨g i, hgM i⟩ : N0) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [hdμ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [algebra_compatible_smul E (a i)]
    have h2 := congrArg fL h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h2
    change f _ = _ at h2
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, Algebra.smul_def]
    rfl
  have h3 : algebraMap (𝓞 E) E (d : 𝓞 E) * f μ = algebraMap (𝓞 E) E (d : 𝓞 E) * F μ := by
    rw [← hsm (d : 𝓞 E) μ hμ, hfd, hFμ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha i, Algebra.smul_def, mul_assoc]
  exact (mul_left_cancel₀ hdE h3).symm

end UnipMove
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.UnipotentMoves.SDual
section
namespace UnipMove

open ReciprocityTheory.ChartRestriction.G.FD NumberField
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sDual : SDual E := by
  intro t ht
  have hb : ∀ i, IsIntegral ℤ (NumberField.integralBasis E i) := by
    intro i
    rw [NumberField.integralBasis_apply]
    exact (NumberField.RingOfIntegers.basis E i).isIntegral_coe
  have hx : t ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro a ha
    obtain ⟨y, rfl⟩ := Submodule.mem_one.1 ha
    obtain ⟨k, hk⟩ := ht y
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply]
    rw [show algebraMap (𝓞 E) E y = (y : E) from rfl, hk]
    simp
  have h1 : (1 : E) ∈ (1 : Submodule (𝓞 E) E) := Submodule.mem_one.2 ⟨1, map_one _⟩
  have hI := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ)
    (1 : Submodule (𝓞 E) E) hb h1 hx
  rw [← NumberField.coe_discr, Algebra.smul_def, mul_one, map_intCast] at hI
  let α : 𝓞 E := ⟨_, hI⟩
  have hα : (α : E) = (NumberField.discr E : E) * t := rfl
  rcases Int.natAbs_eq (NumberField.discr E) with h | h
  · refine ⟨α, ?_⟩
    have h' : ((NumberField.discr E : ℤ) : E) = (((NumberField.discr E).natAbs : ℤ) : E) :=
      congrArg _ h
    rw [hα, h', Int.cast_natCast]
  · refine ⟨-α, ?_⟩
    have h' : ((NumberField.discr E : ℤ) : E) = ((-((NumberField.discr E).natAbs : ℤ) : ℤ) : E) :=
      congrArg _ h
    show -(α : E) = _
    rw [hα, h', Int.cast_neg, Int.cast_natCast]
    ring

end UnipMove
end

