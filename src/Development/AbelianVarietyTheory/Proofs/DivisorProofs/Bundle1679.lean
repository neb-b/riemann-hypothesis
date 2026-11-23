module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1662
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1222
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1664
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlphaHFinIdlIncU
section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl finIdl_incU)

noncomputable section

namespace GlobalTheory.BottomReal

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem xiH_finIdl_incU {μ₀ : T} (hL : L.Is μ₀) (t : T) (a : D.host.Eˣ) :
    (L.xiH t).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) = 1 := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h1 := (L.xiH t).2.2 a
  rw [← GlobalTheory.Mem.ChiLaws.infDiag_mul_finPart, map_mul, ← finIdl_incU] at h1
  have h2 := HChar.inf_eq_one_of_order hn ho a
  rw [HChar.inf, MonoidHom.comp_apply] at h2
  rw [h2, one_mul] at h1
  exact h1

theorem nuH_finIdl_incU {μ₀ : T} (hL : L.Is μ₀) (t t' : T) (i j : Fin D.R.m) (a : D.host.Eˣ) :
    (nuH G t i j).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) =
      (nuH G t' i j).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) := by
  simp only [nuH, Subgroup.coe_div, Subgroup.coe_mul, MonoidHom.div_apply, MonoidHom.mul_apply,
    xiH_finIdl_incU hL t a, xiH_finIdl_incU hL t' a]

theorem prod_pow_eq {N : ℕ} (χ : HeckeU D N) (e : ℤ) (ν : HChar D.host.E) (hf : ∀ x, χ.f x ^ e = (ν⁻¹).1 (finIdl D x))
    (a : D.host.E) (ha : a ≠ 0) :
    ∏ τ, (Formalism.L2.Host.embTau D τ a / ((‖Formalism.L2.Host.embTau D τ a‖ : ℝ) : ℂ)) ^ (e * χ.n τ) =
      ((ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D (Units.mk0 a ha))) : ℂˣ) : ℂ) := by
  set u := Units.mk0 a ha
  set φ := Formalism.L2.Host.embTau D
  have hA : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) *
      ∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ) = 1 := χ.aut u
  have hB := congrArg (fun z : ℂˣ => (z : ℂ)) (hf (GlobalTheory.NormSum.UnramHecke.incU D u))
  simp only [Units.val_zpow_eq_zpow_val] at hB
  have hB' : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) ^ e =
      (((ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D u))) : ℂˣ) : ℂ)⁻¹ := by
    rw [← Units.val_inv_eq_inv_val]
    exact hB
  have hX : ((χ.f (Units.map (inc D).toMonoidHom u) : ℂˣ) : ℂ) = (∏ τ, (φ τ a / ((‖φ τ a‖ : ℝ) : ℂ)) ^ (χ.n τ))⁻¹ :=
    eq_inv_of_mul_eq_one_left hA
  rw [hX, inv_zpow', ← Finset.prod_zpow] at hB'
  simp_rw [mul_comm e, zpow_mul]
  have := congrArg (·⁻¹) hB'
  simp only [inv_inv] at this
  rw [← this, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_neg, neg_neg]

theorem alphaH_finIdl_incU {μ₀ : T} (hL : L.Is μ₀) (t t' : T) (i j : Fin D.R.m) (a : D.host.Eˣ) :
    (alphaH L t i j).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) =
      (alphaH L t' i j).1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) := by
  simp only [alphaH, Subgroup.coe_mul, MonoidHom.mul_apply, xiH_finIdl_incU hL t a, xiH_finIdl_incU hL t' a]

theorem exps_eq_of {N N₁ : ℕ} (χ : HeckeU D N) (χ₁ : HeckeU D N₁) (e e₁ : ℤ) (ν ν₁ : HChar D.host.E)
    (hν : ∀ a : D.host.Eˣ, ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) =
      ν₁.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)))
    (hf : ∀ x, χ.f x ^ e = (ν⁻¹).1 (finIdl D x)) (hf₁ : ∀ x, χ₁.f x ^ e₁ = (ν₁⁻¹).1 (finIdl D x)) (τ : D.what₂.Tau) :
    e * χ.n τ = e₁ * χ₁.n τ := by
  have hc := GlobalTheory.SplitWeight.exps_eq_zero (Formalism.L2.Host.embTau D) (GlobalTheory.SplitWeight.embTau_inj D)
    (GlobalTheory.SplitWeight.embTau_ne_conj D) (fun τ => e * χ.n τ - e₁ * χ₁.n τ) (fun a ha => by
      have hne : ∀ τ, Formalism.L2.Host.embTau D τ a / ((‖Formalism.L2.Host.embTau D τ a‖ : ℝ) : ℂ) ≠ 0 := fun τ =>
        div_ne_zero (by simpa using ha) (by exact_mod_cast norm_ne_zero_iff.2 (by simpa using ha))
      simp_rw [zpow_sub₀ (hne _), Finset.prod_div_distrib, prod_pow_eq χ e _ hf a ha, prod_pow_eq χ₁ e₁ _ hf₁ a ha, hν]
      exact div_self (Units.ne_zero _))
  have h := congrFun hc τ
  simpa [sub_eq_zero] using h

theorem pair_real_eq {δ t0 δ₁ t₁ : ℂ} {Q Q₁ : ℕ} (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (P₁ : GlobalTheory.NormSum.Pair D ⊤ δ₁ t₁ Q₁)
    (ν ν₁ : HChar D.host.E) (hν : ∀ a : D.host.Eˣ, ν.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)) =
      ν₁.1 (finIdl D (GlobalTheory.NormSum.UnramHecke.incU D a)))
    (hf : ∀ x, P.W.chV'.f x ^ P.W.ep' = (ν⁻¹).1 (finIdl D x))
    (hf₁ : ∀ x, P₁.W.chV'.f x ^ P₁.W.ep' = (ν₁⁻¹).1 (finIdl D x)) (hd : P.d = P₁.d) :
    (∀ τ, P.W.ep' * P.W.chV'.n τ = P₁.W.ep' * P₁.W.chV'.n τ) ∧ P.n = P₁.n := by
  have h := exps_eq_of P.W.chV' P₁.W.chV' P.W.ep' P₁.W.ep' ν ν₁ hν hf hf₁
  refine ⟨h, funext fun τ => ?_⟩
  have h1 := P.wt τ
  have h2 := P₁.wt τ
  rw [h τ, hd] at h1
  have : (P.n τ : ℤ) = P₁.n τ := by omega
  exact_mod_cast this

theorem bottom_real_eq {μ₀ : T} (hL : L.Is μ₀) {i j : Fin D.R.m} {t t' : T} {𝔪 𝔪₁ : Ideal (𝓞 D.host.E)}
    {δ t0 δ₁ t₁ : ℂ} {Q Q₁ : ℕ} {P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q} {P₁ P₁' : GlobalTheory.NormSum.Pair D ⊤ δ₁ t₁ Q₁}
    (h : IsBottom G t i j 𝔪 P P') (h₁ : IsBottom G t' i j 𝔪₁ P₁ P₁') :
    (P.a = P₁.a ∧ P.d = P₁.d ∧ P.n = P₁.n ∧ (∀ τ, P.W.ep' * P.W.chV'.n τ = P₁.W.ep' * P₁.W.chV'.n τ) ∧
        ∀ τ, P.W.ep * P.W.chV.n τ = P₁.W.ep * P₁.W.chV.n τ) ∧
      (P'.a = P₁'.a ∧ P'.d = P₁'.d ∧ P'.n = P₁'.n ∧ (∀ τ, P'.W.ep' * P'.W.chV'.n τ = P₁'.W.ep' * P₁'.W.chV'.n τ) ∧
        ∀ τ, P'.W.ep * P'.W.chV.n τ = P₁'.W.ep * P₁'.W.chV.n τ) := by
  obtain ⟨ha, ha', hd, hd'⟩ := h.rank
  obtain ⟨hb, hb', he, he'⟩ := h₁.rank
  have hν := nuH_finIdl_incU G hL t t' i j
  have hdd : P.d = P₁.d := by rw [hd, he]
  have hdd' : P'.d = P₁'.d := by rw [hd', he', hdd]
  obtain ⟨r1, r2⟩ := pair_real_eq P P₁ _ _ hν h.chars.2 h₁.chars.2 hdd
  obtain ⟨r1', r2'⟩ := pair_real_eq P' P₁' _ _ hν h.chars'.2 h₁.chars'.2 hdd'
  refine ⟨⟨by rw [ha, hb], hdd, r2, r1, ?_⟩, ⟨by rw [ha', hb'], hdd', r2', r1', ?_⟩⟩
  · exact exps_eq_of P.W.chV P₁.W.chV P.W.ep P₁.W.ep _ _ (fun _ => rfl) h.chars.1 h₁.chars.1
  · refine exps_eq_of P'.W.chV P₁'.W.chV P'.W.ep P₁'.W.ep (alphaH L t i j)⁻¹ (alphaH L t' i j)⁻¹ (fun a => ?_)
      (fun x => by rw [inv_inv]; exact h.chars'.1 x) (fun x => by rw [inv_inv]; exact h₁.chars'.1 x)
    show ((alphaH L t i j).1 _)⁻¹ = ((alphaH L t' i j).1 _)⁻¹
    rw [alphaH_finIdl_incU hL t t' i j a]

end GlobalTheory.BottomReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanThetaLocalAction
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.ArchPure

open Matrix

variable {F : Type} [Field F] [NumberField F]

def mk (a : Ainf F) (b : Af F) : AF F := (a, b)

theorem evI_fin (b : Af F) : evI F (((0 : Ainf F), b) : AF F) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
  exact map_zero _

theorem snd_of_at {z : AF F} (hz : At (evI F) z) : z.2 = 0 := by
  have h := hz (((0 : Ainf F), (1 : Af F)) : AF F) (evI_fin 1)
  have h2 : (1 : Af F) * z.2 = 0 := congrArg Prod.snd h
  rwa [one_mul] at h2

theorem slice {κ : Type} [Fintype κ] (c : κ → Af F) :
    ∀ Ψ ∈ schA F κ, ∃ f' : SInf F κ, ∀ s : κ → mixedEmbedding.mixedSpace F,
      Ψ (fun i => mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (s i)) (c i)) = f' s := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, -, rfl⟩ := hx
    refine ⟨g c • f, fun s => ?_⟩
    simp only [pureA, mk, RingEquiv.apply_symm_apply, SchwartzMap.smul_apply, smul_eq_mul,
      mul_comm]
  | zero => exact ⟨0, fun s => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨f1, h1⟩ := hx
    obtain ⟨f2, h2⟩ := hy
    exact ⟨f1 + f2, fun s => by rw [Pi.add_apply, h1, h2, SchwartzMap.add_apply]⟩
  | smul a x _ hx =>
    obtain ⟨f1, h1⟩ := hx
    exact ⟨a • f1, fun s => by rw [Pi.smul_apply, h1, SchwartzMap.smul_apply]⟩

theorem locA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ (C K : Set (κ → Af F)), IsCompact C ∧ IsOpen K ∧ (0 : κ → Af F) ∈ K ∧
      (∀ x : κ → AF F, Φ x ≠ 0 → (fun i => (x i).2) ∈ C) ∧
      ∀ x x' : κ → AF F, (∀ i, (x i).1 = (x' i).1) → (fun i => (x' i).2 - (x i).2) ∈ K → Φ x' = Φ x := _root_.GlobalTheory.FinLocSchA.compact_support_locally_constant_fin

theorem locB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (C K : Set (κ → Af F)), IsCompact C → IsOpen K → (0 : κ → Af F) ∈ K →
    ∀ y : κ → AF F, ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, ∀ i, (b i).1 = 0) ∧
      ∑ b ∈ s, c b * ψ (y ⬝ᵥ b) = 1 ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ C → (∀ k ∈ K, (fun i => (x i).2) ≠ (fun i => (y i).2) + k) →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = 0 := _root_.GlobalTheory.FinCharCut.fin_char_cut

theorem fibre : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (T : Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ → (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) →
    (∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) → T Φ y = 0 := by
  intro F _ _ κ _ ψ T hψ hkeep hcomm Φ hΦ y hy
  obtain ⟨C, K, hC, hK, hK0, hsupp, hinv⟩ := locA Φ hΦ
  obtain ⟨s, c, hs, hy1, hm⟩ := locB ψ hψ C K hC hK hK0 y
  have hu0 : evI F (mk 0 1) = 0 := evI_fin 1
  have hub : ∀ b ∈ s, (mk 0 1 : AF F) • b = b := fun b hb => funext fun i =>
    Prod.ext (show (0 : Ainf F) * (b i).1 = (b i).1 by rw [zero_mul, hs b hb i])
      (show (1 : Af F) * (b i).2 = (b i).2 from one_mul _)
  have hsch : ∀ (b : κ → AF F) (Ψ : (κ → AF F) → ℂ), schr ψ (0, b) Ψ = fun x => ψ (x ⬝ᵥ b) * Ψ x :=
    fun b Ψ => funext fun x => by simp [schr]
  have hfac : ∀ (Ψ : (κ → AF F) → ℂ) x, (∑ b ∈ s, c b • schr ψ (0, b) Ψ) x = (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Ψ x := by
    intro Ψ x
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Pi.smul_apply, hsch, smul_eq_mul]
    ring
  have hzero : (∑ b ∈ s, c b • schr ψ (0, b) Φ) = 0 := by
    funext x
    rw [hfac, Pi.zero_apply]
    by_cases hx : Φ x = 0
    · rw [hx, mul_zero]
    · refine mul_eq_zero_of_left (hm x (hsupp x hx) fun k hk he => hx ?_) _
      have hk' : (fun i => (x i).2 - (y i).2) = k := funext fun i => by
        rw [congrFun he i, Pi.add_apply]
        abel
      have e1 : Φ x = Φ (fun i => mk (x i).1 (y i).2) := hinv _ _ (fun i => rfl) (by rw [← hk'] at hk; exact hk)
      rw [e1]
      have hz : At (evI F) (fun i => mk ((x i).1 - (y i).1) (0 : Af F)) := by
        intro u' hu'
        have h1 : u'.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hu'
        funext i
        exact Prod.ext (show u'.1 * ((x i).1 - (y i).1) = 0 by rw [h1, zero_mul])
          (show u'.2 * (0 : Af F) = 0 from mul_zero _)
      have e2 := hy _ hz
      have e3 : y + (fun i => mk ((x i).1 - (y i).1) (0 : Af F)) = fun i => mk (x i).1 (y i).2 := by
        funext i
        exact Prod.ext (show (y i).1 + ((x i).1 - (y i).1) = (x i).1 by abel)
          (show (y i).2 + 0 = (y i).2 from add_zero _)
      rwa [e3] at e2
  have hT : T (∑ b ∈ s, c b • schr ψ (0, b) Φ) = ∑ b ∈ s, c b • schr ψ (0, b) (T Φ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [map_smul]
    congr 1
    have := hcomm (mk 0 1) hu0 0 b Φ hΦ
    rwa [smul_zero, hub b hb] at this
  have e := congrFun hT y
  rw [hzero, map_zero, Pi.zero_apply, hfac, hy1, one_mul] at e
  exact e.symm

end GlobalTheory.ArchPure

namespace GlobalTheory.ArchPure

open Matrix

theorem arch_pure : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (g : UA σ G.V'.J) (h : UA σ G.W.J), At (evI F) (mat g - 1) → At (evI F) (mat h - 1) →
    ∀ (f : SInf F (Fin a' × Fin (a + a'))) (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ),
    (∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w)) → (∀ᶠ w in Filter.cofinite, φ w = G.M'.vac w) →
    ∃ f₂ : SInf F (Fin a' × Fin (a + a')), om' (g, h) (pure f φ) = pure f₂ φ := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT g h hg hh f φ hφ hstd
  have hW := IsUWeilPair.isUSplitting hT.weil'
  set T := om' (g, h) with hTdef
  have hkeep : ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), T Φ ∈ schA F _ := fun Φ hΦ => hW.pres (g, h) Φ hΦ
  have hcomm : ∀ u : AF F, evI F u = 0 → ∀ p q : Fin a' × Fin (a + a') → AF F, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')),
      T (schr B.ψ (u • p, u • q) Φ) = schr B.ψ (u • p, u • q) (T Φ) := by
    intro u hu p q Φ hΦ
    set w := G.M'.co.e.symm (p, q) with hw
    have he : G.M'.co.e (u • w) = (u • p, u • q) := by
      rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
    have h1 : u • (mat g - 1) = 0 := hg u hu
    have h2 : u • (mat h - 1) = 0 := hh u hu
    have e1 : mat g * (u • w) = u • w := by
      have : mat g * (u • w) - u • w = (u • (mat g - 1)) * w := by
        rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
      rw [h1, Matrix.zero_mul, sub_eq_zero] at this
      exact this
    have e2 : (u • w) * (mat h)ᵀ = u • w := by
      have : (u • w) * (mat h)ᵀ - u • w = w * (u • (mat h - 1))ᵀ := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
          Matrix.mul_sub, Matrix.mul_one, smul_sub]
      rw [h2, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at this
      exact this
    have hact : actAB (cA σ) (g, h) (u • w) = u • w := by
      simp only [actAB]
      simp only [mat] at e1 e2
      rw [e1, e2]
    have h3 := hW.impl (g, h) (u • w) Φ hΦ
    simp only [Darboux.rho, he, hact] at h3
    exact h3
  have hstd' : ∀ᶠ w in Filter.cofinite,
      φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    filter_upwards [hstd, hT.geo.hM'.std] with w h1 h2
    rw [h1, h2]
  have hΦ : pure f φ ∈ schA F _ := GlobalTheory.TensUniq.pure_mem_schA f φ hφ hstd'
  set P : (Fin a' × Fin (a + a') → AF F) → ℂ := fun x => ∏ᶠ v, φ v fun i => evFin F v (x i) with hPdef
  have hPf : ∀ x x' : Fin a' × Fin (a + a') → AF F, (∀ i, (x i).2 = (x' i).2) → P x = P x' := by
    intro x x' hx
    simp only [hPdef]
    congr 1
    funext v
    congr 1
    funext i
    show evalV F v (x i).2 = evalV F v (x' i).2
    rw [hx i]
  have hpure : ∀ (f₀ : SInf F (Fin a' × Fin (a + a'))) x, pure f₀ φ x = f₀ (fun i => evI F (x i)) * P x :=
    fun _ _ => rfl
  by_cases h0 : ∀ x, P x = 0
  · refine ⟨f, ?_⟩
    have e : pure f φ = 0 := funext fun x => by rw [hpure, h0 x, mul_zero]; rfl
    rw [e, map_zero]
  push_neg at h0
  obtain ⟨y0, hy0⟩ := h0
  obtain ⟨f', hf'⟩ := slice (fun i => (y0 i).2) (T (pure f φ)) (hkeep _ hΦ)
  refine ⟨(P y0)⁻¹ • f', ?_⟩
  funext y
  set d : Fin a' × Fin (a + a') → AF F := fun i => mk 0 ((y0 i).2 - (y i).2) with hd
  set u : AF F := mk 0 1 with hu
  have hu0 : evI F u = 0 := evI_fin 1
  have hud : u • d = d := by
    funext i
    exact Prod.ext (show (0 : Ainf F) * 0 = 0 from mul_zero _) (show (1 : Af F) * _ = _ from one_mul _)
  have hsh : ∀ Φ' : (Fin a' × Fin (a + a') → AF F) → ℂ, schr B.ψ (d, 0) Φ' = fun x => Φ' (x + d) :=
    fun Φ' => funext fun x => by simp [schr]
  have htr : ∀ Ψ ∈ schA F (Fin a' × Fin (a + a')), T (fun x => Ψ (x + d)) = fun x => T Ψ (x + d) := by
    intro Ψ hΨ
    have := hcomm u hu0 d 0 Ψ hΨ
    rw [hud, smul_zero, hsh, hsh] at this
    exact this
  set c : ℂ := P y / P y0 with hc
  set Θ : (Fin a' × Fin (a + a') → AF F) → ℂ := c • fun x => pure f φ (x + d) with hΘdef
  have hΘ : Θ ∈ schA F _ := by
    refine Submodule.smul_mem _ c ?_
    have := GlobalTheory.HeisSchA.schr_mem_schA B.ψ hT.base.std (d, 0) _ hΦ
    rwa [hsh] at this
  have hvan : ∀ z, At (evI F) z → (pure f φ - Θ) (y + z) = 0 := by
    intro z hz
    have hz2 : ∀ i, (z i).2 = 0 := fun i => snd_of_at (fun u' hu' => congrFun (hz u' hu') i)
    have hevI : (fun i => evI F ((y + z + d) i)) = fun i => evI F ((y + z) i) := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (((y + z) i).1 + (0 : Ainf F)) =
        InfiniteAdeleRing.ringEquiv_mixedSpace F ((y + z) i).1
      rw [add_zero]
    have hP1 : P (y + z) = P y := hPf _ _ fun i => by
      show (y i).2 + (z i).2 = (y i).2
      rw [hz2 i, add_zero]
    have hP2 : P (y + z + d) = P y0 := hPf _ _ fun i => by
      show (y i).2 + (z i).2 + ((y0 i).2 - (y i).2) = (y0 i).2
      rw [hz2 i, add_zero]
      abel
    rw [Pi.sub_apply, hΘdef, Pi.smul_apply, smul_eq_mul, hpure, hpure, hevI, hP1, hP2, hc]
    field_simp
    ring
  have h1 := fibre B.ψ T hT.base.std hkeep hcomm _ (sub_mem hΦ hΘ) y hvan
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h1
  have h2 : T Θ y = c * T (pure f φ) (y + d) := by
    rw [hΘdef, map_smul, htr _ hΦ]
    rfl
  have hyd : y + d = fun i => mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (evI F (y i))) ((y0 i).2) := by
    funext i
    refine Prod.ext ?_ ?_
    · show (y i).1 + 0 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)
      rw [add_zero, RingEquiv.symm_apply_apply]
    · show (y i).2 + ((y0 i).2 - (y i).2) = (y0 i).2
      abel
  rw [hpure, h1, h2, hyd, hf', SchwartzMap.smul_apply, smul_eq_mul, hc]
  field_simp

end GlobalTheory.ArchPure
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseThetaKernelSeriesUnique
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.BaseKernelUniq

variable {D : D7}

theorem res_unique {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : IsRes χ P c) (h' : IsRes χ P c') : c = c' := by
  refine MonoidHom.ext fun u => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  haveI : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h0
    have h1 : a = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    apply u.ne_zero
    rw [← ha, h1, map_zero]
  rw [h a (Units.mk0 _ ha0) u rfl ha.symm, h' a (Units.mk0 _ ha0) u rfl ha.symm]

theorem idemSum_unique (V : HSp D) {e e' : AE D} {P : Finset (Pl D.host.E)} (h : IsIdemSum e P)
    (h' : IsIdemSum e' P) : e = e' := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := h'
  exact Finset.sum_congr rfl fun PP hP => (GlobalTheory.HeckeParts.idem_unique V (hes PP hP) (hes' PP hP)).symm

theorem omegaQ_congr {a b : ℕ} {Q : Finset (Pl D.host.E)} {ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    (hξ : ∀ PP ∈ Q, ξ PP = ξ' PP) (r : ℕ) (k : ℤ) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaQ Q r ξ k y = omegaQ Q r ξ' k y := by
  unfold omegaQ
  split_ifs with hy
  · exact Finset.prod_congr rfl fun PP _ => by rw [hξ PP.1 PP.2]
  · rfl

theorem thPVec_unique {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Set (Fin S.rank → D.host.E)} {ΛT : Set (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)} {βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)} {Pg Q : Finset (Pl D.host.E)}
    {ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {f₀ f f' : WO S T → ℂ}
    (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) (h' : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ' f₀ f')
    (hξ : ∀ PP ∈ Q, ξ PP = ξ' PP) : f = f' := by
  obtain ⟨-, e, he, hT⟩ := h
  obtain ⟨-, e', he', hT'⟩ := h'
  obtain rfl := idemSum_unique S he he'
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hT
  rw [hall Tm hTm, hT'.2 Tm hTm]
  congr 1
  funext x
  rw [omegaQ_congr hξ]

theorem baseKernelUnique : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → BaseKernelUnique R i v (ownAt D v) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F _ i v _ _ ω φ ω' φ' hk hk'
  obtain ⟨χ, ξR, hχ, hres, hω, hv⟩ := hk
  obtain ⟨χ', ξR', hχ', hres', hω', hv'⟩ := hk'
  obtain rfl : χ = χ' := (GlobalTheory.ChrEqUnique.chrEq_unique D).2.1 χ χ' _ hχ hχ'
  obtain rfl : φ = φ' := thPVec_unique hv hv' fun PP hP => res_unique (hres PP hP) (hres' PP hP)
  have hθφ := GlobalTheory.VecTheta.isThetaFunO_thPVec hv
  have hinf : IsInfFam R.θ := hv.1.2.inf
  funext h w u g
  exact congrFun (GlobalTheory.WeilUniq.weilDatum_unique D R.ψ hω.std _ _ _ _ ω ω' hω hω' (h, g) _
    (GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hinf _ _ _ _ hθφ _)) 0

end GlobalTheory.BaseKernelUniq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantFunctionHasTrivialRepSatakeParametersStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantFunction_has_trivialRep_satakeParameters : ∀ {D : D7} (A : HSp D) (LA : Lat A) (Sf : Finset (FinPl D)), IsSelfDualC A LA → (∀ v ∉ Sf, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) → GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) (fun _ : GA D A => (1 : ℂ)) (GlobalTheory.BottomRallis.trivPar A.rank) := by
  first | exact @GlobalTheory.BottomRallis.TrivParFun.isParamFun_one_trivPar | exact GlobalTheory.BottomRallis.TrivParFun.isParamFun_one_trivPar | (intros; apply GlobalTheory.BottomRallis.TrivParFun.isParamFun_one_trivPar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitiveStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_intertwiner_transitive : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → ∃ Φ ∈ schA F (Fin n × Fin d), e Φ ≠ 0 := by
  first | exact @GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero | exact GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero | (intros; apply GlobalTheory.EvNonzero.exists_mem_schA_ev_ne_zero <;> assumption)
end

