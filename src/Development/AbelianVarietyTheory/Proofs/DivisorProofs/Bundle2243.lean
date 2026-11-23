module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2172
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1736
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2104
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2142
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2147
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ActionRelativelyAmple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound

open Matrix

theorem quad_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) (x : Fin n → ℝ) :
    (t • x) ⬝ᵥ M *ᵥ (t • x) = t ^ 2 * (x ⬝ᵥ M *ᵥ x) := by
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  ring

theorem exists_nat_posDef {n : ℕ} (E A : Matrix (Fin n) (Fin n) ℝ) (hE : E.PosDef) (hA : A.IsHermitian) :
    ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ → ((κ : ℝ) • E - A).PosDef := by
  have hq : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ E *ᵥ x := fun x hx => by
    simpa using hE.dotProduct_mulVec_pos hx
  have hc : ContinuousOn (fun x : Fin n → ℝ => (x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ E *ᵥ x)) (Metric.sphere 0 1) := by
    refine ContinuousOn.div₀ (by fun_prop) (by fun_prop) fun x hx => (hq x ?_).ne'
    rintro rfl
    simp at hx
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Fin n → ℝ) 1).exists_bound_of_continuousOn hc
  refine ⟨⌈C⌉₊ + 1, fun κ hκ => PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_⟩
  · simp only [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hE.1.eq, hA.eq, star_trivial]
  · have hx0 : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hx0.ne']
    have hb := hC _ hy
    rw [quad_smul, quad_smul, mul_div_mul_left _ _ (pow_ne_zero 2 (inv_ne_zero hx0.ne'))] at hb
    have hqx := hq x hx
    have h1 : (x ⬝ᵥ A *ᵥ x) / (x ⬝ᵥ E *ᵥ x) ≤ C := le_trans (le_abs_self _) (by rwa [Real.norm_eq_abs] at hb)
    have h2 : (x ⬝ᵥ A *ᵥ x) ≤ C * (x ⬝ᵥ E *ᵥ x) := (div_le_iff₀ hqx).1 h1
    have h3 : C < (κ : ℝ) := by
      have := Nat.le_ceil C
      have : ((⌈C⌉₊ + 1 : ℕ) : ℝ) ≤ κ := by exact_mod_cast hκ
      push_cast at this
      linarith
    have h4 : C * (x ⬝ᵥ E *ᵥ x) < κ * (x ⬝ᵥ E *ᵥ x) := mul_lt_mul_of_pos_right h3 hqx
    have h5 : x ⬝ᵥ ((κ : ℝ) • E) *ᵥ x = κ * (x ⬝ᵥ E *ᵥ x) := by
      first
        | rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
        | rw [Matrix.smul_mulVec_assoc, dotProduct_smul, smul_eq_mul]
        | simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm]
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, h5]
    linarith

theorem exists_kappa (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) :
    ∃ κ : ℕ, ∀ i : Fin 2,
      ((((κ : ℤ) • W - (actMat W i).transpose * W * actMat W i) +
        ((κ : ℤ) • W - (actMat W i).transpose * W * actMat W i).transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
  have key : ∀ m : Matrix (Fin 8) (Fin 8) ℤ, ∃ κ₀ : ℕ, ∀ κ : ℕ, κ₀ ≤ κ →
      ((((κ : ℤ) • W - m.transpose * W * m) + ((κ : ℤ) • W - m.transpose * W * m).transpose).map
        (Int.cast : ℤ → ℝ)).PosDef := by
    intro m
    have hs : (m.transpose * (W + W.transpose) * m).transpose = m.transpose * (W + W.transpose) * m := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_add, add_comm,
        Matrix.mul_assoc]
    have hA : ((m.transpose * (W + W.transpose) * m).map (Int.cast : ℤ → ℝ)).IsHermitian := by
      refine Matrix.IsHermitian.ext fun i j => ?_
      simp only [Matrix.map_apply, star_trivial]
      exact congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun hs i) j)
    obtain ⟨κ₀, h⟩ := exists_nat_posDef _ _ hW.1 hA
    refine ⟨κ₀, fun κ hκ => ?_⟩
    have e : (((κ : ℤ) • W - m.transpose * W * m) + ((κ : ℤ) • W - m.transpose * W * m).transpose).map
        (Int.cast : ℤ → ℝ) = (κ : ℝ) • (W + W.transpose).map (Int.cast : ℤ → ℝ) -
          (m.transpose * (W + W.transpose) * m).map (Int.cast : ℤ → ℝ) := by
      have e' : ((κ : ℤ) • W - m.transpose * W * m) + ((κ : ℤ) • W - m.transpose * W * m).transpose =
          (κ : ℤ) • (W + W.transpose) - m.transpose * (W + W.transpose) * m := by
        simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
          Matrix.mul_add, Matrix.add_mul, smul_add, Matrix.mul_assoc]
        abel
      rw [e']
      ext a b
      simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [e]
    exact h κ hκ
  obtain ⟨κ₀, h₀⟩ := key (actMat W 0)
  obtain ⟨κ₁, h₁⟩ := key (actMat W 1)
  refine ⟨max κ₀ κ₁, fun i => ?_⟩
  fin_cases i
  · exact h₀ _ (le_max_left _ _)
  · exact h₁ _ (le_max_right _ _)

end GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound

namespace GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound

open GlobalTheory.SS GlobalTheory.CechPic


set_option maxRecDepth 20000 in
theorem exists_bound_relAmple : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∃ κ : ℕ, ∀ (gQ : ℕ) (K : Type) [Field K] [IsAlgClosed K] (P' : PolAV (Sp K))
  (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (M : RigLB B) (pr : Fin 8 → (P'.A ⟶ B)),
  E8Fibration.IsPPFib B gQ M → E8Fibration.IsProd pr → E8Fibration.IsE8WeightedBundle W pr P'.L M.L →
  ∀ act : Fin 2 → (P'.A ⟶ P'.A), (∀ i, IsMonHom (act i)) → (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) →
  ∀ i, Out.RelAmple P'.A (LB.LinComb P'.L (K := Fin 2) ![𝟙 P'.A.left, (act i).left] ![(κ : ℤ), -1]) := by
  intro W hW
  obtain ⟨κ, hκ⟩ := exists_kappa W hW
  refine ⟨κ, ?_⟩
  intro gQ K _ _ P' B _ _ M pr hPP hpr hE act _ hact i
  obtain ⟨hB, -, ⟨cub⟩, ha, -⟩ := hPP
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  let c := GlobalTheory.EighthPowerFactor.siegOne hG hB M.isLB gQ
  have hdiag : Out.RelAmple c.A c.diag :=
    GlobalTheory.EighthPowerFactor.relAmple_diag_lam hB M.isLB ⟨cub.t, cub.isGen⟩ ha
  have hamp := GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef hG gQ 1 8 K _ (Sp K) (𝟙 _) c P'.A pr
    ((κ : ℤ) • W - (actMat W i).transpose * W * actMat W i) hpr.1 hpr.2 hdiag (hκ i)
  have := P'.isAb.proper
  have hL := P'.isLB
  have hT := LB.isLB_linComb hL (K := Fin 2) ![𝟙 P'.A.left, (act i).left] ![(κ : ℤ), -1]
  refine GlobalTheory.PosDefAmple.relAmple_of_nsmul hT (LB.isLB_linComb c.isLB _ _) (N := 1) le_rfl ?_ hamp
  rw [one_smul]
  set f := act i with hf
  set m := actMat W i with hm
  have hflat := LB.isLB_linComb M.isLB (K := (Fin 8 × Fin 8) × Fin 4)
    (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2) (fun k => -(W k.1.1 k.1.2 * negε k.2))
  have hPL : cls P'.L hL = ∑ uv : Fin 8 × Fin 8,
      W uv.1 uv.2 • pull (lift (pr uv.1) (pr uv.2)).left (cls c.P c.isLB) := by
    rw [(cls_eq_iff hL hflat).2 hE, cls_linComb M.isLB, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun uv _ => ?_
    have hlam : cls c.P c.isLB = lam (cls M.L M.isLB) (fst B B) (snd B B) := cls_cube_two M.isLB _ _ c.isLB
    erw [hlam]
    erw [pull_lam, lift_fst, lift_snd]
    rw [Fin.sum_univ_four]
    simp only [lam, lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, smul_sub, smul_add, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
    module
  have hsub := (cls_eq_iff (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb c.isLB _ _)).2
    (GlobalTheory.BilinCalc.main (Sp K) c.A c.P c.isLB
      (GlobalTheory.Biadditive.biadditive_of_triv_axes hG (Sp K) c.A c.diag c.ab (pull_isLB c.isLB _) hdiag c.P c.isLB
        c.rig₁ c.rig₂)
      c.symm P'.A 8 8 pr W (m.transpose * W * m) m (by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_assoc]))
  rw [cls_linComb c.isLB, cls_linComb c.isLB] at hsub
  have hpf : pull f.left (cls P'.L hL) = ∑ uv : Fin 8 × Fin 8,
      (m.transpose * W * m) uv.1 uv.2 • pull (lift (pr uv.1) (pr uv.2)).left (cls c.P c.isLB) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hPL, map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun uv _ => ?_) hsub.symm
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift, hact i uv.1, hact i uv.2]
    rfl
  rw [cls_linComb hL, cls_linComb c.isLB, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.vecHead]
  rw [pull_id, hpf, hPL]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_smul, mul_smul, Finset.sum_sub_distrib,
    Finset.smul_sum]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  first
    | exact neg_one_smul ℤ _
    | exact neg_one_zsmul _
    | simp

end GlobalTheory.Poinc.Sep.E8Fibration.AmpleBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerPreservesSchwartzSpace
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

namespace GlobalTheory.ModelTr

theorem extEquiv {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (e : V →ₗ[ℂ] V) (h : Set.BijOn e S S) :
    ∃ T : V ≃ₗ[ℂ] V, (∀ x ∈ S, T x = e x) ∧ ∀ x, x ∈ S ↔ T x ∈ S := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl S
  let f : V →ₗ[ℂ] V := LinearMap.ofIsCompl hQ (e ∘ₗ S.subtype) Q.subtype
  have dec : ∀ x : V, ∃ s ∈ S, ∃ q ∈ Q, x = s + q := fun x => by
    have : x ∈ S ⊔ Q := by rw [hQ.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨s, hs, q, hq, rfl⟩ := Submodule.mem_sup.1 this
    exact ⟨s, hs, q, hq, rfl⟩
  have hf : ∀ s ∈ S, ∀ q ∈ Q, f (s + q) = e s + q := fun s hs q hq => by
    rw [map_add (f := _), LinearMap.ofIsCompl_apply_left hQ (⟨s, hs⟩ : S), LinearMap.ofIsCompl_apply_right hQ (⟨q, hq⟩ : Q)]
    rfl
  have hdisj : ∀ y ∈ S, y ∈ Q → y = 0 := fun y h1 h2 => by
    have := hQ.inf_eq_bot
    exact (Submodule.mem_bot ℂ).1 (this ▸ Submodule.mem_inf.2 ⟨h1, h2⟩)
  have hmem : ∀ x, x ∈ S ↔ f x ∈ S := by
    intro x
    obtain ⟨s, hs, q, hq, rfl⟩ := dec x
    rw [hf s hs q hq]
    constructor
    · intro hx
      have hq0 : q = 0 := hdisj q (by simpa using S.sub_mem hx hs) hq
      subst hq0
      simpa using h.mapsTo hs
    · intro hx
      have hq0 : q = 0 := hdisj q (by simpa using S.sub_mem hx (h.mapsTo hs)) hq
      subst hq0
      simpa using hs
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hxS : x ∈ S := (hmem x).2 (hx ▸ S.zero_mem)
    obtain ⟨s, hs, q, hq, rfl⟩ := dec x
    have hq0 : q = 0 := hdisj q (by simpa using S.sub_mem hxS hs) hq
    subst hq0
    rw [add_zero] at hx ⊢
    have h0 := hf s hs 0 Q.zero_mem
    rw [add_zero, add_zero] at h0
    rw [h0] at hx
    exact h.injOn hs S.zero_mem (by rw [hx, map_zero])
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨s', hs', q, hq, rfl⟩ := dec y
    obtain ⟨s, hs, rfl⟩ := h.surjOn hs'
    exact ⟨s + q, hf s hs q hq⟩
  refine ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun x hx => ?_, hmem⟩
  show f x = e x
  have := hf x hx 0 Q.zero_mem
  rwa [add_zero, add_zero] at this

theorem adm_congr {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}
    (h : ∀ Φ ∈ schA F κ, l Φ = l' Φ) : l ∈ (adeleClass F).adm κ ↔ l' ∈ (adeleClass F).adm κ := by
  have key : ∀ {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ}, (∀ Φ ∈ schA F κ, l Φ = l' Φ) →
      l ∈ (adeleClass F).adm κ → l' ∈ (adeleClass F).adm κ := by
    intro l l' h hl g hg
    obtain ⟨T, hT⟩ := hl g hg
    exact ⟨T, fun f => (h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).symm.trans (hT f)⟩
  exact ⟨key h, key fun Φ hΦ => (h Φ hΦ).symm⟩

theorem exists_isWeil_trans : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∃ om₁ : Rep σ X W, M₁.IsWeil B.ψ χX χW om₁ ∧ ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), e (om x Φ) = om₁ x (e Φ) := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij
  obtain ⟨T, hTe, hTs⟩ := extEquiv (schA F (Fin n × Fin d)) e hbij
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hgood : IsGoodInt (adeleClass F) B.ψ M.co M₁.co T := by
    refine ⟨hTs, fun w Φ hΦ => ?_, fun l => ?_, fun μ hμ => ?_⟩
    · have hm : M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
        _root_.GlobalTheory.SchrKeepsSchA.schr_mem_schA F B.ψ hpair.base.std _ (M.co.e w) Φ hΦ
      have := hev.Heisenberg₂ w Φ hΦ
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at this
      rw [hTe _ hm, hTe _ hΦ, this]
    · refine (_root_.GlobalTheory.ModelAdm.model_admissible_iff_evaluation hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij l).trans (adm_congr ?_)
      intro Φ hΦ
      simp [hTe Φ hΦ]
    · obtain ⟨c, hc⟩ := _root_.GlobalTheory.ModelTrUnit.exists_const hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij μ hμ
      exact ⟨c, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hc Φ hΦ⟩
  refine ⟨trRep T om, isUWeilPair_trRep hgood
    (_root_.GlobalTheory.DblInt.main hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe)
    (GlobalTheory.T.model_evaluation_intertwines hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe) hpair.weil, fun x Φ hΦ => ?_⟩
  have hpres : om x Φ ∈ schA F (Fin n × Fin d) := hpair.weil.isUSplitting.pres x Φ hΦ
  rw [trRep_apply, ← hTe Φ hΦ, LinearEquiv.symm_apply_apply, hTe _ hpres]

end GlobalTheory.ModelTr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFibreIsoEqCoordinatewisePower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PoincDiag

@[reassoc]
theorem mapFst {S S' : Scheme.{0}} (t : S' ⟶ S) {X Y : Over S} (φ : X ⟶ Y) :
    ((Over.pullback t).map φ).left ≫ pullback.fst Y.hom t = pullback.fst X.hom t ≫ φ.left := by
  simp only [Over.pullback_map_left]; exact pullback.lift_fst _ _ _

theorem mapSnd {S S' : Scheme.{0}} (t : S' ⟶ S) {X Y : Over S} (φ : X ⟶ Y) :
    ((Over.pullback t).map φ).left ≫ pullback.snd Y.hom t = pullback.snd X.hom t := by
  simp only [Over.pullback_map_left]
  exact pullback.lift_snd _ _ _

theorem abBC : ∀ (R R' : Type) [CommRing R] [CommRing R'] (f : R →+* R') (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → IsAbelianScheme ((Over.pullback (spMap f)).obj B) ∧ SmoothOfRelativeDimension g ((Over.pullback (spMap f)).obj B).hom := by
  intro R R' _ _ f B _ g hB hd
  exact GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback f B _ _ g
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback B (spMap f)) hB hd

theorem torsPull : ∀ (S S' : Scheme.{0}) (t : S' ⟶ S) (X : Over S) [GrpObj X] (z : 𝟙_ (Over S') ⟶ (Over.pullback t).obj X) (y : Over.mk t ⟶ X) (n : ℕ), y.left = z.left ≫ pullback.fst X.hom t → z ^ n = 1 → y ^ n = 1 := by
  intro S S' t X _ z y n hy hz
  have hgp := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback X t
  let k : Over.mk ((𝟙_ (Over S')).hom ≫ t) ⟶ Over.mk t := Over.homMk (𝟙 _) (by simp)
  have hw : ((1 : 𝟙_ (Over S') ⟶ (Over.pullback t).obj X).left ≫ pullback.fst X.hom t) ≫ X.hom = (Over.mk t).hom := by
    have e := Over.w (1 : 𝟙_ (Over S') ⟶ (Over.pullback t).obj X)
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    simp only [Over.pullback_obj_hom] at e
    rw [e]
    simp
  let u : Over.mk t ⟶ X := Over.homMk ((1 : 𝟙_ (Over S') ⟶ (Over.pullback t).obj X).left ≫ pullback.fst X.hom t) hw
  have hu : u = 1 := by
    have h := hgp.2 (𝟙_ (Over S')) 1 1 (k ≫ u) (k ≫ u) (by simp [k, u]) (by simp [k, u])
    rw [← MonObj.comp_mul, _root_.mul_one] at h
    have e : u * u = u := Over.OverMorphism.ext (by simpa [k, u] using h)
    exact mul_eq_left.1 e
  have hp : ∀ m : ℕ, (y ^ m).left = (z ^ m).left ≫ pullback.fst X.hom t := by
    intro m
    induction m with
    | zero =>
      simp only [pow_zero]
      rw [← hu]
      rfl
    | succ m ih =>
      have h := hgp.2 (𝟙_ (Over S')) (z ^ m) z (k ≫ y ^ m) (k ≫ y) (by simp [k, ih]) (by simp [k, hy])
      rw [← MonObj.comp_mul, ← pow_succ, ← pow_succ] at h
      simpa [k] using h
  apply Over.OverMorphism.ext
  rw [hp n, hz, ← hu]
  rfl

theorem fibreIso_eq_pow : ∀ (l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∀ j, 1 ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsUnit (l : V₁) → ∀ (Q : Data V) (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁), ∀ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4) (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))), (∀ a, IsMonHom (pr a)) → (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) → w.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (σ : K ≃+* K), ∀ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f → LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) → (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) → ∃ f₁ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left, IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f₁ ∧ ∀ (a : Fin 8) (T : Scheme.{0}) (x : T ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left) (y : T ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), y ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.fst D.P.A.hom (spMap ev) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) → y ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = x ≫ pullback.snd D.P.A.hom (spMap ev) → x ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = y ≫ f₁ ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) := by
  intro l hl hodd W hW j hj V V₁ _ _ _ _ _ hlu Q ρ hρ D pr w hpr huniv hw K _ _ ev σ f hf hL htor
  haveI := D.P.isAb.comm
  have hfw : f ≫ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).hom = ((Over.pullback (spMap ev)).obj D.P.A).hom := by
    simpa using hf.1.w
  let F : (Over.pullback (spMap ev)).obj D.P.A ⟶ (Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A := Over.homMk f hfw
  haveI : IsIso f := hf.1.isIso_fst_of_isIso
  haveI hFi : IsIso F := by
    have : IsIso ((Over.forget _).map F) := by change IsIso f; infer_instance
    exact isIso_of_reflects_iso F (Over.forget _)
  haveI hFm : IsMonHom F := GlobalTheory.AmpleRigid.isMonHom_of_mul_comp F
    (fun T x y => GlobalTheory.AmpleRigid.mul_comp_of_grpPullback_id F hf x y)
  obtain ⟨hm₀, hu₀⟩ := _root_.GlobalTheory.baseChange_eighthPower_product_monHom _ _ (spMap ev) D.P.A _ pr hpr huniv
  obtain ⟨hm₁, hu₁⟩ := _root_.GlobalTheory.baseChange_eighthPower_product_monHom _ _ (spMap (σ.toRingHom.comp ev)) D.P.A _ pr hpr huniv
  have hBab := abBC V V₁ ρ Q.B Q.g Q.isAb Q.smoothDim
  have hB₀ := (abBC V₁ K ev _ Q.g hBab.1 hBab.2).1
  have hB₁ := (abBC V₁ K (σ.toRingHom.comp ev) _ Q.g hBab.1 hBab.2).1
  have hlK : (l : K) ≠ 0 := by
    have := hlu.map ev
    rw [map_natCast] at this
    exact this.ne_zero

  have key : ∀ (z : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback (spMap ev)).obj D.P.A), (∃ k : ℕ, z ^ (l ^ k) = 1) → ∀ a,
      (z ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a)).left ≫
          pullback.fst ((Over.pullback (spMap ρ)).obj Q.B).hom (spMap (σ.toRingHom.comp ev)) =
        spMap σ.toRingHom ≫ (z ≫ (Over.pullback (spMap ev)).map (pr a)).left ≫
          pullback.fst ((Over.pullback (spMap ρ)).obj Q.B).hom (spMap ev) := by
    rintro z ⟨k, hk⟩ a
    have hzw : z.left ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ := by simpa using Over.w z
    have hyw : (z.left ≫ pullback.fst D.P.A.hom (spMap ev)) ≫ D.P.A.hom = (Over.mk (spMap ev)).hom := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hzw, Category.id_comp]; rfl
    let y : Over.mk (spMap ev) ⟶ D.P.A := Over.homMk (z.left ≫ pullback.fst D.P.A.hom (spMap ev)) hyw
    have hy : y ^ (l ^ k) = 1 := torsPull _ _ (spMap ev) D.P.A z y (l ^ k) rfl hk
    have h := htor y ⟨k, hy⟩ z.left rfl hzw
    simp only [Over.comp_left, Category.assoc]
    rw [mapFst, mapFst]
    change z.left ≫ f ≫ _ = _
    rw [reassoc_of% h]
    rfl
  have htors : ∀ (z z' : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback (spMap ev)).obj D.P.A), (∃ k : ℕ, z ^ (l ^ k) = 1) →
      (∃ k : ℕ, z' ^ (l ^ k) = 1) → ∀ a a', z ≫ (Over.pullback (spMap ev)).map (pr a) = z' ≫ (Over.pullback (spMap ev)).map (pr a') →
      z ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a) = z' ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a') := by
    intro z z' hz hz' a a' he
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [key z hz a, key z' hz' a', he]
    · exact (Over.w (z ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a))).trans
        (Over.w (z' ≫ F ≫ (Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a'))).symm
  obtain ⟨f₁', hm, hiso, hco⟩ := _root_.GlobalTheory.PowerDiagonal.exists_diagonal K _ _ _ _ (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB₀)
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hB₁) l hl hlK _ _ hm₀ hm₁ hu₀ hu₁ F hFm hFi htors
  obtain ⟨f₁, hf₁, hcoord⟩ := _root_.GlobalTheory.FibreTransport.transport V V₁ K Q.B ρ ev σ f₁' hm hiso
  refine ⟨f₁, hf₁, fun a T x y h1 h2 => ?_⟩
  have hc : f ≫ ((Over.pullback (spMap (σ.toRingHom.comp ev))).map (pr a)).left =
      ((Over.pullback (spMap ev)).map (pr a)).left ≫ f₁'.left := congrArg (·.left) (hco a)
  have := hcoord T (x ≫ ((Over.pullback (spMap ev)).map (pr a)).left) y
    (by rw [h1, Category.assoc, mapFst_assoc]) (by rw [h2, Category.assoc, mapSnd])
  rw [← this, Category.assoc, ← reassoc_of% hc, mapFst_assoc]

end GlobalTheory.PoincDiag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsBaseChangeIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem isProd_pullback_iso : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) {A B : Over S} [GrpObj A] [GrpObj B] (pr : Fin 8 → (A ⟶ B)), E8Fibration.IsProd pr → ∀ (P : Over S') [GrpObj P] (i : (Over.pullback f).obj A ≅ P), IsMonHom i.hom → E8Fibration.IsProd (fun a => i.inv ≫ (Over.pullback f).map (pr a)) := by
  intro S S' f A B _ _ pr hpr P _ i hi
  obtain ⟨hmon, huniv⟩ := hpr
  refine ⟨fun a => ?_, fun T y => ?_⟩
  · haveI := hmon a
    infer_instance
  · let adj := Over.mapPullbackAdj f
    obtain ⟨x', hx', hu⟩ := huniv ((Over.map f).obj T) (fun a => (adj.homEquiv T B).symm (y a))
    refine ⟨adj.homEquiv T A x' ≫ i.hom, fun a => ?_, fun x hx => ?_⟩
    · simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Adjunction.homEquiv_naturality_right, hx' a, Equiv.apply_symm_apply]
    · have h1 : (adj.homEquiv T A).symm (x ≫ i.inv) = x' := by
        apply hu
        intro a
        rw [← Adjunction.homEquiv_naturality_right_symm, Category.assoc, hx a]
      rw [← h1, Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end GlobalTheory.Poinc.Sep.E8Fibration

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenCoverAlgebraPointLiesInCoverStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_cover_algebraPoint_liesInCover :
    ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens),
      ⨆ i, W i = ⊤ → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D),
        ∃ (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ ∧ ∀ a,
          Sm (X := X) W (D := Localization.Away (s a))
            (spOver (IsScalarTower.toAlgHom R D (Localization.Away (s a))) ≫ x) :=
  GlobalTheory.PtExt.exists_away_cover_sm
end

