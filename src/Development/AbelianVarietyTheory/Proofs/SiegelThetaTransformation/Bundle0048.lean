module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0002
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFinPartMat
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.LocClauseOfUnifPlaces
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionPreservesThetaAndInnerProduct
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaTestFunctionNoCoinvariantsIsotropic
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdmissibleDoubledHermitianThetaFamily
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicCuspFormAutomorphicBoundedSquareIntegrable
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct Topology

namespace GlobalTheory.AdelicCusp

theorem adel_muPin_automorphic {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    {V : HSp D} {X : Comp → Data E r} {dict : GA D V → Σ k, Frame (X k).Ψ r} {Kf : Subgroup (GA D V)}
    {th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hr : V.rank = r}
    (hd : DictIsUnif V dict Kf th hr) (hloc : GlobalTheory.DictLocTest.LocClause V dict) {mu : GA D V → ℂ}
    (hmu : MuUnit V dict mu) (hmc : Continuous mu) {c : Comp → ℂ} (hc : CUnit c) (s : ℂ)
    (la : ∀ k, Wt (X k).Ψ r) (P : FDSec X) (hPc : ∀ k, ContinuousOn (P k) (X k).dom)
    (hΓ : ∀ k, ∀ γ ∈ (X k).Γ, ∀ x ∈ (X k).dom, P k (lact γ x) = P k x) (hfin : supE X la P ≠ ⊤)
    (φ : GA D V → ℂ) (hφ : ∀ g, φ g = s * (c (dict g).1 * mu g * P (dict g).1 (dict g).2)) :
    (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ (∀ k ∈ Kf, ∀ g, φ (g * k) = mu k * φ g) ∧ Continuous φ ∧
      (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) ∧ MemLp (onQ V φ) 2 (muQ1 V) := by
  obtain ⟨hQ, hK, -, hdom, -, -⟩ := hd
  obtain ⟨hmul, hnorm, hQ1, hunit⟩ := hmu

  have key : ∀ g g' : GA D V, ∀ γ' ∈ (X (dict g).1).Γ, dict g' = ⟨(dict g).1, lact γ' (dict g).2⟩ →
      c (dict g').1 * P (dict g').1 (dict g').2 = c (dict g).1 * P (dict g).1 (dict g).2 := by
    intro g g' γ' hγ' he
    rw [he]
    show c (dict g).1 * P (dict g).1 (lact γ' (dict g).2) = _
    rw [hΓ _ γ' hγ' _ (hdom g)]
  have hφ' : ∀ g, φ g = s * mu g * (c (dict g).1 * P (dict g).1 (dict g).2) := fun g => by
    rw [hφ]; ring
  have hL : ∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g := by
    intro γ hγ g
    obtain ⟨γ', hγ', he⟩ := hQ γ hγ g
    rw [hφ', hφ', key g _ γ' hγ' he, hmul, hQ1 γ hγ, one_mul]
  have hR : ∀ k ∈ Kf, ∀ g, φ (g * k) = mu k * φ g := by
    intro k hk g
    obtain ⟨γ', hγ', he⟩ := hK k hk g
    rw [hφ', hφ', key g _ γ' hγ' he, hmul]
    ring

  have hC : Continuous φ := by
    rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨N, hN, k, x, hxc, hx⟩ := hloc g₀
    have hloc' : ∀ g ∈ N, c (dict g).1 * P (dict g).1 (dict g).2 = c k * P k (x g) := by
      intro g hg
      obtain ⟨hxd, γ, hγ, he⟩ := hx g hg
      rw [he]
      show c k * P k (lact γ (x g)) = _
      rw [hΓ k γ hγ (x g) hxd]
    have hcont : ContinuousOn (fun g => s * mu g * (c k * P k (x g))) N :=
      (continuousOn_const.mul hmc.continuousOn).mul
        (continuousOn_const.mul ((hPc k).comp hxc fun g hg => (hx g hg).1))
    have heq : (fun g => s * mu g * (c k * P k (x g))) =ᶠ[𝓝 g₀] φ := by
      filter_upwards [hN] with g hg
      rw [hφ', hloc' g hg]
    exact (hcont.continuousAt hN).congr heq

  have hB : ∀ g, ‖φ g‖ ≤ ‖s‖ * (supE X la P).toReal := by
    intro g
    have hw : (X (dict g).1).pnorm (la (dict g).1) (P (dict g).1) (dict g).2 = ‖P (dict g).1 (dict g).2‖ := by
      unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
      simp [hunit g]
    have hle : ENNReal.ofReal ((X (dict g).1).pnorm (la (dict g).1) (P (dict g).1) (dict g).2) ≤ supE X la P := by
      unfold Formalism.L2.Pj.supE
      exact le_iSup_of_le ⟨(dict g).1, ⟨(dict g).2, hdom g⟩⟩ le_rfl
    have hP : ‖P (dict g).1 (dict g).2‖ ≤ (supE X la P).toReal := by
      rw [← hw]
      exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hle
    rw [hφ, norm_mul, norm_mul, norm_mul, hc (dict g).1, hnorm g, one_mul, one_mul]
    exact mul_le_mul_of_nonneg_left hP (norm_nonneg s)
  refine ⟨hL, hR, hC, ⟨_, hB⟩, ?_⟩

  have hinv : ∀ g, onQ V φ (autMk V g) = φ g := by
    intro g
    show φ (Quotient.out (autMk V g)) = φ g
    have h1 := Quotient.exact (Quotient.out_eq (autMk V g))
    have h2 : g * (Quotient.out (autMk V g))⁻¹ ∈ GQ V := QuotientGroup.rightRel_apply.mp h1
    have h3 := hL _ h2 (Quotient.out (autMk V g))
    rw [inv_mul_cancel_right] at h3
    exact h3.symm
  have hmeas : Measurable (onQ V φ) := by
    have : BorelSpace (GA D V) := ⟨rfl⟩
    rw [measurable_from_quotient]
    have : onQ V φ ∘ Quotient.mk'' = φ := funext hinv
    rw [this]
    exact hC.measurable
  refine MemLp.of_bound hmeas.aestronglyMeasurable (‖s‖ * (supE X la P).toReal)
    (Filter.Eventually.of_forall fun q => ?_)
  show ‖φ (Quotient.out q)‖ ≤ _
  exact hB _


set_option maxHeartbeats 1000000 in
theorem phiJ_automorphic : ∀ (D : D7) (T : CoreJ D) (h : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hD : Dom a n), ∀ f ∈ T.cuspA j a n, (∀ γ ∈ GQ (T.V j σ), ∀ g, T.phiJ j σ a f (γ * g) = T.phiJ j σ a f g) ∧ (∀ k ∈ T.Kf j σ, ∀ g, T.phiJ j σ a f (g * k) = T.mu j σ k * T.phiJ j σ a f g) ∧ Continuous (T.phiJ j σ a f) ∧ (∃ C : ℝ, ∀ g, ‖T.phiJ j σ a f g‖ ≤ C) ∧ MemLp (onQ (T.V j σ) (T.phiJ j σ a f)) 2 (muQ1 (T.V j σ)) := by
  intro D T h j hj σ hσ a n hD f hf
  obtain ⟨th, hr, hth, hd⟩ := h.dictU j hj σ hσ
  have hU := h.unf j hj σ hσ
  have hLK := h.levelK j hj σ hσ
  have hK : T.Kf j σ ≤ GfC (T.V j σ) := fun k hk => ((hLK k).mp hk).1
  have hpos : 0 < D.host.g 0 * D.host.g 1 := Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hN : ∀ g₀ : GA D (T.V j σ), {g : GA D (T.V j σ) | ∃ k ∈ T.Kf j σ, ∃ h ∈ GinfC (T.V j σ), g = g₀ * k * h} ∈ 𝓝 g₀ :=
    fun g₀ => LevelOpen.level_mem_nhds D (T.V j σ) (D.host.g 0 * D.host.g 1) (T.Kf j σ) hpos hLK g₀
  have hloc := GlobalTheory.DictLocTest.locClause_of_unif_places hd hK hN (fun k τ => ⟨τ.1, hth k τ⟩)
  have hmem : rdU (T.U j σ) f ∈ holSub (T.U j σ).X (laU (T.U j σ) a n) := by
    have h1 := (Submodule.mem_inf.mp hf).2
    rw [Submodule.mem_iInf] at h1
    have h2 := h1 σ
    rw [Submodule.mem_iInf] at h2
    exact h2 hσ

  have hΓ : ∀ P ∈ holSub (T.U j σ).X (laU (T.U j σ) a n), ∀ k, ∀ γ ∈ ((T.U j σ).X k).Γ,
      ∀ x ∈ ((T.U j σ).X k).dom, P k (lact γ x) = P k x := by
    intro P hP
    unfold Formalism.L2.Pj.holSub at hP
    induction hP using Submodule.span_induction with
    | mem Q hQ =>
      intro k γ hγ x hx
      have hQ' : IsHolCusp (T.U j σ).X (laU (T.U j σ) a n) Q := hQ
      unfold Formalism.L2.Pj.IsHolCusp at hQ'
      obtain ⟨⟨⟨-, -, hsec⟩, -⟩, -⟩ := hQ' k
      rw [hsec γ hγ x hx, h.chiTriv j hj σ hσ a n hD k γ hγ, one_mul]
    | zero => intro k γ hγ x hx; rfl
    | add Q R _ _ hQ hR =>
      intro k γ hγ x hx
      simp only [Pi.add_apply, hQ k γ hγ x hx, hR k γ hγ x hx]
    | smul t Q _ hQ =>
      intro k γ hγ x hx
      simp only [Pi.smul_apply, hQ k γ hγ x hx]
  refine adel_muPin_automorphic (hd := hd) (hloc := hloc) (hmu := h.muUnit j hj σ hσ)
    (hmc := h.muCont j hj σ hσ) (hc := h.cUnit j hj σ hσ) (s := (lieFac (T.Q.Dw j) (xiR D) a : ℂ))
    (la := laU (T.U j σ) a n) (P := rdU (T.U j σ) f) (hPc := fun k => rdC_continuousOn hU hD ⟨f, hf⟩ k)
    (hΓ := hΓ _ hmem) (hfin := supE_cusp_ne_top hσ hf) (φ := T.phiJ j σ a f) (hφ := ?_)
  intro g
  simp only [Formalism.L2.Pj.CoreJ.phiJ, Pi.smul_apply, smul_eq_mul, Formalism.L2.Pj.adel_muPin]

end GlobalTheory.AdelicCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsProperProjection
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StabProper

private lemma sum_mul_conj_eq_conj_dotProduct {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    ∑ a, ∑ b, x a * conj (G b a) * conj (y b) = conj (y ⬝ᵥ (G *ᵥ star x)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_conj]
  ring

theorem unitary_iff_form {n : ℕ} (G g : Matrix (Fin n) (Fin n) ℂ) :
    gᴴ * G * g = G ↔ ∀ v w : Fin n → ℂ,
      ∑ a, ∑ b, (g.map conj *ᵥ v) a * conj (G b a) * conj ((g.map conj *ᵥ w) b) =
        ∑ a, ∑ b, v a * conj (G b a) * conj (w b) := by
  have h1 : ∀ v : Fin n → ℂ, star (g.map conj *ᵥ v) = g *ᵥ star v := by
    intro v; ext i
    simp [mulVec, dotProduct]
  have key : ∀ v w : Fin n → ℂ, ∑ a, ∑ b, (g.map conj *ᵥ v) a * conj (G b a) * conj ((g.map conj *ᵥ w) b) =
      conj (w ⬝ᵥ ((gᴴ * G * g) *ᵥ star v)) := by
    intro v w
    rw [sum_mul_conj_eq_conj_dotProduct, h1]
    congr 1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w gᴴ]
    congr 1
    ext j
    simp [vecMul, mulVec, dotProduct, conjTranspose_apply, mul_comm]
  constructor
  · intro h v w
    rw [key, h, sum_mul_conj_eq_conj_dotProduct]
  · intro h
    ext i j
    have hs : ∀ k : Fin n, star (Pi.single k 1 : Fin n → ℂ) = Pi.single k 1 := by
      intro k; ext l; by_cases hl : l = k <;> simp [hl]
    have := h (Pi.single j 1) (Pi.single i 1)
    rw [key, sum_mul_conj_eq_conj_dotProduct, hs] at this
    have := (starRingEnd ℂ).injective this
    simpa [mulVec, dotProduct, Pi.single_apply] using this

variable {D : D7}

theorem compAt_eq (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} (w : Mx D m n) :
    compAt θ τ w = w.map ((θ τ).comp (infPart D)) := rfl

theorem hermC_eq {S T : HSp D} (C : Ctx S T) (σ : C.X.Ψ) (v w : Fin T.rank → ℂ) :
    hermC σ.1 C.X.Gm v w = ∑ a, ∑ b, v a * conj (gramAt D T (C.m.e.symm σ) b a) * conj (w b) := by
  unfold hermC gramAt
  have he := C.m.e_emb (C.m.e.symm σ)
  rw [Equiv.apply_symm_apply] at he
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [C.m.gT, he]
  simp [NumberField.ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.StabProper

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianThetaLevelDataFormsSystem
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW.RecSys

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem EF_swap (hs : IsSympl X bas) (u v : Fin r → E) : EF X u v = -EF X v u := by
  rw [EF_crd hs u v, EF_crd hs v u, neg_neg, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem eq_zero_of_EF (hs : IsSympl X bas) (u : Fin r → E) (h : ∀ v, EF X u v = 0) : u = 0 := by
  have hc : crd X bas u = 0 := by
    funext j
    rcases j with i | i
    · have h1 := h (vecQ X bas (Pi.single (Sum.inr i) 1))
      rw [EF_crd hs, crd_vecQ hs] at h1
      simpa [Pi.single_apply] using h1
    · have h1 := h (vecQ X bas (Pi.single (Sum.inl i) 1))
      rw [EF_crd hs, crd_vecQ hs] at h1
      simpa [Pi.single_apply] using h1
  rw [← vecQ_crd X bas u, hc]
  exact vecQ_zero X bas

theorem EFBil_nondegenerate (hs : IsSympl X bas) :
    LinearMap.BilinForm.Nondegenerate (EFBil X) := by
  refine ⟨fun u hu => eq_zero_of_EF hs u fun v => hu v, fun u hu => eq_zero_of_EF hs u fun v => ?_⟩
  have h0 : EF X v u = 0 := hu v
  rw [EF_swap hs, h0, neg_zero]

theorem selfD_int {L : Lt E r} (h : SelfD X L) : (L.restrictScalars ℤ).FG ∧
    LinearMap.BilinForm.dualSubmodule (EFBil X) (L.restrictScalars ℤ) = L.restrictScalars ℤ := by
  refine ⟨h.1.restrictScalars, ?_⟩
  ext x
  rw [LinearMap.BilinForm.mem_dualSubmodule, Submodule.restrictScalars_mem, h.2 x]
  constructor
  · intro H y hy
    obtain ⟨k, hk⟩ := Submodule.mem_one.1 (H y hy)
    exact ⟨k, hk.symm.trans (eq_intCast _ k)⟩
  · intro H y hy
    obtain ⟨k, hk⟩ := H y hy
    exact Submodule.mem_one.2 ⟨k, (eq_intCast _ k).trans hk.symm⟩

theorem tail_le (hs : IsSympl X bas) (hn : 4 * (Module.finrank ℚ E * r) + 4 ≤ n)
    (𝓛 : Set (Lt E r)) (h𝓛 : ∀ L ∈ 𝓛, SelfD X L) {L : Lt E r} (hL : L ∈ 𝓛) :
    Summable (fun L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L} =>
      (L'.1.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ (-(n : ℝ) / 2)) ∧
    ∑' L' : {L' // L' ∈ 𝓛 ∧ L' ≠ L},
      (L'.1.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ (-(n : ℝ) / 2) ≤ 0.65 := by
  classical
  have hρ : Module.finrank ℚ (Fin r → E) = Module.finrank ℚ E * r := by
    rw [Module.finrank_pi_fintype]
    simp [mul_comm]
  have hsw := EF_swap (X := X) hs
  have hB := EFBil_nondegenerate hs
  have hrefl : (EFBil X).IsRefl := fun x y hxy => by
    have h0 : EF X x y = 0 := hxy
    show EF X y x = 0
    rw [hsw, h0, neg_zero]
  have hlr : ∀ x y, EFBil X x y = EFBil X y x ∨ EFBil X x y = -EFBil X y x :=
    fun x y => Or.inr (show EF X x y = -EF X y x from hsw x y)
  obtain ⟨hLfg, hLd⟩ := selfD_int (h𝓛 L hL)
  have key := card_selfDual_le (EFBil X) hB hrefl hlr _ hLfg hLd
  let f : {L' // L' ∈ 𝓛 ∧ L' ≠ L} → ℕ := fun L' => L'.1.toAddSubgroup.relIndex L.toAddSubgroup
  let G : {L' // L' ∈ 𝓛 ∧ L' ≠ L} → Submodule ℤ (Fin r → E) := fun L' => L'.1.restrictScalars ℤ
  have hGinj : Function.Injective G := fun a b hab =>
    Subtype.ext (Submodule.restrictScalars_injective ℤ _ _ hab)
  have hGmem : ∀ i, (G i).FG ∧ LinearMap.BilinForm.dualSubmodule (EFBil X) (G i) = G i ∧
      (G i).toAddSubgroup.relIndex (L.restrictScalars ℤ).toAddSubgroup = f i := fun i =>
    ⟨(selfD_int (h𝓛 i.1 i.2.1)).1, (selfD_int (h𝓛 i.1 i.2.1)).2, rfl⟩
  have h2 : ∀ i, 2 ≤ f i := by
    intro i
    obtain ⟨hne, h1⟩ := (key 1 le_rfl).2.2 (G i) (hGmem i).1 (hGmem i).2.1
    have hfi : f i ≠ 1 := fun h1' => i.2.2 (Submodule.restrictScalars_injective ℤ _ _ (h1 h1'))
    have : f i ≠ 0 := hne
    omega
  have hc : ∀ m, {i | f i = m}.Finite ∧ {i | f i = m}.ncard ≤ m ^ (2 * Module.finrank ℚ (Fin r → E)) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have he : {i | f i = 0} = ∅ := Set.eq_empty_of_forall_notMem fun i hi => by
        have := h2 i
        simp only [Set.mem_ofPred_eq] at hi
        omega
      simp [he]
    · have hsub : ∀ i ∈ {i | f i = m}, G i ∈ {L' : Submodule ℤ (Fin r → E) | L'.FG ∧
          LinearMap.BilinForm.dualSubmodule (EFBil X) L' = L' ∧ L'.toAddSubgroup.relIndex (L.restrictScalars ℤ).toAddSubgroup = m} :=
        fun i hi => ⟨(hGmem i).1, (hGmem i).2.1, (hGmem i).2.2.trans hi⟩
      have hfin' := (key m hm).1
      refine ⟨(hfin'.preimage hGinj.injOn).subset fun i hi => hsub i hi, ?_⟩
      exact (Set.ncard_le_ncard_of_injOn G hsub hGinj.injOn hfin').trans (key m hm).2.1
  have hρn : 4 * Module.finrank ℚ (Fin r → E) + 4 ≤ n := by rw [hρ]; exact hn
  let c : {L' // L' ∈ 𝓛 ∧ L' ≠ L} → ℂ := fun i => (((f i : ℝ) ^ (-(n : ℝ) / 2) : ℝ) : ℂ)
  have hnorm : ∀ i, ‖c i‖ = (f i : ℝ) ^ (-(n : ℝ) / 2) := fun i =>
    Complex.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have res := tail_sum_lt_one f _ n hρn h2 hc c fun i => (hnorm i).le
  simp only [hnorm] at res
  exact res

theorem norm_eq_one_of_ip {φ : TF n g} (hφ : IsSB φ) (h1 : SW.ip φ φ = 1) {c : ℂ}
    (h : SW.ip (c • φ) (c • φ) = 1) : ‖c‖ = 1 := by
  have hc := (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) φ φ hφ hφ).2.2.2.1
  have hF := (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) φ _ hφ hc).2.2.1
  have hsm := (isSB_algebra_haar_linear ℚ (Fin n) (Fin g) _ _ hF hF).2.2.2.2.2.1 (c * conj c)
  have e : (fun x => (c • φ) x * conj ((c • φ) x)) = (c * conj c) • (φ * fun x => conj (φ x)) := by
    funext x
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, map_mul]
    ring
  have h1' : haar (φ * fun x => conj (φ x)) = 1 := h1
  unfold SW.ip at h
  rw [e, hsm, h1', mul_one, Complex.mul_conj] at h
  have h2 : ‖c‖ ^ 2 = 1 := by
    rw [← Complex.normSq_eq_norm_sq]
    exact_mod_cast h
  nlinarith [norm_nonneg c]

end GlobalTheory.SW.RecSys

namespace GlobalTheory.SW

open RecSys

theorem isSystem_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → ∀ (D : Level X) (hn : r ≤ n) (M : ℕ), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ μ : GL (Fin r) E → Lt E r → ℂ, (∀ γ ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (γ : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx γ (v₀ L) = (μ γ L * (D.lam k : ℂˣ)) • v₀ (mapL γ L)) → IsSystem X bas idx M D.grp D.lats (D.phi bas hn v₀) μ := by
  intro E _ _ _ r X g bas idx n hs hn2 hnE D hn M hM0 hMm v₀ hv₀ μ hμ
  obtain ⟨-, -, hgrp, hlats, hlam, -, -⟩ := _root_.GlobalTheory.SW.level_laws E r X g bas idx n hs hn2 D hn
  have T4 := GlobalTheory.T.levelTestFunction_finite_sum_equivariant E r X g bas idx n hs hn2 D hn M hM0 hMm v₀ hv₀
  have T5 := _root_.GlobalTheory.SW.PhiNorm.phi_norm_overlap E r X g bas idx n hs hn2 D hn M hM0 hMm v₀ hv₀
  have hfinQ : Finite (𝓞 E ⧸ D.𝔪) := D.𝔪.finiteQuotientOfFreeOfNeBot D.ne_bot
  have hfinM : Finite (Matrix (Fin r) (Fin r) (𝓞 E ⧸ D.𝔪)) :=
    inferInstanceAs (Finite (Fin r → Fin r → 𝓞 E ⧸ D.𝔪))
  have hcard : 0 < Nat.card D.J := Nat.card_pos
  refine
    { un := fun γ hγ => ((hgrp γ).1 hγ).1
      lat := fun L hL => ⟨hL.1.1, (hlats L hL).2.1⟩
      stab := fun γ hγ L hL => ((hlats L hL).2.2.2 γ hγ).1
      sb := fun L hL Λ hΛ => (T4 L hL Λ hΛ).1
      norm := ⟨(Nat.card D.J : ℝ), by exact_mod_cast hcard,
        fun L hL Λ hΛ => by rw [(T5 L hL Λ hΛ).1, Complex.ofReal_natCast],
        fun L L' => (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) ^ (-(n : ℝ) / 2), 0.65,
        by norm_num, fun L hL L' hL' Λ hΛ => (T5 L hL Λ hΛ).2 L' hL',
        fun L hL => RecSys.tail_le hs hnE D.lats (fun L' hL' => hL'.1) hL⟩
      mu := fun γ hγ L hL => ?_
      supp := fun γ hγ hγ' L hL L' hL' Λ hΛ =>
        _root_.GlobalTheory.SW.phi_overlap_eq_zero E r X g bas idx n hs hn2 D hn M hM0 hMm v₀ hv₀ γ hγ hγ' L hL L' hL' Λ hΛ
      cusp := fun ξ hξ hξ0 L hL Λ hΛ =>
        _root_.GlobalTheory.SW.Coinv.phi_no_coinvariants E r X g bas idx n hs hn2 D hn M hM0 hMm v₀ hv₀ ξ hξ hξ0 L hL Λ hΛ
      adm := fun L hL L' hL' => _root_.GlobalTheory.SW.DblAdm.adm_dbl_phi_of_isVac E r X g bas idx n hs hn2 D hn M hM0 hMm v₀ hv₀ L hL L' hL' }
  obtain ⟨hun, k, hkJ, hred⟩ := (hgrp γ).1 hγ
  have hmem := ((hlats L hL).2.2.2 γ hγ).1
  have hrel := hμ γ hγ L hL ⟨k, hkJ⟩ hred
  have hvac := hv₀ L hL
  have hvac' := hv₀ _ hmem
  have hip : SW.ip ((μ γ L * ((D.lam ⟨k, hkJ⟩ : ℂˣ) : ℂ)) • v₀ (mapL γ L))
      ((μ γ L * ((D.lam ⟨k, hkJ⟩ : ℂˣ) : ℂ)) • v₀ (mapL γ L)) = 1 := by
    rw [← hrel, ((wG_laws E r X g bas idx n hs hn2 γ hun (v₀ L) hvac.1).2.2.1 (v₀ L) hvac.1).1]
    exact hvac.2.1
  have htn := RecSys.norm_eq_one_of_ip hvac'.1 hvac'.2.1 hip
  have hl := hlam ⟨k, hkJ⟩
  refine ⟨?_, fun Λ hΛ => ?_⟩
  · rw [norm_mul, hl, mul_one] at htn
    exact htn
  · rw [(T4 L hL Λ hΛ).2.2.2 γ hγ ⟨k, hkJ⟩ hred _ htn hrel, mul_inv_cancel_right₀ (Units.ne_zero _)]

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.MemSSOfEqSumThP
section
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical

namespace GlobalTheory.Dict.CuspSum

theorem mem_SS_of_eq_sum_thP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ), ((∃ τ, ∃ i : Fin q0, i.val + 1 = q0 ∧ 1 ≤ k τ i) ∨ q0 = 0) → ∀ (J : Type) [Fintype J] (φ : J → TF n g) (P : J → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), (∀ j, IsSB (φ j)) → (∀ j, P j ∈ Harm.rowHighest ℂ k k') → ∀ Q : Frame X.Ψ r → ℂ, (∀ x ∈ X.dom, Q x = ∑ j, thP X hr bas idx (φ j) (P j) x) → (∀ ga ∈ X.Γ, ∀ x ∈ X.dom, Q (lact ga x) = X.χ (wtOf X hr k k' n) ga * Q x) → Q ∈ X.SS (wtOf X hr k k' n) := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn k k' hk J _ φ P hφ hP Q hQ hΓ
  choose m a b t h using fun j =>
    (GlobalTheory.SW.CharLink.harmonicTheta_eq_sum_thetaCharacteristic E r X g q0 hr bas idx n hs hn).2 (φ j) (hφ j)
  have hQ' : ∀ x ∈ X.dom, Q x = ∑ p ∈ (Finset.univ : Finset (Σ j : J, Fin (m j))), t p.1 p.2 *
      thFr X hr bas idx n (fun k i => (a p.1 p.2 k i : ℝ)) (fun k i => (b p.1 p.2 k i : ℝ)) (P p.1) x := by
    intro x hx
    rw [hQ x hx, Fintype.sum_sigma]
    exact Finset.sum_congr rfl fun j _ => h j (P j) x hx
  rcases hk with ⟨τ, hτ⟩ | h0
  · exact CuspAny.mem_SS_of_eq_sum_thFr idx hr _ _ _ _ hs hn ⟨τ, Or.inl hτ⟩ (fun p _ => hP p.1) hQ' hΓ
  · exact ThFr.mem_SS_of_eq_sum_thFr idx hr _ _ _ _ hs hn
      (Or.inr (CuspClass.not_isIso_of_definite X (by omega))) (fun p _ => hP p.1) hQ' hΓ

end GlobalTheory.Dict.CuspSum
end

