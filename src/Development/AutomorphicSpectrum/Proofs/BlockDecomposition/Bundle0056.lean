module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0032
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0044
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0030
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0034
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinScalingLaw
section
noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisScale

variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

lemma ht_rep {Γ K P : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) (q : Cos P Γ) (g : G) :
    l (rep q * g) = l g := by
  have hq : rep q ∈ Γ := (Quotient.out q).2
  rw [hl.left _ (Subgroup.mem_top _), hl.rat _ hq (Subgroup.mem_top _), zero_add]

lemma eis_twist {Γ K P : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) (c : G → ℂ)
    (ρ : K →* (W →L[ℂ] W)) (Λ Λ' : G → ℂ) (t : ℂ) (h : ∀ x, Λ' x = Λ x + t * l x) (g : G) (w : W) :
    eis Γ K P c ρ Λ' g w = Complex.exp (t * l g) • eis Γ K P c ρ Λ g w := by
  unfold eis
  rw [← tsum_const_smul'']
  refine tsum_congr fun q => ?_
  rw [h, ht_rep hl, Complex.exp_add, smul_smul, mul_comm]

lemma conv_twist {Γ K P : Subgroup G} {l : G → ℝ} (hl : IsHt Γ K ⊤ l) {f f' : G → ℝ} (t : ℝ)
    (h : ∀ x, f' x = f x + t * l x) (hc : Conv Γ P f) : Conv Γ P f' := by
  intro g
  refine ((hc g).mul_right (Real.exp (t * l g))).congr fun q => ?_
  rw [h, ht_rep hl, Real.exp_add]

theorem wall_scale [IsTopologicalGroup G] {K Γ P P' : Subgroup G} {ρ : K →* (W →L[ℂ] W)} {c : G → ℂ}
    {η η' β l : G → ℝ} {s : ℝ} (hs : 0 < s) (hl : IsHt Γ K ⊤ l) {R : ℝ} {D : ℂ → ℂ}
    {Op : ℂ → (secSp K P c ρ →L[ℂ] secSp K P' c ρ)} {H : ℂ → G → (secSp K P c ρ →L[ℂ] W)}
    (hw : Wall Γ K P P' c η η' β ρ (secSp K P c ρ) R D Op H) :
    Wall Γ K P P' c (fun g => s * (η g + l g)) (fun g => s * (η' g - l g)) β ρ (secSp K P c ρ) (R / s)
      (fun z => D (s * z)) (fun z => Op (s * z))
      (fun z g => Complex.exp (s * z * l g) • H (s * z) g) := by
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hre : ∀ z : ℂ, ((s : ℂ) * z).re = s * z.re := fun z => by simp
  have hσ : Differentiable ℂ (fun z : ℂ => (s : ℂ) * z) := by fun_prop
  have hgtx : ∀ x : ℝ, R / s < x → R < s * x := fun x hx => by
    rwa [div_lt_iff₀' hs] at hx
  have hltx : ∀ x : ℝ, x < -(R / s) → s * x < -R := fun x hx => by
    have h1 := mul_lt_mul_of_pos_left hx hs
    have h2 : s * -(R / s) = -R := by field_simp
    linarith
  have hlec : ∀ {x : ℝ} {z : ℂ}, x ≤ z.re → s * x ≤ ((s : ℂ) * z).re := fun h => by
    rw [hre]; exact mul_le_mul_of_nonneg_left h hs.le
  have hlec' : ∀ {y : ℝ} {z : ℂ}, z.re ≤ y → ((s : ℂ) * z).re ≤ s * y := fun h => by
    rw [hre]; exact mul_le_mul_of_nonneg_left h hs.le
  have hlc : Continuous fun g => (l g : ℂ) := Complex.continuous_ofReal.comp hl.cont
  refine
    { le := hw.le
      pos := div_nonneg hw.pos hs.le
      convR := fun x hx => ?_
      convL := fun x hx => ?_
      dEnt := ⟨hw.dEnt.1.comp hσ, fun b a => ?_⟩
      dNe := ?_
      op := ⟨?_, fun b a ha => ?_⟩
      hol := fun g => ?_
      cont := ?_
      bdd := fun b a g => ?_
      eqR := fun z hz g w => ?_
      eqL := fun z hz g w => ?_ }
  · exact conv_twist hl (s * x) (fun y => by ring) (hw.convR (s * x) (hgtx x hx))
  · exact conv_twist hl (s * x) (fun y => by ring) (hw.convL (s * x) (hltx x hx))
  · obtain ⟨M, hM⟩ := hw.dEnt.2 (s * b) (s * a)
    exact ⟨M, fun z h1 h2 => hM _ (hlec h1) (hlec' h2)⟩
  · obtain ⟨z, hz⟩ := hw.dNe
    refine ⟨z / s, ?_⟩
    have : (s : ℂ) * (z / s) = z := by field_simp
    simpa [this] using hz
  · refine hw.op.1.comp hσ.differentiableOn fun z hz => ?_
    have hz' : z.re < -(R / s) := hz
    show ((s : ℂ) * z).re < -R
    rw [hre]; exact hltx _ hz'
  · obtain ⟨M, hM⟩ := hw.op.2 (s * b) (s * a) (hltx a ha)
    exact ⟨M, fun z h1 h2 => hM _ (hlec h1) (hlec' h2)⟩
  · have h1 : Differentiable ℂ fun z : ℂ => Complex.exp (s * z * l g) := by fun_prop
    exact h1.smul ((hw.hol g).comp hσ)
  · have h1 : Continuous fun y : ℂ × G => Complex.exp (s * y.1 * l y.2) :=
      ((continuous_const.mul continuous_fst).mul (hlc.comp continuous_snd)).cexp
    have h2 : Continuous fun y : ℂ × G => H (s * y.1) y.2 :=
      hw.cont.comp (f := fun y : ℂ × G => ((s : ℂ) * y.1, y.2)) (by fun_prop)
    exact h1.smul h2
  · obtain ⟨U, hU, M, hM⟩ := hw.bdd (s * b) (s * a) g
    have hV : {g' | |l g'| < |l g| + 1} ∈ 𝓝 g :=
      (isOpen_lt (continuous_abs.comp hl.cont) continuous_const).mem_nhds (by simp)
    refine ⟨U ∩ {g' | |l g'| < |l g| + 1}, inter_mem hU hV,
      Real.exp (s * max |b| |a| * (|l g| + 1)) * M, fun z h1 h2 g' hg' => ?_⟩
    have hH := hM _ (hlec h1) (hlec' h2) g' hg'.1
    have hg2 : |l g'| < |l g| + 1 := hg'.2
    have hz : |z.re| ≤ max |b| |a| := abs_le_max_abs_abs h1 h2
    have hE : ‖Complex.exp (s * z * l g')‖ ≤ Real.exp (s * max |b| |a| * (|l g| + 1)) := by
      rw [Complex.norm_exp, Complex.re_mul_ofReal, hre]
      apply Real.exp_le_exp.mpr
      calc s * z.re * l g' ≤ |s * z.re * l g'| := le_abs_self _
        _ = s * |z.re| * |l g'| := by rw [abs_mul, abs_mul, abs_of_pos hs]
        _ ≤ s * max |b| |a| * (|l g| + 1) := by gcongr
    rw [norm_smul]
    exact mul_le_mul hE hH (norm_nonneg _) (Real.exp_pos _).le
  · rw [eis_twist hl c ρ (fun x => s * z * η x) _ (s * z) (fun x => by push_cast; ring),
      ContinuousLinearMap.smul_apply, hw.eqR _ (by rw [hre]; exact hgtx _ hz) g w, smul_comm]
  · rw [eis_twist hl c ρ (fun x => β x - s * z * η' x) _ (s * z) (fun x => by push_cast; ring),
      ContinuousLinearMap.smul_apply, hw.eqL _ (by rw [hre]; exact hltx _ hz) g w]

theorem scale : PositivityTheory.RgEis.Scale := by
  intro G _ _ _ _ _ W _ _ _ K ρ _ _ Γ P P' c η η' β l s hs hl hW
  obtain ⟨R, D, Op, H, hw⟩ := hW
  exact ⟨_, _, _, _, wall_scale hs hl hw⟩

end GlobalTheory.CompanionTheory.RgEisScale
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfLeSmall
section
noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.KerPoint

theorem support_cv_adj_cv (hKB : KerBasic) (hCv : CvTest) (X : Ctx) (φ ψ : X.G → ℂ) (hφ : Tst φ) (hψ : Tst ψ)
    (N : Set X.G) (hNc : IsCompact N) (hN : tsupport ψ ⊆ N) :
    Function.support (cv X.μ (adj ψ) (cv X.μ φ ψ)) ⊆ N⁻¹ * (tsupport φ * N) := by
  have hadj : Tst (adj ψ) := (hKB X ψ hψ).2.2.2.1
  have hc := hCv X φ ψ hφ hψ
  have hcc := hCv X (adj ψ) (cv X.μ φ ψ) hadj hc.1
  refine hcc.2.1.trans ?_
  have hs1 : tsupport (adj ψ) ⊆ N⁻¹ := by
    refine closure_minimal ?_ hNc.inv.isClosed
    intro z hz
    have hz' : ψ z⁻¹ ≠ 0 := by
      intro h0
      apply hz
      simp [adj, h0]
    exact Set.mem_inv.2 (hN (subset_tsupport _ hz'))
  have hs2 : tsupport (cv X.μ φ ψ) ⊆ tsupport φ * N :=
    closure_minimal (hc.2.1.trans (Set.mul_subset_mul_left hN)) (hφ.2.isCompact.mul hNc).isClosed
  exact Set.mul_subset_mul hs1 hs2

theorem inner_map_sub_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (U : H →L[ℂ] H)
    (a b k₁ k₂ : H) (δ : ℝ) (ha : ‖a - k₁‖ ≤ δ) (hb : ‖b - k₂‖ ≤ δ) :
    ‖inner ℂ a (U b) - inner ℂ k₁ (U k₂)‖ ≤ ‖U‖ * δ * (‖k₂‖ + δ) + ‖k₁‖ * ‖U‖ * δ := by
  have e : inner ℂ a (U b) - inner ℂ k₁ (U k₂) = inner ℂ (a - k₁) (U b) + inner ℂ k₁ (U (b - k₂)) := by
    simp only [inner_sub_left, inner_sub_right, map_sub]
    ring
  have hbn : ‖b‖ ≤ ‖k₂‖ + δ := by
    have := norm_add_le (b - k₂) k₂
    rw [sub_add_cancel] at this
    linarith
  have hU : 0 ≤ ‖U‖ := norm_nonneg _
  have t1 : ‖(inner ℂ (a - k₁) (U b) : ℂ)‖ ≤ ‖U‖ * δ * (‖k₂‖ + δ) := by
    calc ‖(inner ℂ (a - k₁) (U b) : ℂ)‖ ≤ ‖a - k₁‖ * ‖U b‖ := norm_inner_le_norm _ _
      _ ≤ δ * (‖U‖ * (‖k₂‖ + δ)) := by
          have h2 : ‖U b‖ ≤ ‖U‖ * (‖k₂‖ + δ) :=
            (U.le_opNorm b).trans (mul_le_mul_of_nonneg_left hbn hU)
          exact mul_le_mul ha h2 (norm_nonneg _) ((norm_nonneg _).trans ha)
      _ = ‖U‖ * δ * (‖k₂‖ + δ) := by ring
  have t2 : ‖(inner ℂ k₁ (U (b - k₂)) : ℂ)‖ ≤ ‖k₁‖ * ‖U‖ * δ := by
    calc ‖(inner ℂ k₁ (U (b - k₂)) : ℂ)‖ ≤ ‖k₁‖ * ‖U (b - k₂)‖ := norm_inner_le_norm _ _
      _ ≤ ‖k₁‖ * (‖U‖ * δ) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          exact (U.le_opNorm _).trans (mul_le_mul_of_nonneg_left hb hU)
      _ = ‖k₁‖ * ‖U‖ * δ := by ring
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add t1 t2)

theorem eq_zero_of_le_small {D C : ℝ} (hC : 0 ≤ C) (h : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → D ≤ δ * C) : D ≤ 0 := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hC1 : 0 < C + 1 := by linarith
  have hδ : 0 < min 1 (ε / (C + 1)) := lt_min one_pos (div_pos hε hC1)
  have h1 := h _ hδ (min_le_left _ _)
  have h2 : min 1 (ε / (C + 1)) * C ≤ ε := by
    calc min 1 (ε / (C + 1)) * C ≤ ε / (C + 1) * (C + 1) :=
          mul_le_mul (min_le_right _ _) (by linarith) hC (div_pos hε hC1).le
      _ = ε := by field_simp
  linarith

theorem ptEq_of : KerBasic → CvTest → OpAdj → ColOp → BumpEx → ApproxU → KerClose → VecLim → PtEq := by
  intro hKB hCv hAdj hCol hBump hAU hKC hVL X ι _ Φ₁ Φ₂ Φ T₁ T₂ U h1 h2 h hT1 hT2 hT x y i j k₁ k₂ hk1 hk2
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have h1N : (1 : X.G) ∈ N := mem_of_mem_nhds hN1
  have hΩ : IsCompact (N⁻¹ * (tsupport (Φ i j) * N)) := hNc.inv.mul ((h i j).2.isCompact.mul hNc)
  obtain ⟨M, hM0, hM⟩ := hKC X _ x y hΩ
  have hadj1 : ∀ a b, Tst ((fun i j => adj (Φ₁ j i)) a b : X.G → ℂ) :=
    fun a b => (hKB X _ (h1 b a)).2.2.2.1
  have hTadj := hAdj X ι Φ₁ T₁ h1 hT1
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ‖ker X.Γ (Φ i j) x y - inner ℂ k₁ (U k₂)‖ ≤
      δ * (M + ‖U‖ * (‖k₂‖ + 1) + ‖k₁‖ * ‖U‖) := by
    intro δ hδ hδ1
    obtain ⟨W₁, hW₁, hL₁⟩ := hVL X ι (fun i j => adj (Φ₁ j i)) (ContinuousLinearMap.adjoint T₁) x i k₁ δ hadj1 hTadj hk1 hδ
    obtain ⟨W₂, hW₂, hL₂⟩ := hVL X ι Φ₂ T₂ y j k₂ δ h2 hT2 hk2 hδ
    obtain ⟨W₃, hW₃, hL₃⟩ := hAU X (Φ i j) δ (h i j) hδ
    obtain ⟨ψ, hψ, hsub⟩ := hBump X (N ∩ W₁ ∩ W₂ ∩ W₃)
      (Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hN1 hW₁) hW₂) hW₃)
    have sN : tsupport ψ ⊆ N := fun z hz => (hsub hz).1.1.1
    have s1 : tsupport ψ ⊆ W₁ := fun z hz => (hsub hz).1.1.2
    have s2 : tsupport ψ ⊆ W₂ := fun z hz => (hsub hz).1.2
    have s3 : tsupport ψ ⊆ W₃ := fun z hz => (hsub hz).2
    have hc := hCol X ι ψ hψ.1
    obtain ⟨v, hv⟩ := hc.1 x i
    obtain ⟨u, hu⟩ := hc.1 y j
    have e1 : inner ℂ v ((T₁ * U * T₂) u) = ker X.Γ (cv X.μ (adj ψ) (cv X.μ (Φ i j) ψ)) x y :=
      (hc.2 Φ (T₁ * U * T₂) h hT y j u hu).2 x i v hv
    have e2 : inner ℂ v ((T₁ * U * T₂) u) = inner ℂ (ContinuousLinearMap.adjoint T₁ v) (U (T₂ u)) := by
      rw [ContinuousLinearMap.adjoint_inner_left]
      rfl
    have b1 := hL₁ ψ hψ s1 v hv
    have b2 := hL₂ ψ hψ s2 u hu
    have b3 := inner_map_sub_le U _ _ k₁ k₂ δ b1 b2
    have b4 := hM (cv X.μ (adj ψ) (cv X.μ (Φ i j) ψ)) (Φ i j) δ
      (support_cv_adj_cv hKB hCv X _ ψ (h i j) hψ.1 N hNc sN)
      (by
        intro z hz
        refine ⟨1⁻¹, Set.inv_mem_inv.2 h1N, z * 1, ⟨z, subset_tsupport _ hz, 1, h1N, rfl⟩, by simp⟩)
      (fun z => (hL₃ ψ hψ s3 z).2)
    have hsplit : ker X.Γ (Φ i j) x y - inner ℂ k₁ (U k₂) =
        (inner ℂ (ContinuousLinearMap.adjoint T₁ v) (U (T₂ u)) - inner ℂ k₁ (U k₂)) -
          (ker X.Γ (cv X.μ (adj ψ) (cv X.μ (Φ i j) ψ)) x y - ker X.Γ (Φ i j) x y) := by
      rw [← e2, e1]
      ring
    have hU : 0 ≤ ‖U‖ := norm_nonneg _
    have hk : 0 ≤ ‖k₂‖ := norm_nonneg _
    have hle : ‖U‖ * δ * (‖k₂‖ + δ) ≤ ‖U‖ * δ * (‖k₂‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hU hδ.le)
    rw [hsplit]
    refine (norm_sub_le _ _).trans ?_
    nlinarith [b3, b4, hle]
  have hC : 0 ≤ M + ‖U‖ * (‖k₂‖ + 1) + ‖k₁‖ * ‖U‖ := by positivity
  have := eq_zero_of_le_small hC key
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)

end GlobalTheory.CompanionTheory.KerPoint

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBaseChangeEquiv
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.ExteriorBase

theorem exists_baseChange_equiv (A R M : Type) [CommRing A] [CommRing R] [Algebra A R]
    [AddCommGroup M] [Module A M] (a : ℕ) :
    ∃ e : R ⊗[A] (⋀[A]^a M) ≃ₗ[R] ⋀[R]^a (R ⊗[A] M), ∀ (r : R) (m : Fin a → M),
      e (r ⊗ₜ exteriorPower.ιMulti A a m) =
        r • exteriorPower.ιMulti R a (fun k => (1 : R) ⊗ₜ[A] m k) := by
  have h := GlobalTheory.TopForm.isBaseChange_exteriorPower (TensorProduct.isBaseChange A M R) a
  refine ⟨h.equiv, fun r m => ?_⟩
  rw [h.equiv_tmul, GlobalTheory.exteriorPowerMapOver_ιMulti]
  rfl

end GlobalTheory.CompanionTheory.ExteriorBase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCommonOrderedForm
section
open Zc.Comb

universe u

namespace GlobalTheory.CompanionTheory.SegOrder

variable {T : Type u}

theorem interleave_left_nil (b : List T) : Interleave b [] b := by
  induction b with
  | nil => exact Interleave.nil
  | cons a b ih => exact Interleave.left ih

theorem interleave_right_nil (b : List T) : Interleave [] b b := by
  induction b with
  | nil => exact Interleave.nil
  | cons a b ih => exact Interleave.right ih

theorem Interleave.append_left {u v w : List T} (h : Interleave u v w) (b : List T) :
    Interleave (u ++ b) v (w ++ b) := by
  induction h with
  | nil => exact interleave_left_nil b
  | left _ ih => exact Interleave.left ih
  | right _ ih => exact Interleave.right ih

theorem Interleave.append_right {u v w : List T} (h : Interleave u v w) (b : List T) :
    Interleave u (v ++ b) (w ++ b) := by
  induction h with
  | nil => exact interleave_right_nil b
  | left _ ih => exact Interleave.left ih
  | right _ ih => exact Interleave.right ih

theorem wt_cons (s : T → T) (a : ASeg T) (L : List (ASeg T)) :
    wt s (a :: L) = wt s L ++ ASeg.dec s a := by
  simp [wt]

theorem exists_sublists_interleave (s : T → T) (L : List (ASeg T)) :
    ∀ m n : Multiset (ASeg T), (L : Multiset (ASeg T)) = m + n →
      ∃ L₁ L₂ : List (ASeg T), L₁.Sublist L ∧ L₂.Sublist L ∧
        (L₁ : Multiset (ASeg T)) = m ∧ (L₂ : Multiset (ASeg T)) = n ∧
        Interleave (wt s L₁) (wt s L₂) (wt s L) := by
  classical
  induction L with
  | nil =>
    intro m n h
    have h0 : m = 0 ∧ n = 0 := add_eq_zero.1 (by simpa using h.symm)
    refine ⟨[], [], List.Sublist.refl _, List.Sublist.refl _, ?_, ?_, Zc.Comb.Interleave.nil⟩
    · simp [h0.1]
    · simp [h0.2]
  | cons a L ih =>
    intro m n h
    have ha : a ∈ m + n := by
      rw [← h]
      simp
    rcases Multiset.mem_add.1 ha with ha | ha
    · have hL : (L : Multiset (Zc.Comb.ASeg T)) = m.erase a + n := by
        apply (Multiset.cons_inj_right a).1
        rw [Multiset.cons_coe, h, ← Multiset.cons_add, Multiset.cons_erase ha]
      obtain ⟨L₁, L₂, h₁, h₂, e₁, e₂, hI⟩ := ih (m.erase a) n hL
      refine ⟨a :: L₁, L₂, List.Sublist.cons₂ a h₁, List.Sublist.cons a h₂, ?_, e₂, ?_⟩
      · rw [← Multiset.cons_coe, e₁, Multiset.cons_erase ha]
      · rw [GlobalTheory.CompanionTheory.SegOrder.wt_cons, GlobalTheory.CompanionTheory.SegOrder.wt_cons]
        exact GlobalTheory.CompanionTheory.SegOrder.Interleave.append_left hI _
    · have hL : (L : Multiset (Zc.Comb.ASeg T)) = m + n.erase a := by
        apply (Multiset.cons_inj_right a).1
        rw [Multiset.cons_coe, h, ← Multiset.add_cons, Multiset.cons_erase ha]
      obtain ⟨L₁, L₂, h₁, h₂, e₁, e₂, hI⟩ := ih m (n.erase a) hL
      refine ⟨L₁, a :: L₂, List.Sublist.cons a h₁, List.Sublist.cons₂ a h₂, e₁, ?_, ?_⟩
      · rw [← Multiset.cons_coe, e₂, Multiset.cons_erase ha]
      · rw [GlobalTheory.CompanionTheory.SegOrder.wt_cons, GlobalTheory.CompanionTheory.SegOrder.wt_cons]
        exact GlobalTheory.CompanionTheory.SegOrder.Interleave.append_right hI _

theorem exists_common_ordered_form : ∀ {T : Type u} (s : T → T), Function.Injective s →
    (∀ (t : T) (j : ℕ), 0 < j → s^[j] t ≠ t) →
    ∀ m n : Multiset (ASeg T), ∃ L₁ L₂ L : List (ASeg T),
      (L₁ : Multiset (ASeg T)) = m ∧ (L₂ : Multiset (ASeg T)) = n ∧
      (L : Multiset (ASeg T)) = m + n ∧ AOrdered s L₁ ∧ AOrdered s L₂ ∧ AOrdered s L ∧
      Interleave (wt s L₁) (wt s L₂) (wt s L) := by
  intro T s hinj hs m n
  obtain ⟨L, hL, hord⟩ := exists_ordered_form s hinj hs (m + n)
  obtain ⟨L₁, L₂, h₁, h₂, c₁, c₂, hi⟩ := exists_sublists_interleave s L m n hL
  exact ⟨L₁, L₂, L, c₁, c₂, hL, List.Pairwise.sublist h₁ hord, List.Pairwise.sublist h₂ hord,
    hord, hi⟩

end GlobalTheory.CompanionTheory.SegOrder
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsConstOfRhoEq
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.BMid

theorem exists_const_of_rho_eq : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [CommRing K] (K₁ : Type) [CommRing K₁] (K₂ : Type) [CommRing K₂] (K₃ : Type) [CommRing K₃] (f g : K) (i₁ : Polynomial K →+* K₁) (i₂ : Polynomial K →+* K₂) (i₃ : K[T;T⁻¹] →+* K₃) (ρ₁ : K₁ →+* K₃) (ρ₂ : K₂ →+* K₃), Pf p K → PQ p i₁ (Ideal.span {Polynomial.C f - Polynomial.X * Polynomial.C g}) → PQ p i₂ (Ideal.span {Polynomial.C g - Polynomial.X * Polynomial.C f}) → PQ p i₃ (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → (∀ α, ρ₁ (i₁ α) = i₃ (Polynomial.toLaurent α)) → (∀ β, ρ₂ (i₂ β) = i₃ (LaurentPolynomial.invert (Polynomial.toLaurent β))) → ∀ (b₁ : K₁) (b₂ : K₂), ρ₁ b₁ = ρ₂ b₂ → ∃ a : K, i₁ (Polynomial.C a) = b₁ ∧ i₂ (Polynomial.C a) = b₂ := by
  intro p _ K _ K₁ _ K₂ _ K₃ _ f g i₁ i₂ i₃ ρ₁ ρ₂ hK h₁ h₂ h₃ hρ₁ hρ₂ b₁ b₂ hb
  obtain ⟨k₁, α₁, hα₁⟩ := h₁.2 b₁
  obtain ⟨k₂, α₂, hα₂⟩ := h₂.2 b₂
  have e₁ : b₁ ^ p ^ (k₁ + k₂) = i₁ (α₁ ^ p ^ k₂) := by
    rw [pow_add, pow_mul, hα₁, map_pow]
  have e₂ : b₂ ^ p ^ (k₁ + k₂) = i₂ (α₂ ^ p ^ k₁) := by
    rw [add_comm, pow_add, pow_mul, hα₂, map_pow]
  generalize α₁ ^ p ^ k₂ = α at e₁
  generalize α₂ ^ p ^ k₁ = β at e₂
  generalize k₁ + k₂ = m at e₁ e₂
  have h30 : i₃ (Polynomial.toLaurent α - LaurentPolynomial.invert (Polynomial.toLaurent β)) = 0 := by
    rw [map_sub, ← hρ₁, ← hρ₂, ← e₁, ← e₂, map_pow, map_pow, hb, sub_self]
  obtain ⟨k, hk⟩ := (h₃.3 _).1 h30
  have hchar : (p : K[T;T⁻¹]) = 0 := by
    rw [← map_natCast (LaurentPolynomial.C : K →+* K[T;T⁻¹]) p, hK.1, map_zero]
  obtain ⟨Fr, hFr⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p (K[T;T⁻¹]) hchar k
  have hx : (Polynomial.toLaurent α - LaurentPolynomial.invert (Polynomial.toLaurent β)) ^ p ^ k =
      Polynomial.toLaurent (α ^ p ^ k) - LaurentPolynomial.invert (Polynomial.toLaurent (β ^ p ^ k)) := by
    rw [← hFr, map_sub, hFr, hFr, map_pow, map_pow, map_pow]
  rw [hx] at hk
  obtain ⟨c, hc₁, hc₂⟩ := GlobalTheory.CompanionTheory.LaurSplit.exists_const_of_mem_span K f g _ _ hk
  have hz₁ : i₁ (α ^ p ^ k - Polynomial.C c) = 0 := (h₁.3 _).2 ⟨0, by simpa using hc₁⟩
  have hz₂ : i₂ (β ^ p ^ k - Polynomial.C c) = 0 := (h₂.3 _).2 ⟨0, by simpa using hc₂⟩
  rw [map_sub, sub_eq_zero, map_pow, ← e₁, ← pow_mul, ← pow_add] at hz₁
  rw [map_sub, sub_eq_zero, map_pow, ← e₂, ← pow_mul, ← pow_add] at hz₂
  obtain ⟨a, ha⟩ := (GlobalTheory.CompanionTheory.PerfectRing.pf_facts p K hK).2.2.1 (m + k) c
  have inj₁ := (GlobalTheory.CompanionTheory.PerfectRing.pf_facts p K₁ h₁.1).2.2.2.1
  have inj₂ := (GlobalTheory.CompanionTheory.PerfectRing.pf_facts p K₂ h₂.1).2.2.2.1
  refine ⟨a, inj₁ (m + k) _ _ ?_, inj₂ (m + k) _ _ ?_⟩
  · rw [← map_pow, ← map_pow, ha, hz₁]
  · rw [← map_pow, ← map_pow, ha, hz₂]

end GlobalTheory.CompanionTheory.BMid
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRealizationOfCompatibleStatement
section
open CrystallineSemistableComparison.Pb.Kap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realization_of_compatible : ∀ {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K] (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j), C.Comp x → ∃ f : Module.Dual K (C.V j) →+ B, C.Rho x f := by
  first | exact @GlobalTheory.CompanionTheory.KapRho.exists_rho | exact GlobalTheory.CompanionTheory.KapRho.exists_rho | (intros; apply GlobalTheory.CompanionTheory.KapRho.exists_rho <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsScaledNontrivialCharacter
section
open ValuativeRel MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.CharConductor

theorem exists_conductor_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (a c : k),
    valuation k a < 1 → ψ c ≠ 1 → ∃ d : k, ψ d ≠ 1 ∧ (∃ r : ℕ, ∃ μ ∈ 𝒪[k], d = μ * a ^ r * c) ∧
      ∀ s ∈ 𝒪[k], ψ (s * a * d) = 1 := by
  intro k _ _ _ _ ψ hψ a c ha hc
  classical
  have hA : MulArchimedean (ValueGroupWithZero k) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  obtain ⟨γ, hγ, hball⟩ := GlobalTheory.CharDualMat.exists_ball_trivial ψ hψ
  have hc0 : valuation k c ≠ 0 := by
    intro h0
    rw [map_eq_zero] at h0
    exact hc (by rw [h0, AddChar.map_zero_eq_one])
  obtain ⟨m, hm⟩ := exists_pow_lt₀ ha (Units.mk0 (γ / valuation k c) (div_ne_zero hγ hc0))
  rw [Units.val_mk0, lt_div_iff₀ (zero_lt_iff.mpr hc0)] at hm
  have hex : ∃ r : ℕ, ∀ μ ∈ 𝒪[k], ψ (μ * a ^ r * c) = 1 := by
    refine ⟨m, fun μ hμ => hball _ ?_⟩
    have hμ1 : valuation k μ ≤ 1 := (Valuation.mem_integer_iff _ _).mp hμ
    rw [map_mul, map_mul, map_pow]
    calc valuation k μ * valuation k a ^ m * valuation k c
        ≤ 1 * valuation k a ^ m * valuation k c := by gcongr
      _ = valuation k a ^ m * valuation k c := by rw [one_mul]
      _ < γ := hm
  have hfind := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hfind
    exact hc (by simpa using hfind 1 (one_mem _))
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hmin := Nat.find_min hex (m := r) (by omega)
  push Not at hmin
  obtain ⟨μ, hμ, hne⟩ := hmin
  refine ⟨μ * a ^ r * c, hne, ⟨r, μ, hμ, rfl⟩, fun s hs => ?_⟩
  have h := hfind (s * μ) (mul_mem hs hμ)
  rw [hr] at h
  have e : s * a * (μ * a ^ r * c) = s * μ * a ^ (r + 1) * c := by ring
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.CharConductor
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicSeriesUniformTubeStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_series_uniform_tube : ∀ (ι X T : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] [TopologicalSpace T]
    (t : ι → ℂ × ℂ → T → X) (Ω : Set (ℝ × ℝ)),
    (∀ r g (p v : ℂ × ℂ), Differentiable ℂ fun τ : ℂ => t r (p + τ • v) g) →
    (∀ r, Continuous fun y : (ℂ × ℂ) × T => t r y.1 y.2) →
    (∀ x ∈ Ω, ∀ g, ∃ V ∈ 𝓝 x, ∃ U ∈ 𝓝 g, ∃ u : ι → ℝ, Summable u ∧
      ∀ l ∈ PositivityTheory.RgEis.tube V, ∀ g' ∈ U, ∀ r, ‖t r l g'‖ ≤ u r) →
    PositivityTheory.RgEis.TubeGood (fun l g => ∑' r, t r l g) Ω ∧
      ∀ l ∈ PositivityTheory.RgEis.tube Ω, ∀ g, Summable fun r => ‖t r l g‖ := by
  first | exact @GlobalTheory.CompanionTheory.RgEisCross.tubeGood_tsum | exact GlobalTheory.CompanionTheory.RgEisCross.tubeGood_tsum | (intros; apply GlobalTheory.CompanionTheory.RgEisCross.tubeGood_tsum <;> assumption)
end

