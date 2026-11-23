module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Bundle0005
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.HeckeComponentVectors.HeckeVecFst
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.F.RS

attribute [local instance] borelG borelF borelA borelH

private theorem heckeVec_fst {G₁ G₂ V : Type} [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) {x : V}
    (hx : x ∈ fixed ρ (K₁.prod K₂)) (f : G₁ → ℂ) (h : G₂ → ℂ)
    (hf : ∀ g, ∀ k ∈ K₁, f (g * k) = f g) (h0 : ∀ g, g ∉ K₂ → h g = 0) (h1 : ∀ g ∈ K₂, h g = 1) :
    heckeVec ρ (K₁.prod K₂) (fun g => f g.1 * h g.2) x =
      heckeVec (ρ.comp (MonoidHom.inl G₁ G₂)) K₁ f x := by
  unfold heckeVec
  let e : G₁ ⧸ K₁ → (G₁ × G₂) ⧸ (K₁.prod K₂) := fun c => QuotientGroup.mk (c.out, 1)
  have he : Function.Injective e := by
    intro c d hcd
    have h2 := QuotientGroup.eq.1 hcd
    have h3 : c.out⁻¹ * d.out ∈ K₁ := by simpa using (Subgroup.mem_prod.1 h2).1
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d]
    exact QuotientGroup.eq.2 h3
  have hsupp : Function.support (fun c : (G₁ × G₂) ⧸ (K₁.prod K₂) => (f c.out.1 * h c.out.2) • ρ c.out x) ⊆ Set.range e := by
    intro d hd
    have hk : d.out.2 ∈ K₂ := by
      by_contra hn
      exact hd (by simp [h0 _ hn])
    refine ⟨QuotientGroup.mk d.out.1, ?_⟩
    rw [← QuotientGroup.out_eq' d]
    refine QuotientGroup.eq.2 (Subgroup.mem_prod.2 ⟨?_, by simpa using hk⟩)
    have h3 : (QuotientGroup.mk d.out.1 : G₁ ⧸ K₁).out⁻¹ * d.out.1 ∈ K₁ :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    simpa using h3
  have key : ∑ᶠ d : (G₁ × G₂) ⧸ (K₁.prod K₂), (f d.out.1 * h d.out.2) • ρ d.out x =
      ∑ᶠ c : G₁ ⧸ K₁, (f (e c).out.1 * h (e c).out.2) • ρ (e c).out x := by
    rw [← finsum_mem_range he (f := fun d : (G₁ × G₂) ⧸ (K₁.prod K₂) => (f d.out.1 * h d.out.2) • ρ d.out x),
      finsum_mem_def, Set.indicator_eq_self.2 hsupp]
  refine key.trans (finsum_congr fun c => ?_)
  have hm : ((c.out, 1) : G₁ × G₂)⁻¹ * (e c).out ∈ K₁.prod K₂ :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' (e c)).symm
  obtain ⟨m1, m2⟩ := Subgroup.mem_prod.1 hm
  have m1' : c.out⁻¹ * (e c).out.1 ∈ K₁ := by simpa using m1
  have m2' : (e c).out.2 ∈ K₂ := by simpa using m2
  have hfd : f (e c).out.1 = f c.out := by
    have := hf c.out _ m1'
    rwa [mul_inv_cancel_left] at this
  have hρ : ρ (e c).out x = ρ (c.out, 1) x := by
    have h5 : ρ (((c.out, 1) : G₁ × G₂) * (((c.out, 1) : G₁ × G₂)⁻¹ * (e c).out)) x = ρ (c.out, 1) x := by
      rw [map_mul, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 hx _ hm]
    rwa [mul_inv_cancel_left] at h5
  rw [hfd, h1 _ m2', hρ, mul_one]
  rfl

private theorem heckeVec_snd {G₁ G₂ V : Type} [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂) {x : V}
    (hx : x ∈ fixed ρ (K₁.prod K₂)) (f : G₂ → ℂ) (h : G₁ → ℂ)
    (hf : ∀ g, ∀ k ∈ K₂, f (g * k) = f g) (h0 : ∀ g, g ∉ K₁ → h g = 0) (h1 : ∀ g ∈ K₁, h g = 1) :
    heckeVec ρ (K₁.prod K₂) (fun g => h g.1 * f g.2) x =
      heckeVec (ρ.comp (MonoidHom.inr G₁ G₂)) K₂ f x := by
  unfold heckeVec
  let e : G₂ ⧸ K₂ → (G₁ × G₂) ⧸ (K₁.prod K₂) := fun c => QuotientGroup.mk (1, c.out)
  have he : Function.Injective e := by
    intro c d hcd
    have h2 := QuotientGroup.eq.1 hcd
    have h3 : c.out⁻¹ * d.out ∈ K₂ := by simpa using (Subgroup.mem_prod.1 h2).2
    rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d]
    exact QuotientGroup.eq.2 h3
  have hsupp : Function.support (fun c : (G₁ × G₂) ⧸ (K₁.prod K₂) => (h c.out.1 * f c.out.2) • ρ c.out x) ⊆ Set.range e := by
    intro d hd
    have hk : d.out.1 ∈ K₁ := by
      by_contra hn
      exact hd (by simp [h0 _ hn])
    refine ⟨QuotientGroup.mk d.out.2, ?_⟩
    rw [← QuotientGroup.out_eq' d]
    refine QuotientGroup.eq.2 (Subgroup.mem_prod.2 ⟨by simpa using hk, ?_⟩)
    have h3 : (QuotientGroup.mk d.out.2 : G₂ ⧸ K₂).out⁻¹ * d.out.2 ∈ K₂ :=
      QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    simpa using h3
  have key : ∑ᶠ d : (G₁ × G₂) ⧸ (K₁.prod K₂), (h d.out.1 * f d.out.2) • ρ d.out x =
      ∑ᶠ c : G₂ ⧸ K₂, (h (e c).out.1 * f (e c).out.2) • ρ (e c).out x := by
    rw [← finsum_mem_range he (f := fun d : (G₁ × G₂) ⧸ (K₁.prod K₂) => (h d.out.1 * f d.out.2) • ρ d.out x),
      finsum_mem_def, Set.indicator_eq_self.2 hsupp]
  refine key.trans (finsum_congr fun c => ?_)
  have hm : ((1, c.out) : G₁ × G₂)⁻¹ * (e c).out ∈ K₁.prod K₂ :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' (e c)).symm
  obtain ⟨m1, m2⟩ := Subgroup.mem_prod.1 hm
  have m1' : (e c).out.1 ∈ K₁ := by simpa using m1
  have m2' : c.out⁻¹ * (e c).out.2 ∈ K₂ := by simpa using m2
  have hfd : f (e c).out.2 = f c.out := by
    have := hf c.out _ m2'
    rwa [mul_inv_cancel_left] at this
  have hρ : ρ (e c).out x = ρ (1, c.out) x := by
    have h5 : ρ (((1, c.out) : G₁ × G₂) * (((1, c.out) : G₁ × G₂)⁻¹ * (e c).out)) x = ρ (1, c.out) x := by
      rw [map_mul, Module.End.mul_apply, GlobalTheory.LGrp.mem_fixed.1 hx _ hm]
    rwa [mul_inv_cancel_left] at h5
  rw [hfd, h1 _ m1', hρ, one_mul]
  rfl

private theorem tj_zero_mem {E : Type} [Field E] [NumberField E] (w : Pl E) (n : ℕ) (ϖ : w.adicCompletion E) :
    ∀ g ∈ KGL w (n := n), Tj ℂ n (Ov E w) ϖ 0 g = 1 := by
  intro g hg
  unfold Tj
  refine Set.indicator_of_mem ?_ _
  exact ⟨g, hg, 1, one_mem _, by simp [diagJ]⟩

private theorem tj_zero_not {E : Type} [Field E] [NumberField E] (w : Pl E) (n : ℕ) (ϖ : w.adicCompletion E) :
    ∀ g, g ∉ KGL w (n := n) → Tj ℂ n (Ov E w) ϖ 0 g = 0 := by
  intro g hg
  unfold Tj
  refine Set.indicator_of_notMem ?_ _
  rintro ⟨x, hx, y, hy, e⟩
  refine hg ?_
  have : g = x * y := Units.ext (by simpa [diagJ] using e)
  rw [this]
  exact mul_mem hx hy

private theorem tj_right {E : Type} [Field E] [NumberField E] (w : Pl E) (n : ℕ) {ϖ : w.adicCompletion E}
    (hϖ : IsUnifV E w ϖ) (i : ℕ) : ∀ g, ∀ k ∈ KGL w (n := n), Tj ℂ n (Ov E w) ϖ i (g * k) = Tj ℂ n (Ov E w) ϖ i g := by
  intro g k hk
  have := (Tj_mem_hecke (n := n) hϖ i).1 1 ⟨k, hk⟩ g
  simpa using this

private theorem sat_zero (q n : ℕ) (B : Multiset ℂˣ) : satEig q n B 0 = 1 := by
  simp [satEig, Multiset.esymm]

theorem UpperTheory.Zero.ConvolutionTheory.EB.sat2Slice :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (G : H E a b → ℂ) (B₁ B₂ : Multiset ℂˣ), IsSat2 w (pairRt a b w) G B₁ B₂ →
    (∀ (φ : Sm E a) m₂, (φ.1 = fun x => G (x, m₂)) → φ ≠ 0 → IsSatVecGL w (UpperTheory.V.Cj.S.fL a w) φ B₁) ∧
    ∀ (φ : Sm E b) m₁, (φ.1 = fun x => G (m₁, x)) → φ ≠ 0 → IsSatVecGL w (UpperTheory.V.Cj.S.fL b w) φ B₂ := by
  intro E _ _ _ a b w G B₁ B₂ hS
  obtain ⟨hfix, c₁, c₂, hT⟩ := hS
  refine ⟨fun φ m₂ hφ h0 => ?_, fun φ m₁ hφ h0 => ?_⟩
  · have hG0 : G ≠ 0 := by
      rintro rfl
      exact h0 (Subtype.ext hφ)
    have s1 : IsSatVecGL w ((pairRt a b w).comp (MonoidHom.inl _ _)) G B₁ := by
      refine ⟨hG0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, c₁, fun ϖ hϖ i hi => ?_⟩
      · exact GlobalTheory.LGrp.mem_fixed.1 hfix _ (Subgroup.mem_prod.2 ⟨hk, one_mem _⟩)
      · have h1 := hT ϖ hϖ i hi 0 (Nat.zero_le _)
        rw [heckeVec_fst _ _ _ hfix _ _ (tj_right w a hϖ i) (tj_zero_not w b ϖ) (tj_zero_mem w b ϖ),
          sat_zero, mul_one] at h1
        exact h1
    let L : (H E a b → ℂ) →ₗ[ℂ] (GA E a → ℂ) :=
      { toFun := fun F x => F (x, m₂), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have s2 : IsSatVecGL w ((rightReg ℂ (GA E a) ℂ).comp (embW a w)) (L G) B₁ :=
      s1.map L (fun g y => by
        funext x
        simp [L, pairRt, rightReg, LinearMap.funLeft]) (fun e => h0 (Subtype.ext (hφ.trans e)))
    have e : (Sm E a).subtype φ = L G := hφ
    rw [← e] at s2
    exact IsSatVecGL.of_map (Sm E a).subtype (fun _ _ => rfl) Subtype.val_injective s2
  · have hG0 : G ≠ 0 := by
      rintro rfl
      exact h0 (Subtype.ext hφ)
    have s1 : IsSatVecGL w ((pairRt a b w).comp (MonoidHom.inr _ _)) G B₂ := by
      refine ⟨hG0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, c₂, fun ϖ hϖ i hi => ?_⟩
      · exact GlobalTheory.LGrp.mem_fixed.1 hfix _ (Subgroup.mem_prod.2 ⟨one_mem _, hk⟩)
      · have h1 := hT ϖ hϖ 0 (Nat.zero_le _) i hi
        rw [heckeVec_snd _ _ _ hfix _ _ (tj_right w b hϖ i) (tj_zero_not w a ϖ) (tj_zero_mem w a ϖ),
          sat_zero, one_mul] at h1
        exact h1
    let L : (H E a b → ℂ) →ₗ[ℂ] (GA E b → ℂ) :=
      { toFun := fun F x => F (m₁, x), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    have s2 : IsSatVecGL w ((rightReg ℂ (GA E b) ℂ).comp (embW b w)) (L G) B₂ :=
      s1.map L (fun g y => by
        funext x
        simp [L, pairRt, rightReg, LinearMap.funLeft]) (fun e => h0 (Subtype.ext (hφ.trans e)))
    have e : (Sm E b).subtype φ = L G := hφ
    rw [← e] at s2
    exact IsSatVecGL.of_map (Sm E b).subtype (fun _ _ => rfl) Subtype.val_injective s2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.HeckeComponentVectors.TjZeroAct
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.F.RS

attribute [local instance] borelG borelF borelA borelH

section SlopeTestRemainingChoices

open GlobalTheory.LGrp GlobalTheory.LFun.SatCompare GlobalTheory.LocGL GlobalTheory.WeylGL

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem unifIs (w : Pl E) : IsUnifV E w (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) :=
  Classical.epsilon_spec (exists_isUnifV w)

private theorem tj_indep (w : Pl E) (n j : ℕ) {ϖ ϖ' : w.adicCompletion E} (hu : IsUnifV E w ϖ)
    (hu' : IsUnifV E w ϖ') : Tj ℂ n (Ov E w) ϖ' j = Tj ℂ n (Ov E w) ϖ j := by
  have h0 := ne_zero_of_isUnifV hu
  have hv : Valued.v (ϖ' / ϖ) = 1 := by
    rw [map_div₀, hu, hu', div_self WithZero.coe_ne_zero]
  have e := Final.TjIndep _ (Ov E w) ϖ (ϖ' / ϖ) ℂ n j hv.le
    (show Valued.v (ϖ' / ϖ)⁻¹ ≤ 1 by rw [map_inv₀, hv, inv_one]) (div_ne_zero (ne_zero_of_isUnifV hu') h0)
  rwa [div_mul_cancel₀ _ h0] at e

private theorem tj_zero_act (w : Pl E) (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GLw n w) V) {ϖ : w.adicCompletion E} (hu : IsUnifV E w ϖ) {x : V}
    (hx : x ∈ fixed π (KGL w (n := n))) : heckeVec π (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ 0) x = x := by
  have h0 := ne_zero_of_isUnifV hu
  have e : Tj ℂ n (Ov E w) ϖ 0 = dosetInd ℂ (KGL w (n := n)) 1 := by
    rw [Tj_eq h0]
    congr 1
  rw [e, heckeVec_one (Final.GLintComm E w n) hx]

private theorem tj_top_ne (w : Pl E) (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GLw n w) V) {ϖ : w.adicCompletion E} (hu : IsUnifV E w ϖ) {x : V} (hx0 : x ≠ 0)
    (hx : x ∈ fixed π (KGL w (n := n))) {c : ℂ} (h1 : heckeVec π (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ n) x = c • x) : c ≠ 0 := by
  intro e
  have h0 := ne_zero_of_isUnifV hu
  have hTn : Tj ℂ n (Ov E w) ϖ n = dosetInd ℂ (KGL w (n := n)) (tor h0 fun _ => 1) := by
    rw [Tj_eq h0]; simp
  rw [e, zero_smul, hTn, heckeVec_dosetInd (R := {tor h0 fun _ => 1}) hx, Finset.sum_singleton] at h1
  · exact hx0 (by simpa [← Module.End.mul_apply, ← map_mul] using congrArg (π (tor h0 fun _ => 1)⁻¹) h1)
  · intro γ hγ
    exact mem_doset.2 ⟨1, one_mem _, 1, one_mem _, by simpa using hγ⟩
  · intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doset.1 hg
    refine ⟨_, ⟨Finset.mem_singleton_self _, ?_⟩, fun γ hγ => Finset.mem_singleton.1 hγ.1⟩
    rw [← tor_const_comm, mul_assoc, inv_mul_cancel_left]
    exact mul_mem ha hb

end SlopeTestRemainingChoices

theorem UpperTheory.Zero.ConvolutionTheory.EB.sat2Ex :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (V ι : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLw a w × GLw b w) V) (x : ι → V)
    (t : Fin (a + 1) × Fin (b + 1) → ℂ), x ≠ 0 → (∀ i, x i ∈ fixed ρ (K2 a b w)) →
    (∀ (p : Fin (a + 1) × Fin (b + 1)) i, heckeVec ρ (K2 a b w) (fun y : GLw a w × GLw b w => Tj ℂ a (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) p.1 y.1 * Tj ℂ b (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) p.2 y.2) (x i) = t p • x i) →
    ∃ B₁ B₂ : Multiset ℂˣ, B₁.card = a ∧ B₂.card = b ∧ (∀ p, t p = satEig (qV E w) a B₁ p.1 * satEig (qV E w) b B₂ p.2) ∧ ∀ i, IsSat2 w ρ (x i) B₁ B₂ := by
  intro E _ _ _ a b w V ι _ _ ρ x t hx0 hfix ht
  have hu := unifIs w
  have hKa := Final.GLintComm E w a
  have hKb := Final.GLintComm E w b
  have hTa := fun i : ℕ => Tj_mem_hecke (n := a) hu i
  have hTb := fun j : ℕ => Tj_mem_hecke (n := b) hu j
  obtain ⟨k₀, hk₀⟩ : ∃ k, x k ≠ 0 := Function.ne_iff.1 hx0
  have fA : ∀ k, x k ∈ fixed (ρ.comp (MonoidHom.inl _ _)) (KGL w (n := a)) := fun k =>
    GlobalTheory.LGrp.mem_fixed.2 fun g hg =>
      GlobalTheory.LGrp.mem_fixed.1 (hfix k) (g, 1) (Subgroup.mem_prod.2 ⟨hg, one_mem _⟩)
  have fB : ∀ k, x k ∈ fixed (ρ.comp (MonoidHom.inr _ _)) (KGL w (n := b)) := fun k =>
    GlobalTheory.LGrp.mem_fixed.2 fun g hg =>
      GlobalTheory.LGrp.mem_fixed.1 (hfix k) (1, g) (Subgroup.mem_prod.2 ⟨one_mem _, hg⟩)
  have fAB : ∀ k (j : ℕ), heckeVec (ρ.comp (MonoidHom.inr _ _)) (KGL w (n := b))
      (Tj ℂ b (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) j) (x k) ∈ fixed (ρ.comp (MonoidHom.inl _ _)) (KGL w (n := a)) := by
    intro k j
    refine GlobalTheory.LGrp.mem_fixed.2 fun g hg => ?_
    have key := map_heckeVec hKb (hTb j) (ρ := ρ.comp (MonoidHom.inr _ _)) (ρ' := ρ.comp (MonoidHom.inr _ _))
      ((ρ.comp (MonoidHom.inl _ _)) g) (fun g' y => by
        simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply]
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
        simp) (x k)
    rw [key, GlobalTheory.LGrp.mem_fixed.1 (fA k) g hg]
  have pp : ∀ (p : Fin (a + 1) × Fin (b + 1)) k, heckeVec (ρ.comp (MonoidHom.inl _ _)) (KGL w (n := a))
      (Tj ℂ a (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) p.1) (heckeVec (ρ.comp (MonoidHom.inr _ _)) (KGL w (n := b))
        (Tj ℂ b (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) p.2) (x k)) = t p • x k := fun p k => by
    rw [← heckeVec_pairProd ρ hKa hKb (hTa _) (hTb _) (hfix k)]
    exact ht p k
  have eA : ∀ (i : Fin (a + 1)) k, heckeVec (ρ.comp (MonoidHom.inl _ _)) (KGL w (n := a))
      (Tj ℂ a (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) i) (x k) = t (i, 0) • x k := fun i k => by
    have := pp (i, 0) k
    simp only [Fin.val_zero] at this
    rwa [tj_zero_act w b _ hu (fB k)] at this
  have eB : ∀ (j : Fin (b + 1)) k, heckeVec (ρ.comp (MonoidHom.inr _ _)) (KGL w (n := b))
      (Tj ℂ b (Ov E w) (UpperTheory.V.Z.Tf.GlobalTraceComparison.unif w) j) (x k) = t (0, j) • x k := fun j k => by
    have := pp (0, j) k
    simp only [Fin.val_zero] at this
    rwa [tj_zero_act w a _ hu (fAB k j)] at this
  have t00 : t (0, 0) = 1 := by
    have h1 := eA 0 k₀
    simp only [Fin.val_zero] at h1
    rw [tj_zero_act w a _ hu (fA k₀)] at h1
    exact smul_left_injective ℂ hk₀ (by simpa using h1.symm)
  have mul : ∀ p : Fin (a + 1) × Fin (b + 1), t p = t (p.1, 0) * t (0, p.2) := fun p => by
    have h1 := pp p k₀
    rw [eB p.2 k₀, heckeVec_smul_pair _ hKa (hTa _), eA p.1 k₀, smul_smul, mul_comm] at h1
    exact smul_left_injective ℂ hk₀ h1.symm
  have hta : t (Fin.last a, 0) ≠ 0 :=
    tj_top_ne w a _ hu hk₀ (fA k₀) (by simpa using eA (Fin.last a) k₀)
  have htb : t (0, Fin.last b) ≠ 0 :=
    tj_top_ne w b _ hu hk₀ (fB k₀) (by simpa using eB (Fin.last b) k₀)
  obtain ⟨B₁, c₁, h₁⟩ := _root_.GlobalTheory.LFun.exists_satEig_eq (qV E w) a (qV_ne_zero w)
    (fun i => if h : i < a + 1 then t (⟨i, h⟩, 0) else 0) (by simpa using t00)
    (by simpa [Fin.last] using hta)
  obtain ⟨B₂, c₂, h₂⟩ := _root_.GlobalTheory.LFun.exists_satEig_eq (qV E w) b (qV_ne_zero w)
    (fun j => if h : j < b + 1 then t (0, ⟨j, h⟩) else 0) (by simpa using t00)
    (by simpa [Fin.last] using htb)
  have s₁ : ∀ i : Fin (a + 1), satEig (qV E w) a B₁ i = t (i, 0) := fun i => by
    rw [h₁ i (Nat.lt_succ_iff.1 i.2), dite_eq_left i.2]
  have s₂ : ∀ j : Fin (b + 1), satEig (qV E w) b B₂ j = t (0, j) := fun j => by
    rw [h₂ j (Nat.lt_succ_iff.1 j.2), dite_eq_left j.2]
  have tp : ∀ p : Fin (a + 1) × Fin (b + 1), t p = satEig (qV E w) a B₁ p.1 * satEig (qV E w) b B₂ p.2 := fun p => by
    rw [s₁, s₂]
    exact mul p
  refine ⟨B₁, B₂, c₁, c₂, tp, fun k => ⟨hfix k, c₁, c₂, fun ϖ hϖ i hi j hj => ?_⟩⟩
  have h := ht (⟨i, Nat.lt_succ_iff.2 hi⟩, ⟨j, Nat.lt_succ_iff.2 hj⟩) k
  rw [tp] at h
  rw [tj_indep w a i hu hϖ, tj_indep w b j hu hϖ]
  exact h
end

