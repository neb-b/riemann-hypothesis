module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PAbsStep
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc

private lemma lv_eq_sum {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (K : Subgroup G) (u : G → ℂ) (S : Finset (G ⧸ K)) (hS : ∀ c : G ⧸ K, u c.out ≠ 0 → c ∈ S) :
    Lv ρ K u = ∑ c ∈ S, u c.out • ρ c.out := by
  have hs : Function.support (fun c : G ⧸ K => u c.out • (ρ c.out ∘ₗ LinearMap.id)) ⊆ (S : Set (G ⧸ K)) := by
    intro c hc
    refine Finset.mem_coe.2 (hS c fun h0 => hc ?_)
    simp [h0]
  simp only [Lv, GlobalTheory.BCT.levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
  rw [finsum_eq_sum_of_support_subset _ hs]
  rfl

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.absStep_pf :
    AbsStep := by
  intro G A V _ _ _ _ ρ K N j q f h h₁ hqj hcomm hjN hqK hh hh₁N hK hfN hfs hh₁s y hy
  classical
  have hyk : ∀ k ∈ K, ρ k y = y := fun k hk => by
    have := hy ⟨k, hk⟩
    simpa using this

  have hx0 : ∀ g, q ((j (q g))⁻¹ * g) = 1 := fun g => by simp [hqj]
  have hright : ∀ g k, k ∈ K → h (g * k) = h g := by
    intro g k hk
    rw [hh (g * k), hh g]
    have e1 : f (q (g * k)) = f (q g) := by
      rw [map_mul]
      exact hfN _ (hqK k hk) _
    have c : Commute (j (q k)) ((j (q g))⁻¹ * g) := hcomm (q k) _ (hx0 g)
    have e2 : (j (q (g * k)))⁻¹ * (g * k) = ((j (q g))⁻¹ * g) * ((j (q k))⁻¹ * k) := by
      have c' : (j (q k))⁻¹ * ((j (q g))⁻¹ * g) = ((j (q g))⁻¹ * g) * (j (q k))⁻¹ := c.inv_left.eq
      rw [map_mul, map_mul, mul_inv_rev, ← mul_assoc ((j (q g))⁻¹ * g), ← c']
      simp only [mul_assoc]
    rw [e1, e2, (hK _ (K.mul_mem (K.inv_mem (hjN _ (hqK k hk))) hk) _).2]
  set S₁ : Finset (A ⧸ N) := hfs.toFinset with hS₁
  set S₂ : Finset (G ⧸ K) := hh₁s.toFinset with hS₂
  have m₁ : ∀ s, s ∈ S₁ ↔ f s.out ≠ 0 := fun s => by simp [hS₁]
  have m₂ : ∀ t, t ∈ S₂ ↔ h₁ t.out ≠ 0 := fun t => by simp [hS₂]
  let φ : (A ⧸ N) × (G ⧸ K) → G ⧸ K := fun p => ((j p.1.out * p.2.out : G) : G ⧸ K)
  have hterm : ∀ (s : A ⧸ N) (t : G ⧸ K), t ∈ S₂ → h (j s.out * t.out) = f s.out * h₁ t.out := by
    intro s t ht
    have hn : q t.out ∈ N := hh₁N _ ((m₂ t).1 ht)
    have e0 : q (j s.out * t.out) = s.out * q t.out := by rw [map_mul, hqj]
    have e1 : (j (q (j s.out * t.out)))⁻¹ * (j s.out * t.out) = (j (q t.out))⁻¹ * t.out := by
      rw [e0, map_mul, mul_inv_rev]
      group
    rw [hh, e1, e0, hfN _ hn, (hK _ (K.inv_mem (hjN _ hn)) _).1]
  have hinj : Set.InjOn φ (S₁ ×ˢ S₂ : Finset _) := by
    rintro ⟨s, t⟩ hp ⟨s', t'⟩ hp' e
    have ht : t ∈ S₂ := (Finset.mem_product.1 (Finset.mem_coe.1 hp)).2
    have ht' : t' ∈ S₂ := (Finset.mem_product.1 (Finset.mem_coe.1 hp')).2
    have hn : q t.out ∈ N := hh₁N _ ((m₂ t).1 ht)
    have hn' : q t'.out ∈ N := hh₁N _ ((m₂ t').1 ht')
    have hk : (j s.out * t.out)⁻¹ * (j s'.out * t'.out) ∈ K := QuotientGroup.eq.1 e
    have hq : (q t.out)⁻¹ * (s.out⁻¹ * s'.out) * q t'.out ∈ N := by
      have := hqK _ hk
      simpa [hqj, mul_assoc] using this
    have hs : s.out⁻¹ * s'.out ∈ N := by
      have := N.mul_mem (N.mul_mem hn hq) (N.inv_mem hn')
      simpa [mul_assoc] using this
    have es : s = s' := by
      rw [← QuotientGroup.out_eq' s, ← QuotientGroup.out_eq' s']
      exact QuotientGroup.eq.2 hs
    subst es
    have ht2 : t.out⁻¹ * t'.out ∈ K := by
      simpa [mul_assoc] using hk
    have et : t = t' := by
      rw [← QuotientGroup.out_eq' t, ← QuotientGroup.out_eq' t']
      exact QuotientGroup.eq.2 ht2
    rw [et]
  have hsupp : ∀ c : G ⧸ K, h c.out ≠ 0 → c ∈ (S₁ ×ˢ S₂).image φ := by
    intro c hc
    set g := c.out with hg
    set a := q g with ha
    set x := (j a)⁻¹ * g with hx
    rw [hh g] at hc
    have hfa : f a ≠ 0 := left_ne_zero_of_mul hc
    have hhx : h₁ x ≠ 0 := right_ne_zero_of_mul hc
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N a
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
    refine Finset.mem_image.2 ⟨((a : A ⧸ N), (x : G ⧸ K)), Finset.mem_product.2 ⟨?_, ?_⟩, ?_⟩
    · show ((a : A ⧸ N)) ∈ S₁
      rw [m₁, hn, hfN _ n.2]
      exact hfa
    · show ((x : G ⧸ K)) ∈ S₂
      rw [m₂, hk, (hK _ k.2 _).2]
      exact hhx
    · show ((j (a : A ⧸ N).out * (x : G ⧸ K).out : G) : G ⧸ K) = c
      have c1 : Commute (j (n : A)) x := hcomm _ _ (hx0 g)
      have e : j (a : A ⧸ N).out * (x : G ⧸ K).out = g * (j (n : A) * (k : G)) := by
        have hgx : j a * x = g := by rw [hx]; group
        rw [hn, hk, map_mul, mul_assoc (j a), ← mul_assoc (j (n : A)), c1.eq, mul_assoc x, ← mul_assoc (j a), hgx]
      rw [e, QuotientGroup.mk_mul_of_mem _ (K.mul_mem (hjN _ n.2) k.2), hg, QuotientGroup.out_eq']
  have hout : ∀ p ∈ S₁ ×ˢ S₂, h (φ p).out • ρ (φ p).out y = (f p.1.out * h₁ p.2.out) • ρ (j p.1.out * p.2.out) y := by
    rintro ⟨s, t⟩ hp
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (j s.out * t.out)
    have ht : t ∈ S₂ := (Finset.mem_product.1 hp).2
    show h (((j s.out * t.out : G) : G ⧸ K)).out • ρ (((j s.out * t.out : G) : G ⧸ K)).out y = _
    rw [hk, hright _ _ k.2, hterm s t ht, map_mul ρ (j s.out * t.out), Module.End.mul_apply, hyk _ k.2]
  rw [lv_eq_sum ρ K h _ hsupp, lv_eq_sum (ρ.comp j) N f S₁ (fun s hs => (m₁ s).2 hs),
    lv_eq_sum ρ K h₁ S₂ (fun t ht => (m₂ t).2 ht)]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  rw [Finset.sum_image hinj, Finset.sum_congr rfl hout, Finset.sum_product]
  refine Finset.sum_congr rfl fun s _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [MonoidHom.comp_apply, map_sum, map_smul, Finset.smul_sum, smul_smul, map_mul, Module.End.mul_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PHeckeSum
section
noncomputable section

open MeasureTheory Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.BCT PositivityTheory.Rg.BcB
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section Abs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

private theorem coset_integral (μ : Measure G) [μ.IsMulLeftInvariant] {K : Subgroup G} (hK : IsOpen (K : Set G))
    (hfin : μ (K : Set G) ≠ ⊤) {h : G → ℂ} (hc : HasCompactSupport h) (hinv : ∀ g, ∀ k ∈ K, h (g * k) = h g) :
    ∃ T : Finset (G ⧸ K), (∀ q : G ⧸ K, h q.out ≠ 0 → q ∈ T) ∧ ∀ f : G → ℂ, (∀ g, ∀ k ∈ K, f (g * k) = f g) →
      ∫ y, h y * f y ∂μ = ∑ q ∈ T, (μ.real (K : Set G) : ℂ) * (h q.out * f q.out) := by
  let c : G ⧸ K → Set G := fun q => {y | q.out⁻¹ * y ∈ K}
  have hcm : ∀ q y, y ∈ c q ↔ (QuotientGroup.mk y : G ⧸ K) = q := by
    intro q y
    change q.out⁻¹ * y ∈ K ↔ _
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    exact eq_comm
  have hco : ∀ q, IsOpen (c q) := fun q => hK.preimage (continuous_const.mul continuous_id)
  have hmeas : ∀ q, μ (c q) = μ (K : Set G) := fun q => measure_preimage_mul μ q.out⁻¹ (K : Set G)
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover (fun g => c (QuotientGroup.mk g))
    (fun g _ => (hco _).mem_nhds ((hcm _ g).2 rfl))
  let T : Finset (G ⧸ K) := t.image fun g => (QuotientGroup.mk g : G ⧸ K)
  have hT : ∀ y, h y ≠ 0 → (QuotientGroup.mk y : G ⧸ K) ∈ T := by
    intro y hy
    obtain ⟨g, hg, hyg⟩ := Set.mem_iUnion₂.1 (ht (subset_tsupport h hy))
    rw [(hcm _ y).1 hyg]
    exact Finset.mem_image_of_mem _ hg
  refine ⟨T, fun q hq => ?_, fun f hf => ?_⟩
  · simpa [QuotientGroup.out_eq'] using hT _ hq
  have hval : ∀ q y, y ∈ c q → h y * f y = h q.out * f q.out := by
    intro q y hy
    have e : y = q.out * (q.out⁻¹ * y) := by group
    rw [e, hinv _ _ hy, hf _ _ hy]
  have hsum : (fun y => h y * f y) = fun y => ∑ q ∈ T, (c q).indicator (fun _ => h q.out * f q.out) y := by
    funext y
    by_cases hy : (QuotientGroup.mk y : G ⧸ K) ∈ T
    · have hyc : y ∈ c (QuotientGroup.mk y) := (hcm _ y).2 rfl
      rw [Finset.sum_eq_single (QuotientGroup.mk y : G ⧸ K), Set.indicator_of_mem hyc, hval _ y hyc]
      · intro q _ hq
        exact Set.indicator_of_notMem (fun hyq => hq ((hcm q y).1 hyq).symm) _
      · exact fun h' => (h' hy).elim
    · have hy0 : h y = 0 := by
        by_contra h'
        exact hy (hT y h')
      rw [hy0, zero_mul]
      refine (Finset.sum_eq_zero fun q hq => Set.indicator_of_notMem (fun hyq => hy ?_) _).symm
      rwa [(hcm q y).1 hyq]
  rw [hsum, integral_finsetSum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hco q).measurableSet]
    simp only [Measure.real, hmeas q, Complex.real_smul]
  · intro q _
    refine (integrable_indicator_iff (hco q).measurableSet).2 ?_
    exact integrableOn_const (by rw [hmeas q]; exact hfin)

end Abs

theorem heckeSum_pf : HeckeSum := by
  intro E _ _ _ n K hKo hKc μf _ h hh y hy
  have hfix : ∀ k ∈ K, finRep E n k y = y := fun k hk => by
    simpa using hy ⟨k, hk⟩
  obtain ⟨T, hT, hI⟩ := coset_integral μf hKo hKc.measure_lt_top.ne hh.1 (fun g k hk => (hh.2 k hk g).2)
  funext x
  have hf := hI (fun g => y.1 (x * finGL E n g)) (fun g k hk => by
    have e := congrArg (fun φ : Sm E n => φ.1 (x * finGL E n g)) (hfix k hk)
    have e' : y.1 (x * finGL E n g * finGL E n k) = y.1 (x * finGL E n g) := e
    simpa [mul_assoc] using e')
  have hL : Lv (finRep E n) K h = ∑ q ∈ T, h q.out • finRep E n q.out := by
    have hs : (Function.support fun q : GF E n ⧸ K => h q.out • (finRep E n q.out ∘ₗ LinearMap.id)) ⊆ T := by
      intro q hq
      refine hT q fun h0 => hq ?_
      simp [h0]
    simp only [Lv, levOp, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_smul]
    rw [finsum_eq_sum_of_support_subset _ hs]
    rfl
  have hv : (∑ q ∈ T, (h q.out • finRep E n q.out) y : Sm E n).1 x =
      ∑ q ∈ T, h q.out * y.1 (x * finGL E n q.out) := by
    rw [Submodule.coe_sum, Finset.sum_apply]
    rfl
  rw [hL, heckeOp, hf, LinearMap.sum_apply, hv, Finset.mul_sum]
  rfl

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PLcLevel
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

private theorem exists_core {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K M : Subgroup G) (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hMo : IsOpen (M : Set G)) (hMK : M ≤ K) :
    ∃ C : Subgroup G, IsOpen (C : Set G) ∧ C ≤ M ∧ ∀ k ∈ K, ∀ x ∈ C, k * x * k⁻¹ ∈ C := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  set M' : Subgroup K := M.subgroupOf K with hM'
  have hM'o : IsOpen (M' : Set K) := hMo.preimage continuous_subtype_val
  haveI : Finite (K ⧸ M') := Subgroup.quotient_finite_of_isOpen M' hM'o
  haveI : M'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hcl : IsClosed (M'.normalCore : Set K) := by
    have hc : IsClosed (M' : Set K) := Subgroup.isClosed_of_isOpen M' hM'o
    have : (M'.normalCore : Set K) = ⋂ b : K, (fun a : K => b * a * b⁻¹) ⁻¹' (M' : Set K) := by
      ext a
      simp [Subgroup.normalCore, Set.mem_iInter]
    rw [this]
    exact isClosed_iInter fun b => hc.preimage (by fun_prop)
  have hop : IsOpen (M'.normalCore : Set K) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hcl
  refine ⟨M'.normalCore.map K.subtype, ?_, ?_, ?_⟩
  · have : ((M'.normalCore.map K.subtype : Subgroup G) : Set G) = Subtype.val '' (M'.normalCore : Set K) := by
      ext x; simp
    rw [this]
    exact hKo.isOpenMap_subtype_val _ hop
  · rintro _ ⟨a, ha, rfl⟩
    have h1 : a ∈ M' := Subgroup.normalCore_le M' ha
    exact h1
  · rintro k hk _ ⟨a, ha, rfl⟩
    refine ⟨⟨k, hk⟩ * a * (⟨k, hk⟩ : K)⁻¹, ?_, by simp⟩
    exact (Subgroup.normalCore_normal M').conj_mem a ha _

private theorem hecke_slice {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E)
    (K' : Subgroup (GLw n w × GLw 0 w)) (f : GLw n w × GLw 0 w → ℂ) (hf : IsHecke K' f)
    (N : Subgroup (GLw n w)) (hN : ∀ k ∈ N, ((k, 1) : GLw n w × GLw 0 w) ∈ K') :
    IsHecke N (fun g => f (g, 1)) := by
  refine ⟨?_, fun k hk x => ?_⟩
  · haveI : Unique (GLw 0 w) := Unique.mk' _
    have e : (fun g : GLw n w => ((g, 1) : GLw n w × GLw 0 w)) =
        ⇑(Homeomorph.prodUnique (GLw n w) (GLw 0 w)).symm := by
      funext g
      exact Prod.ext rfl (Subsingleton.elim _ _)
    have h : Topology.IsClosedEmbedding (fun g : GLw n w => ((g, 1) : GLw n w × GLw 0 w)) := by
      rw [e]
      exact (Homeomorph.prodUnique (GLw n w) (GLw 0 w)).symm.isClosedEmbedding
    exact hf.1.comp_isClosedEmbedding h
  · have h := hf.2 _ (hN k hk) (x, 1)
    simpa using h

theorem lcLevel_pf : LcLevel := by
  classical
  intro E _ _ _ n Z N₀ hN₀ φ₁ φ₂ hφ
  have hK := fun w : Pl E => GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have key : ∀ w ∈ Z, ∃ C : Subgroup (GLw n w), IsOpen (C : Set (GLw n w)) ∧ C ≤ N₀ w ∧
      (∀ k ∈ KGL w (n := n), ∀ x ∈ C, k * x * k⁻¹ ∈ C) ∧ ∀ b, IsHecke C (two φ₁ φ₂ w b) := by
    intro w hw
    obtain ⟨⟨A, hAo, -, hA⟩, ⟨B, hBo, -, hB⟩⟩ := hφ w hw
    let ι : GLw n w →* GLw n w × GLw 0 w := MonoidHom.inl _ _
    have hι : Continuous ι := continuous_id.prodMk continuous_const
    have hMo : IsOpen ((N₀ w ⊓ A.comap ι ⊓ B.comap ι : Subgroup (GLw n w)) : Set (GLw n w)) :=
      ((hN₀ w).1.inter (hAo.preimage hι)).inter (hBo.preimage hι)
    obtain ⟨C, hCo, hCM, hCn⟩ := exists_core (KGL w (n := n)) (N₀ w ⊓ A.comap ι ⊓ B.comap ι) (hK w).1 (hK w).2
      hMo (fun x hx => (hN₀ w).2.1 hx.1.1)
    refine ⟨C, hCo, fun x hx => (hCM hx).1.1, hCn, ?_⟩
    rintro (_ | _)
    · exact hecke_slice w A (φ₁ w) hA C fun k hk => (hCM hk).1.2
    · exact hecke_slice w B (φ₂ w) hB C fun k hk => (hCM hk).2
  choose! C hC using key
  refine ⟨fun w => if w ∈ Z then C w else N₀ w, ?_, ?_, ?_⟩
  · intro w
    by_cases hw : w ∈ Z
    · simp only [if_pos hw]
      obtain ⟨a, b, c, -⟩ := hC w hw
      exact ⟨a, b.trans (hN₀ w).2.1, c, fun h => absurd hw h⟩
    · simp only [if_neg hw]
      exact hN₀ w
  · intro w
    by_cases hw : w ∈ Z
    · simp only [if_pos hw]
      exact (hC w hw).2.1
    · simp only [if_neg hw]
      exact le_rfl
  · intro w hw b
    simp only [if_pos hw]
    exact (hC w hw).2.2.2 b

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PLevelTr
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

private theorem lv_unit {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) (hv : v ∈ fixed ρ K) :
    Lv ρ K ((K : Set G).indicator 1) v = v := by
  have hc : (QuotientGroup.mk 1 : G ⧸ K).out ∈ K := by
    have h : (QuotientGroup.mk (QuotientGroup.mk 1 : G ⧸ K).out : G ⧸ K) = QuotientGroup.mk 1 :=
      QuotientGroup.out_eq' _
    simpa using QuotientGroup.eq.1 h
  have hq : ∀ q : G ⧸ K, q ≠ QuotientGroup.mk 1 → q.out ∉ K := by
    intro q hne hmem
    apply hne
    rw [← QuotientGroup.out_eq' q]
    exact QuotientGroup.eq.2 (by simpa using hmem)
  unfold Lv levOp
  rw [finsum_eq_single _ (QuotientGroup.mk 1 : G ⧸ K)
    (fun q hne => by rw [Set.indicator_of_notMem (hq q hne), zero_smul]),
    Set.indicator_of_mem (show _ ∈ (K : Set G) from hc)]
  simpa using hv ⟨_, hc⟩

private theorem trOn_of_id {V : Type} [AddCommGroup V] [Module ℂ V] (M : Submodule ℂ V)
    [FiniteDimensional ℂ M] (L : V →ₗ[ℂ] V) (hL : ∀ v ∈ M, L v = v) :
    trOn M L = (Module.finrank ℂ M : ℂ) := by
  have h : ∀ v ∈ M, L v ∈ M := fun v hv => by rw [hL v hv]; exact hv
  have hid : L.restrict h = LinearMap.id := by
    ext v
    simp [LinearMap.restrict_apply, hL v.1 v.2]
  unfold trOn
  rw [dite_eq_left h, hid]
  exact LinearMap.trace_id ℂ _

private theorem finFn_one {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (S : Set (Pl E))
    (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w) : (fun g => finFn S φ₁ φ₂ (g, 1)) = pf S (two φ₁ φ₂) := by
  funext g
  have h1 : ∀ w : Pl E, atW w ((g, 1) : Gf E n 0) = (qw n w false g, 1) :=
    fun w => Prod.ext rfl (map_one (GeneralLinearGroup.map (pLoc E w)))
  have h2 : ∀ w : Pl E, atW w (thP E n 0 (g, 1)) = (qw n w true g, 1) := by
    intro w
    refine Prod.ext rfl ?_
    simp [atW, thP]
  unfold finFn pf
  simp only [h1, h2]
  rfl

private theorem ind_hecke {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (w : Pl E)
    (M N' : Subgroup (GLw n w)) (ho : IsOpen (M : Set (GLw n w))) (hM : M ≤ KGL w (n := n)) (hN : N' ≤ M) :
    IsHecke N' ((M : Set (GLw n w)).indicator 1) := by
  have hcl : IsClosed (M : Set (GLw n w)) := M.isClosed_of_isOpen ho
  have hcomp : IsCompact (M : Set (GLw n w)) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n).2.of_isClosed_subset hcl hM
  refine ⟨hcomp.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal Set.support_indicator_subset hcl), fun k hk x => ?_⟩
  have a1 : k * x ∈ M ↔ x ∈ M := M.mul_mem_cancel_left (hN hk)
  have a2 : x * k ∈ M ↔ x ∈ M := M.mul_mem_cancel_right (hN hk)
  simp only [Set.indicator, SetLike.mem_coe, a1, a2, Pi.one_apply, and_self]

theorem levelTr_pf : UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.admitted → ZTr → SeenTr → TTr → LevelTr := by
  intro hAdm hZ hSeen hT E _ _ _ n S Z N hSec hSp hG π y B τ hB hτ
  obtain ⟨hne, d₀, hd₀, hd⟩ := hZ E n S Z N hSec hSp hG π y τ hτ
  have hc : ∀ w ∈ Z, ∃ c : ℂ, c ≠ 0 ∧ ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) →
      GlobalTheory.BCT.trOn (fixed (τ w).ρ (N w)) (Lv (τ w).ρ (N w) (two φ₁ φ₂ w false) * Lv (τ w).ρ (N w) (two φ₁ φ₂ w true)) =
        c * trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1) :=
    fun w hw => hSeen E n w (hSp w hw).2 (τ w) (N w) (hG w).1 (hG w).2.1
  choose! c hc0 hc using hc
  refine ⟨?_, d₀ * ∏ w ∈ Z, c w, mul_ne_zero hd₀ (Finset.prod_ne_zero_iff.2 hc0), ?_⟩
  · let φ₀ : ∀ w : Pl E, LF n 0 w := fun w p => (N w : Set (GLw n w)).indicator 1 p.1
    have h2 : ∀ w b, two φ₀ φ₀ w b = (N w : Set (GLw n w)).indicator 1 := by
      intro w b
      cases b <;> rfl
    refine ⟨φ₀, fun w _ N' hN' b => ?_, Finset.prod_ne_zero_iff.2 fun w hw h0 => ?_⟩
    · rw [h2]
      exact ind_hecke w (N w) N' (hG w).1 (hG w).2.1 hN'
    · haveI : FiniteDimensional ℂ (fixed (τ w).ρ (N w)) := hAdm E n w (τ w) (N w) (hG w).1
      have e := hc w hw φ₀ φ₀ fun b => by
        rw [h2]
        exact ind_hecke w (N w) (N w) (hG w).1 (hG w).2.1 le_rfl
      rw [h0, mul_zero, h2, h2, trOn_of_id _ _ fun v hv => by
        rw [Module.End.mul_apply, lv_unit _ _ v hv, lv_unit _ _ v hv]] at e
      exact hne w hw (Submodule.finrank_eq_zero.1 (Nat.cast_eq_zero.1 e))
  · intro φ₁ φ₂ hφ T hTZ e₁ e₂ hTE
    obtain ⟨h1, h2, h3⟩ := hT E n S Z N hSec hSp hG π y B hB φ₁ φ₂ hφ T hTZ e₁ e₂ hTE
    have hF : ∀ w ∈ Z, ∀ b, two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) w b = two φ₁ φ₂ w b := by
      intro w hw b
      cases b <;> simp [two, intersection_update_fsHerm_neg_one, hw]
    have hP : ∀ w ∈ Z, GlobalTheory.BCT.trOn (fixed (τ w).ρ (N w))
        (Lv (τ w).ρ (N w) (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) w false) *
          Lv (τ w).ρ (N w) (two (intersection_update_fsHerm_neg_one Z ∅ φ₁ e₁) (intersection_update_fsHerm_neg_one Z ∅ φ₂ e₂) w true)) =
        c w * trc (τ w).ρ (KGL w (n := n)) fun g => seen φ₁ φ₂ w (g, 1) := by
      intro w hw
      rw [hF w hw, hF w hw]
      exact hc w hw φ₁ φ₂ (hφ w hw)
    rw [finFn_one S (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂)]
    refine ⟨h1, ?_⟩
    rw [h3, smul_mul_assoc, map_smul, hd _ h2, smul_eq_mul, Finset.prod_congr rfl hP, Finset.prod_mul_distrib]
    ring

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.PLocComm
section
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi UpperTheory.Zero.ConvolutionTheory.EB PositivityTheory.Rg.BcB.Desc
open GlobalTheory.BCT GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host Formalism.UG Formalism.BasicNotions

private theorem lv_commute {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (H : Subgroup G) (hH : IsOpen (H : Set G)) (f : G → ℂ)
    (hf : HasCompactSupport f) (T : Module.End ℂ V) (hT : ∀ a, Commute T (ρ a)) : Commute T (Lv ρ H f) := by
  have hs := GlobalTheory.TwTrLevel.finite_supp H hH f hf
  have hsupp : (Function.support fun q : G ⧸ H =>
      f q.out • (ρ q.out ∘ₗ (LinearMap.id : V →ₗ[ℂ] V))).Finite :=
    hs.subset fun q hq h0 => hq (by simp [h0])
  unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.Lv levOp
  rw [finsum_eq_sum_of_support_subset _ (s := hsupp.toFinset) (by simp)]
  refine Commute.smul_right (Commute.sum_right _ _ _ fun q _ => Commute.smul_right ?_ _) _
  rw [LinearMap.comp_id]
  exact hT _

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.locComm_pf :
    SlotBasic → LevTop → LocComm := by
  intro hSF _ E _ _ _ n S Z N hSec _ hG i hi f hf
  obtain ⟨-, -, hloc, hind, -⟩ := hSF E n S hSec
  have hmem : ∀ c, c ∈ Lev S N ↔ ∀ k, Sl S k → qw n k.1 k.2 c ∈ N k.1 := by
    intro c
    simp only [Lev, Subgroup.mem_iInf, Subgroup.mem_comap, Subtype.forall]
  have hjw : ∀ a ∈ N i.1, jw n i.1 i.2 a ∈ Lev S N := by
    intro a ha
    refine (hmem _).2 fun k hk => ?_
    by_cases h : i = k
    · subst h
      rw [(hloc i.1 i.2).2.2.1]
      exact ha
    · rw [hind i k hi hk h a]
      exact one_mem _
  have hopen := (hG i.1).1
  refine ⟨fun y hy => ?_, fun k hk hik g hg => ?_⟩
  · have hy' := (GlobalTheory.TwTrLevel.mem_fixed_iff _ _ y).1 hy
    have h1 : y ∈ fixed (rw' n i.1 i.2) (N i.1) :=
      (GlobalTheory.TwTrLevel.mem_fixed_iff _ _ y).2 fun a ha => hy' _ (hjw a ha)
    refine ⟨h1, (GlobalTheory.TwTrLevel.mem_fixed_iff _ _ _).2 fun c hc => ?_⟩
    have ha : qw n i.1 i.2 c ∈ N i.1 := (hmem c).1 hc i hi
    obtain ⟨c', hcc⟩ : ∃ c', c' = (jw n i.1 i.2 (qw n i.1 i.2 c))⁻¹ * c := ⟨_, rfl⟩
    have hc' : c' ∈ Lev S N := hcc ▸ mul_mem (inv_mem (hjw _ ha)) hc
    have hq : qw n i.1 i.2 c' = 1 := by
      rw [hcc, map_mul, map_inv, (hloc i.1 i.2).2.2.1, inv_mul_cancel]
    have hc2 : c = jw n i.1 i.2 (qw n i.1 i.2 c) * c' := by
      rw [hcc, mul_inv_cancel_left]
    have hL : Commute (finRep E n c') (Lw N i.1 i.2 f) :=
      lv_commute (rw' n i.1 i.2) (N i.1) hopen f hf.1 _ fun a =>
        (((hloc i.1 i.2).2.2.2 a c' hq).map (finRep E n)).symm
    have hfix : Lw N i.1 i.2 f y ∈ fixed (rw' n i.1 i.2) (N i.1) :=
      GlobalTheory.TwTrLevel.levOp_mem_fixed (rw' n i.1 i.2) (MonoidHom.id _) (fun _ => rfl) LinearMap.id
        (fun _ => rfl) (N i.1) (N i.1) hopen (fun _ h => h) f hf y h1
    have e : finRep E n c' (Lw N i.1 i.2 f y) = Lw N i.1 i.2 f y := by
      have h2 := LinearMap.congr_fun hL.eq y
      rw [Module.End.mul_apply, Module.End.mul_apply, hy' c' hc'] at h2
      exact h2
    have h3 := (GlobalTheory.TwTrLevel.mem_fixed_iff _ _ _).1 hfix _ ha
    rw [hc2, map_mul, Module.End.mul_apply, e]
    exact h3
  · have hrr : ∀ a b, Commute (rw' n i.1 i.2 a) (rw' n k.1 k.2 b) := fun a b =>
      (((hloc k.1 k.2).2.2.2 b (jw n i.1 i.2 a) (hind i k hi hk hik a)).map (finRep E n)).symm
    exact lv_commute (rw' n k.1 k.2) (N k.1) (hG k.1).1 g hg.1 _ fun b =>
      (lv_commute (rw' n i.1 i.2) (N i.1) hopen f hf.1 _ fun a => (hrr a b).symm).symm
end

