module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.CoverEx
section
open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.coverEx :
    CoverEx := by
  classical
  intro Γ V S _ _ _ _ d G hP A O hAO hA hO
  obtain ⟨W, hW⟩ := UpperTheory.V.Lit.Dr.window Γ V S d G hP
  obtain ⟨u, hu⟩ := UpperTheory.V.Lit.Dr.cutoff Γ V S d G W hW
  have hB : ∀ s j, ∃ B : Set V, IsOpen B ∧ Convex ℝ B ∧ B ⊆ A s ∧ (j ∈ A s → j ∈ B) := by
    intro s j
    by_cases hj : j ∈ A s
    · obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 (hAO s).1 j hj
      exact ⟨Metric.ball j r, Metric.isOpen_ball, convex_ball j r, hb, fun _ => Metric.mem_ball_self hr⟩
    · exact ⟨∅, isOpen_empty, convex_empty, Set.empty_subset _, fun h => absurd h hj⟩
  choose B hBo hBc hBA hBm using hB
  have hψ := fun s => partBase V G.Y G.isOpen (fun j => if j ∈ O s then O s else B s j)
    (fun j => by
      by_cases hj : j ∈ O s
      · simpa [hj] using (hAO s).2.2.1
      · simpa [hj] using hBo s j)
    (fun p hp => by
      by_cases hj : p ∈ O s
      · simp [hj]
      · simpa [hj] using hBm s p (((hAO s).2.2.2 hp).resolve_right hj))
  choose ψ h1 h2 h3 h4 using hψ
  have hsub : ∀ (i : Idx Γ V) s, G.ρ i.g⁻¹ ⁻¹' B (G.σ i.g⁻¹ s) i.j ⊆ A s := by
    intro i s p hp
    exact (hA i.g⁻¹ s p).1 (hBA _ _ hp)
  refine ⟨fun i s => G.ρ i.g⁻¹ ⁻¹' B (G.σ i.g⁻¹ s) i.j, _, ⟨?_, ?_, ?_, ?_⟩,
    partProd Γ V S V d G u hu ψ h1 h2 h3, hsub, ?_⟩
  · intro i s
    exact (hBo _ _).preimage (G.ρ _).continuous
  · intro i s
    exact (hBc _ _).linear_preimage (G.ρ i.g⁻¹).toLinearMap
  · intro i s
    exact (hsub i s).trans (hAO s).2.1
  · intro γ i s p
    have e1 : G.ρ (γ * i.g)⁻¹ (G.ρ γ p) = G.ρ i.g⁻¹ p := by
      rw [mul_inv_rev, map_mul, ContinuousLinearMap.mul_apply, G.ρ_inv_apply]
    have e2 : G.σ (γ * i.g)⁻¹ (G.σ γ s) = G.σ i.g⁻¹ s := by
      rw [mul_inv_rev, map_mul, Equiv.Perm.mul_apply]; simp
    simp only [Set.mem_preimage, Idx.smul_g, Idx.smul_j, e1, e2]
  · intro i s p hp hne
    have h5 := h4 _ _ _ (right_ne_zero_of_mul hne)
    have h6 : G.ρ i.g⁻¹ p ∉ O (G.σ i.g⁻¹ s) := fun h => hp ((hO i.g⁻¹ s p).1 h)
    by_cases hj : i.j ∈ O (G.σ i.g⁻¹ s)
    · rw [if_pos hj] at h5
      exact absurd h5 h6
    · rw [if_neg hj] at h5
      exact h5
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.PartOp
section
noncomputable section

open UpperTheory.V.Lit UpperTheory.V.Lit.Dr

namespace UpperTheory.V.Cj.A

section

variable {Γ V S I : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] [MulAction Γ I] {d : ℕ}
  {G : Dr.Geo Γ V S d} {φ : I → S → V → ℝ}

private theorem part_fin_φ (hφ : IsPart G φ) (s : S) {p : V} (hp : p ∈ G.Y) :
    (Function.support fun i : I => φ i s p).Finite := by
  obtain ⟨N, hN, hf⟩ := hφ.locFin s p hp
  exact hf.subset fun i hi => ⟨p, mem_of_mem_nhds hN, hi⟩

private theorem part_fin (hφ : IsPart G φ) {q : ℕ} (c : I → G.Om q) (s : S) (p : V) :
    (Function.support fun i : I => φ i s p • (c i).1 s p).Finite := by
  by_cases hp : p ∈ G.Y
  · refine (part_fin_φ hφ s hp).subset fun i hi h0 => hi ?_
    beta_reduce at h0 ⊢
    rw [h0, zero_smul]
  · refine Set.finite_empty.subset fun i hi => hi ?_
    beta_reduce
    rw [((c i).2 s).2 p hp, smul_zero]

private theorem part_shift (hφ : IsPart G φ) (γ : Γ) (i : I) (s : S) (p : V) :
    φ (γ • i) s p = φ i (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) := by
  have h := hφ.equiv γ⁻¹ (γ • i) s p
  rw [inv_smul_smul] at h
  exact h.symm

end

theorem partOp : PartOp := by
  intro Γ V S I _ _ _ _ d G φ hφ q
  refine ⟨{ toFun := fun c => ⟨_, partMem Γ V S I d G φ hφ q c⟩, map_add' := ?_, map_smul' := ?_ }, ?_, ?_, ?_⟩
  · intro c c'
    refine Subtype.ext (funext fun s => funext fun p => ?_)
    simp only [Pi.add_apply, Submodule.coe_add, smul_add]
    exact finsum_add_distrib (part_fin hφ c s p) (part_fin hφ c' s p)
  · intro a c
    refine Subtype.ext (funext fun s => funext fun p => ?_)
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply]
    rw [smul_finsum' a (part_fin hφ c s p)]
    exact finsum_congr fun i => smul_comm _ _ _
  · intro x
    refine Subtype.ext (funext fun s => funext fun p => ?_)
    change ∑ᶠ i : I, φ i s p • x.1 s p = x.1 s p
    by_cases hp : p ∈ G.Y
    · rw [← finsum_smul' (part_fin_φ hφ s hp), hφ.sum_one s p hp, one_smul]
    · simp [(x.2 s).2 p hp]
  · intro γ c
    refine Subtype.ext (funext fun s => funext fun p => Eq.symm ?_)
    change G.tr q γ (∑ᶠ i : I, φ i (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (c i).1 (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) =
      ∑ᶠ i : I, φ i s p • G.tr q γ ((c (γ⁻¹ • i)).1 (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))
    rw [map_finsum (G.tr q γ) (part_fin hφ c _ _)]
    refine Eq.trans ?_ (finsum_comp_equiv (MulAction.toPerm γ))
    refine finsum_congr fun i => ?_
    rw [MulAction.toPerm_apply, inv_smul_smul, part_shift hφ, map_smul]
  · intro c s p h
    change ∑ᶠ i : I, φ i s p • (c i).1 s p = 0
    refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
    by_cases h0 : φ i s p = 0
    · rw [h0, zero_smul]
    · rw [h i h0, smul_zero]

end UpperTheory.V.Cj.A
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.RelPrim
section
open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.relPrim :
    RelPrim := by
  intro Γ V S _ _ _ _ d G hc C hC q w hw hv
  have h0 : ∀ s, ∀ p ∈ G.Y, extDeriv (w.1 s) p = 0 := fun s p hp => by
    rw [← G.dOm_apply w s hp, hw]; rfl
  choose η hη hd hz using fun s =>
    relPoin V (Fin d → ℂ) G.Y (C s) G.isOpen hc (hC s).1 (hC s).2 q (w.1 s) (w.2 s).1 (h0 s) (hv s)
  refine ⟨⟨fun s => G.Y.indicator (η s), fun s =>
    ⟨(hη s).congr fun p hp => Set.indicator_of_mem hp _,
      fun p hp => Set.indicator_of_notMem hp _⟩⟩, ?_, ?_⟩
  · refine Subtype.ext (funext fun s => funext fun p => ?_)
    by_cases hp : p ∈ G.Y
    · rw [G.dOm_apply _ s hp, ← hd s p hp]
      refine Filter.EventuallyEq.extDeriv_eq ?_
      filter_upwards [G.isOpen.mem_nhds hp] with x hx using Set.indicator_of_mem hx _
    · rw [((G.dOm q _).2 s).2 p hp, (w.2 s).2 p hp]
  · intro s p hp
    exact (Set.indicator_of_mem ((hC s).2 hp) _).trans (hz s p hp)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SatClosed
section
open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.satClosed :
    SatClosed := by
  intro Γ V S _ _ _ _ d G hP hC l hl T K hT hK hKY s
  have hcont : ∀ s', ContinuousOn (fun p : V => l s' p • p) G.Y := fun s' =>
    (hl.1 s').1.continuousOn.smul continuousOn_id
  have hmem : ∀ s', ∀ p ∈ G.Y, l s' p • p ∈ G.Y := fun s' p hp =>
    hC _ ((hl.1 s').2.1 p hp) p hp
  have horb : ∀ s', IsOpen (G.Y \ {p | ∃ γ : Γ, G.σ γ s = s' ∧ G.ρ γ p ∈ (fun p : V => l s' p • p) '' K}) := fun s' =>
    orbClosed Γ V S d G hP _ (by rintro _ ⟨k, hk, rfl⟩; exact hmem s' k (hKY hk))
      (hK.image_of_continuousOn ((hcont s').mono hKY)) s s'
  have hopen := (hcont s).isOpen_inter_preimage G.isOpen (hT.isOpen_biInter fun s' _ => horb s')
  convert hopen using 1
  ext p
  simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_setOf_eq]
  refine and_congr_right fun hp => ⟨fun h s' hs' => ⟨hmem s p hp, ?_⟩, fun h => ?_⟩
  · rintro ⟨γ, rfl, k, hk, hk'⟩
    have h1 := (hl.1 (G.σ γ s)).2.1 k (hKY hk)
    have h2 := (hl.1 s).2.1 p hp
    refine h ⟨γ, (l (G.σ γ s) k)⁻¹ * l s p, mul_pos (inv_pos.2 h1) h2, hs', ?_⟩
    have h3 : l (G.σ γ s) k • k = l s p • G.ρ γ p := by rw [← map_smul]; exact hk'
    rw [mul_smul, ← h3, inv_smul_smul₀ h1.ne']
    exact hk
  · rintro ⟨γ, t, ht, hs', hk⟩
    refine (h _ hs').2 ⟨γ, rfl, _, hk, ?_⟩
    show l (G.σ γ s) (t • G.ρ γ p) • t • G.ρ γ p = _
    rw [(hl.1 _).2.2 t ht _ (G.maps γ p hp), hl.2 γ s p hp, map_smul, smul_smul]
    congr 1
    field_simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SuppBwd
section
open UpperTheory.V.Cj.A
open Matrix NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

private theorem cont_inf (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

private theorem cont_fin (E : Type) [Field E] [NumberField E] (a : ℕ) :
    Continuous (finGL E a) := by
  have hs : Continuous (sFin E : Af E → Ad E) := continuous_const.prodMk continuous_id
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

private theorem mem_out {G : Type} [Group G] (U : Subgroup G) (y : G) :
    y ∈ (fun u => Quotient.out (y : G ⧸ U) * u) '' (U : Set G) :=
  ⟨(Quotient.out (y : G ⧸ U))⁻¹ * y, QuotientGroup.eq.1 (QuotientGroup.out_eq' _), mul_inv_cancel_left _ _⟩

theorem UpperTheory.V.Cj.A.suppBwd :
    SuppBwd := by
  intro E _ _ _ a ho U hU Ξ q α w h ⟨T, K, hT, hK, hKY, hw⟩
  obtain ⟨-, hq2, hq3, -⟩ := qhtFacts E a
  have hC := (sandCpt E a).2 K hKY hK
  have hD : IsCompact (⋃ s ∈ T, (fun u => Quotient.out s * u) '' (U : Set (GL (Fin a) (Af E)))) :=
    hT.isCompact_biUnion fun s _ => hU.image (continuous_const.mul continuous_id)
  obtain ⟨B, hB⟩ := hq3 _ ((hC.prod hD).image
    (((cont_inf E a).comp continuous_fst).mul ((cont_fin E a).comp continuous_snd)))
  refine ⟨B * qht (1 : GA E a), fun X g hg => ?_⟩
  have h0 : w (GeneralLinearGroup.map (pFin E) g : GL (Fin a) (Af E) ⧸ U)
      (sand (GeneralLinearGroup.map (pInf E) g) (hOne E a)) = 0 := by
    refine hw _ _ ⟨_, rfl⟩ ?_
    rintro ⟨γ, r, hr, hσ, hρ⟩
    obtain ⟨t, ht⟩ := (splitFacts E a).2 r hr
    have h1 := ((splitFacts E a).1 t).1
    refine absurd (hB 1 (ratGL E a γ.1 * GlobalTheory.UnitaryBC.splitCentre E a t * g) ?_) ?_
    · refine ⟨(GeneralLinearGroup.map (pInf E) (ratGL E a γ.1 * GlobalTheory.UnitaryBC.splitCentre E a t * g),
        GeneralLinearGroup.map (pFin E) (ratGL E a γ.1 * GlobalTheory.UnitaryBC.splitCentre E a t * g)), ⟨?_, ?_⟩,
        infGL_mul_finGL _⟩
      · rw [geo_ρ, ← map_smul, ← ht] at hρ
        simp only [Set.mem_setOf_eq, map_mul, ContinuousLinearMap.mul_apply]
        exact hρ
      · simp only [map_mul, h1, mul_one]
        refine Set.mem_biUnion hσ ?_
        have e : (geo ho U Ξ).σ γ (GeneralLinearGroup.map (pFin E) g : GL (Fin a) (Af E) ⧸ U) =
            ((GeneralLinearGroup.map (pFin E) (ratGL E a γ.1) * GeneralLinearGroup.map (pFin E) g :
              GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) := rfl
        rw [e]
        exact mem_out U _
    · rw [one_mul, hq2]
      exact not_le.2 hg
  have h2 := h (GeneralLinearGroup.map (pInf E) g) (GeneralLinearGroup.map (pFin E) g) X
  rw [h0, infGL_mul_finGL] at h2
  have h3 := congrArg (fun y => Ξ.mat (GeneralLinearGroup.map (pInf E) g)⁻¹ *ᵥ y) h2
  simp only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply, Matrix.mulVec_zero] at h3
  exact h3.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SuppFwd
section
open UpperTheory.V.Cj.A
open Matrix NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Cj.A.suppFwd :
    SuppFwd := by
  intro E _ _ _ a ho U hU Ξ q α w h hα
  obtain ⟨R, hR⟩ := hα
  obtain ⟨C, hC, hC'⟩ := (qhtFacts E a).2.2.2 R
  have h1 : Continuous (pInf E) := continuous_pi fun v =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex v)).continuous.comp
      ((continuous_apply v).comp continuous_fst)
  have h2 : Continuous (pFin E) := continuous_snd
  have hi : Continuous fun g : GA E a => GeneralLinearGroup.map (pInf E) g :=
    Continuous.units_map _ (continuous_id.matrix_map h1)
  have hf : Continuous fun g : GA E a => GeneralLinearGroup.map (pFin E) g :=
    Continuous.units_map _ (continuous_id.matrix_map h2)
  haveI : DiscreteTopology (GL (Fin a) (Af E) ⧸ U) := QuotientGroup.discreteTopology hU
  refine ⟨(fun g : GA E a => ((GeneralLinearGroup.map (pFin E) g : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U)) '' C,
    (fun g : GA E a => sand (GeneralLinearGroup.map (pInf E) g) (hOne E a)) '' C,
    (hC.image (QuotientGroup.continuous_mk.comp hf)).finite_of_discrete,
    hC.image ((sandCpt E a).1.comp hi), ?_, ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact ⟨_, rfl⟩
  · rintro s _ ⟨g, rfl⟩ hp
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    have hlt : R < qht (infGL E a g * finGL E a x) := by
      by_contra hle
      obtain ⟨γ, t, hm⟩ := hC' _ (not_lt.1 hle)
      obtain ⟨e1, r, hr, e2⟩ := (splitFacts E a).1 t
      refine hp ⟨⟨γ, Subgroup.mem_top γ⟩, r, hr, ⟨_, hm, ?_⟩, ⟨_, hm, ?_⟩⟩
      · simp only [map_mul, e1, pFin_infGL, pFin_finGL, one_mul, mul_one]
        rfl
      · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one, ContinuousLinearMap.mul_apply, e2, map_smul, geo_ρ]
    refine ContinuousAlternatingMap.ext fun v => ?_
    have hv' : v = fun i => (2 : ℝ) • sand g (hv (hv.symm ((2 : ℝ)⁻¹ • sand g⁻¹ (v i)))) := by
      funext i
      rw [LinearEquiv.apply_symm_apply, map_smul, smul_smul, ← ContinuousLinearMap.mul_apply, ← map_mul,
        mul_inv_cancel, map_one]
      simp
    rw [hv', h, hR _ _ hlt, Matrix.mulVec_zero]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.ZigFormal
section
open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.zigFormal :
    ZigFormal := by
  intro Γ V S I _ _ _ _ d G
  refine ⟨fun q k u u' c h hz => ?_, fun ι hι q => ?_⟩
  · cases q with
    | zero => exact fun x hx => (h x hx).symm.trans (hz x hx)
    | succ q =>
      obtain ⟨b, hb, hdb, hz⟩ := hz
      exact ⟨b, hb, fun x hx => (hdb x hx).trans (h x hx), hz⟩
  · induction q with
    | zero => exact fun k u c hz x hx => hz (x.map ι) (by rw [List.length_map, hx])
    | succ q ih =>
      rintro k u c ⟨b, hb, hdb, hz⟩
      refine ⟨fun x => b (x.map ι), fun γ x hx => ?_, fun x hx => hdb (x.map ι) (by rw [List.length_map, hx]), ?_⟩
      · have h := hb γ (x.map ι) (by rw [List.length_map, hx])
        refine Eq.trans ?_ h
        simp only [List.map_map]
        congr 2
        funext δ
        exact hι γ δ
      · have h := ih (k + 1) _ c hz
        have e : (fun x : List Γ => UpperTheory.V.Lit.Geo.hd b (x.map ι)) = UpperTheory.V.Lit.Geo.hd (fun x : List Γ => b (x.map ι)) :=
          funext fun x => (hdFacts.2.2.1 I Γ _ ι b x).symm
        rw [e] at h
        exact h
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.ZigMap
section
open UpperTheory.V.Cj.A UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Cj.A.zigMap :
    ZigMap := by
  intro Γ V S _ _ _ d G P hd' hi ha q
  induction q with
  | zero =>
    intro k u c h x hx
    show P 0 (u x) = G.incl (c x)
    rw [h x hx, hi]
  | succ q ih =>
    rintro k u c ⟨b, hb, hdb, hz⟩
    refine ⟨fun x => P q (b x), fun γ x hx => ?_, fun x hx => ?_, ?_⟩
    · show P q (b (x.map (γ * ·))) = G.act q γ (P q (b x))
      rw [hb γ x hx, ha]
    · show G.dOm q (P q (b x)) = P (q + 1) (u x)
      rw [hd', hdb x hx]
    · have e : hd (fun x => P q (b x)) = fun x => P q (hd b x) :=
        funext fun x => hdFacts.2.2.2.1 Γ _ _ (P q).toAddMonoidHom b x
      rw [e]
      exact ih (k + 1) (hd b) c hz
end

