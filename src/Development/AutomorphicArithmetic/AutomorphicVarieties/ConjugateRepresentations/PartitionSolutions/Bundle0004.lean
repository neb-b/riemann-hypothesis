module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartHOfSs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DeRhamInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.AbsTransOf
section
noncomputable section

open Matrix NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo
open scoped ContDiff

namespace UpperTheory.V.Cj.A

theorem absTrans_of (h1 : HdFacts) (h2 : ZigFwd) (h3 : ZigBwd) (h4 : BwdLast) (h5 : ZigFormal) (h6 : PullOp) (h7 : PullAct)
    (h8 : ZigMap) (h9 : CoverEx) (h10 : SatClosed) (h11 : SatFacts) : AbsTrans := by
  intro Γ V S _ _ _ _ d d' G ξ' τ hτ hc hn hcone hp ⟨l, hl⟩ q w hw hdw ⟨T, K, hT, hK, hKY, hz⟩
  obtain ⟨K1, hK1, hKK, hK1Y⟩ := exists_compact_between hK G.isOpen hKY
  obtain ⟨s1, -, s3, -⟩ := h11 Γ V S d G T K
  obtain ⟨o1, o2, o3, -⟩ := h11 Γ V S d G T (interior K1)
  obtain ⟨-, -, -, f4⟩ := h11 Γ V S d G T K1
  obtain ⟨C, φ, hC, hφ, hCA, hCO⟩ := h9 Γ V S d G hp (fun s => G.Y \ sat G T K s) (sat G T (interior K1))
    (fun s => ⟨h10 Γ V S d G hp hcone l hl T K hT hK hKY s, Set.diff_subset, o2 isOpen_interior s, fun p hp' => by
      by_cases h : p ∈ sat G T K s
      · exact Or.inr (s3 _ hKK s h)
      · exact Or.inl ⟨hp', h⟩⟩)
    (fun γ s p => by simp only [Set.mem_diff, G.ρ_mem_iff, s1 γ s p]) o1
  obtain ⟨c, z1, z2, z3, z4⟩ := h2 Γ V S (Idx Γ V) d G hc hn Idx.g (fun _ _ => rfl) C hC q 0 q (zero_add q) (fun _ => w)
    (fun γ _ _ => (hw γ).symm) (fun _ _ => hdw) (fun x hx => by simp [hd, hx, Finset.sum_range_succ])
    (fun x hx s p _ h => by
      obtain ⟨i, rfl⟩ := List.length_eq_one_iff.1 hx
      have := hCA i s (h i (by simp))
      exact hz s p this.1 this.2)
  let G' := chg G ξ'
  let f : (S → Fin d → ℂ) →+ (S → Fin d' → ℂ) := τ.compLeft S
  have hC' : IsCvx G' C := ⟨hC.1, hC.2, hC.3, hC.4⟩
  have hφ' : IsPart G' φ := ⟨hφ.1, hφ.2, hφ.3, hφ.4⟩
  have hF : ∀ i s, ∀ p ∈ G.Y \ sat G T K1 s, φ i s p ≠ 0 → p ∈ C i s := fun i s p hp' h =>
    hCO i s p (fun h' => hp'.2 (o3 _ interior_subset s h')) h
  obtain ⟨u, u1, u2, u3, u4, u5⟩ := h3 Γ V S (Idx Γ V) d' G' hc hn φ hφ' C (fun s => G.Y \ sat G T K1 s) hC'
    (h10 Γ V S d G hp hcone l hl T K1 hT hK1 hK1Y) hF q (fun x => f (c x))
    (fun γ x hx => by
      beta_reduce
      rw [z2 γ x hx]
      exact funext fun s => hτ γ _)
    (fun x hx => by rw [h1.2.2.2.1 _ _ _ f c x, z3 x hx, map_zero])
    (fun x hx s p h => by
      change τ (c x s) = 0
      rw [z4 x hx s p h, map_zero]) q 0 (zero_add q)
  obtain ⟨w', w1, w2, w3⟩ := h4 Γ V S (Idx Γ V) d' G' φ hφ' C _ hF q u u2 u4 u5
  have hl' : G'.IsInvGauge l := hl
  obtain ⟨P, p1, p2, p3⟩ := h6 Γ V S d' G' hcone l hl'
  have p4 := fun k => h7 Γ V S d' G' hcone l hl' k (P k) (p1 k)
  have hι : ∀ γ δ : Γ, (⟨γ * δ, 0⟩ : Idx Γ V) = γ • (⟨δ, 0⟩ : Idx Γ V) := fun _ _ => rfl
  have y1 := (h5 Γ V S (Idx Γ V) d G).2 (fun γ => ⟨γ, 0⟩) hι q 0 _ _ z1
  have y2 := (h5 Γ V S (Idx Γ V) d' G').2 (fun γ => ⟨γ, 0⟩) hι q 0 _ _ ((h5 Γ V S (Idx Γ V) d' G').1 q 0 u (fun _ => w') _ w2 u1)
  refine ⟨_, P q w', y1, h8 Γ V S d' G' P p2 p3 p4 q 0 _ _ y2, fun γ => by rw [p4, w1], ?_, fun s p hp' v i hv => ?_,
    T, K1, hT, hK1, hK1Y, fun s p hp' h => ?_⟩
  · rw [p2, ← w2 [⟨1, 0⟩] rfl, u3 _ rfl, map_zero]
  · rw [p1 q w' s p hp']
    exact (pullA V _ G.Y G.isOpen hcone (l s) (hl.1 s) q _).1 p hp' v i hv
  · have h0 := (hl.1 s).2.1 p hp'
    rw [p1 q w' s p hp', pull, w3 s _ ⟨hcone _ h0 p hp', fun h' => h ((f4 s p _ h0).1 h')⟩]
    rfl

theorem partA_of (h1 : AbsTrans) (h2 : SuppFwd) (h3 : SuppBwd) (h4 : LevCorr) : PartA := by
  intro E _ _ _ a ha U hUo hU σ Ξ Ξ' h hσ q α hα hd0 hs
  have ho : IsOpen (cone E a) := isOpen_iff_mem_nhds.2 fun p hp => by
    obtain ⟨τ, -, hτ⟩ := locSec E a p hp
    exact hτ.mono fun x hx => ⟨τ x, hx⟩
  obtain ⟨w, w1, w2, w3⟩ := (h4 E a ho U Ξ q).1 α hα hd0
  let τ : (Fin Ξ.d → ℂ) →+ (Fin Ξ'.d → ℂ) := AddMonoidHom.mk' (fun v i => σ (v (Fin.cast h.symm i))) fun v v' => by
    ext i
    simp
  have hτ : ∀ γ v, τ ((geo ho U Ξ).ξ γ *ᵥ v) = (geo ho U Ξ').ξ γ *ᵥ τ v := fun γ v => by
    ext i
    change σ (∑ j, ratC Ξ γ.1 (Fin.cast h.symm i) j * v j) = ∑ j, ratC Ξ' γ.1 i j * σ (v (Fin.cast h.symm j))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← (finCongr h).sum_comp]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← hσ]
    rfl
  obtain ⟨c, w', z1, z2, z3, z4, z5, z6⟩ := h1 _ _ _ _ _ (geo ho U Ξ) (geo ho U Ξ').ξ τ hτ (coneConvex E a).1
    ⟨_, hOne_mem_cone⟩ (coneConvex E a).2 (geoProper E a ho U Ξ hU) (Dr.gauge E a ha ho U Ξ hU) q w w2 w3
    (h2 E a ho U hUo Ξ q α _ w1 hs)
  obtain ⟨β, b1, b2, b3⟩ := (h4 E a ho U Ξ' q).2 w' z3 z4 z5
  refine ⟨U, le_rfl, hUo, hU, β, b3, h3 E a ho U hU Ξ' q β _ b1 z6, hα, b2, c, sigC σ h c, ⟨ho, w, w1, z1⟩,
    ⟨ho, w', b1, z2⟩, ?_⟩
  rw [sub_self]
  cases q with
  | zero => exact fun _ _ => rfl
  | succ q => exact ⟨0, fun _ _ _ => by simp, fun x _ => by simp [hd]⟩

end UpperTheory.V.Cj.A
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.BwdLast
section
open UpperTheory.V.Cj.A UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Cj.A.bwdLast :
    BwdLast := by
  intro Γ V S I _ _ _ _ d G φ hφ C F hC q u hu hhd hvan
  obtain ⟨P, hP1, hPeq, hPvan⟩ := partOp Γ V S I d G φ hφ q
  have hconst : ∀ i j : I, u [i] = u [j] := by
    intro i j
    have h := hhd [i, j] rfl
    simp [UpperTheory.V.Lit.Geo.hd, Finset.sum_range_succ] at h
    have h' : u [j] - u [i] = 0 := by
      rw [sub_eq_add_neg]
      simpa using h
    exact (sub_eq_zero.mp h').symm
  refine ⟨P (fun i => u [i]), ?_, ?_, ?_⟩
  · intro γ
    have hinv : (fun i => (G.act q) γ (u [γ⁻¹ • i])) = fun i => u [i] := by
      funext i
      have h := hu γ [γ⁻¹ • i] rfl
      simp only [List.map_cons, List.map_nil, smul_inv_smul] at h
      exact h.symm
    rw [← hPeq γ (fun i => u [i]), hinv]
  · intro x hx
    match x, hx with
    | [i], _ =>
      have hfun : (fun j => u [j]) = fun _ => u [i] := by
        funext j
        exact hconst j i
      rw [hfun, hP1]
  · intro s p hp
    apply hPvan
    intro i hne
    refine hvan [i] rfl s p hp ?_
    intro i' hi'
    rw [List.mem_singleton] at hi'
    rw [hi']
    exact hC i s p hp hne
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.BwdStep
section
open UpperTheory.V.Cj.A UpperTheory.V.Lit.Geo

private theorem contDiffOn_finsum_locally_finite_smul {V A I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup A]
    [NormedSpace ℝ A] (Y : Set V) (φ : I → V → ℝ) (w : I → V → A)
    (hφ : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ i) Y)
    (hw : ∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (w i) Y)
    (hfin : ∀ p ∈ Y, ∃ N ∈ nhds p, {i | ∃ x ∈ N, φ i x ≠ 0}.Finite) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => ∑ᶠ i, φ i p • w i p) Y := by
  apply contDiffOn_of_locally_contDiffOn
  intro p hp
  obtain ⟨N, hN, hNf⟩ := hfin p hp
  obtain ⟨U, hUN, hUo, hpU⟩ := mem_nhds_iff.mp hN
  refine ⟨U, hUo, hpU, ?_⟩
  have hsum : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => ∑ i ∈ hNf.toFinset, φ i p • w i p) (Y ∩ U) :=
    ContDiffOn.sum (fun i _ => ((hφ i).smul (hw i)).mono Set.inter_subset_left)
  refine hsum.congr ?_
  intro y hy
  apply finsum_eq_sum_of_support_subset
  intro i hi
  rw [Set.Finite.coe_toFinset]
  refine ⟨y, hUN hy.2, ?_⟩
  intro h0
  apply hi
  simp [h0]

theorem UpperTheory.V.Cj.A.bwdStep :
    BwdStep := by
  intro Γ V S I _ _ _ _ d G φ hφ C F hC q k u hu hhd hvan
  have hfinY : ∀ s, ∀ p ∈ G.Y, {i | φ i s p ≠ 0}.Finite := by
    intro s p hp
    obtain ⟨N, hN, hf⟩ := hφ.locFin s p hp
    exact hf.subset (fun i hi => ⟨p, mem_of_mem_nhds hN, hi⟩)
  have hsupp : ∀ (c : I → ↥(G.Om q)) (s : S) (p : V), Function.HasFiniteSupport
      (fun i => φ i s p • ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p) := by
    intro c s p
    by_cases hp : p ∈ G.Y
    · refine (hfinY s p hp).subset ?_
      intro i hi h0
      apply hi
      simp [h0]
    · have hz : (fun i => φ i s p • ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p) = 0 := by
        funext i
        rw [((c i).2 s).2 p hp, smul_zero]
        rfl
      rw [hz]
      exact Set.finite_empty.subset (fun i hi => hi rfl)
  have hex : ∀ c : I → ↥(G.Om q), ∃ w : ↥(G.Om q), ∀ s p,
      (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p
        = ∑ᶠ i, φ i s p • ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p := by
    intro c
    refine ⟨⟨fun s p => ∑ᶠ i, φ i s p • ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p, ?_⟩,
      fun s p => rfl⟩
    intro s
    refine ⟨contDiffOn_finsum_locally_finite_smul G.Y (fun i => φ i s)
      (fun i => ((c i : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)
      (fun i => hφ.smooth i s) (fun i => ((c i).2 s).1) (hφ.locFin s), ?_⟩
    intro p hp
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    rw [((c i).2 s).2 p hp, smul_zero]
  choose Sm hSm using hex
  refine ⟨fun x => Sm (fun i => u (i :: x)), ?_, ?_, ?_⟩
  · intro γ x hx
    have hσ : ∀ t, G.σ γ (G.σ γ⁻¹ t) = t := by
      intro t
      rw [← Equiv.Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one, Equiv.Perm.one_apply]
    have hρ : ∀ v, G.ρ γ (G.ρ γ⁻¹ v) = v := by
      intro v
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]
    apply Subtype.ext
    funext s p
    show _ = G.tr q γ (((Sm fun i => u (i :: x)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))
    rw [hSm, hSm, map_finsum (G.tr q γ) (hsupp _ _ _)]
    conv_lhs => rw [← finsum_comp_equiv (MulAction.toPerm γ : I ≃ I)]
    apply finsum_congr
    intro j
    simp only [MulAction.toPerm_apply]
    have h1 : u (γ • j :: List.map (fun x => γ • x) x) = G.act q γ (u (j :: x)) :=
      hu γ (j :: x) (by simp [hx])
    have h2 : φ (γ • j) s p = φ j (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) := by
      rw [← hφ.equiv γ j (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p), hσ, hρ]
    rw [h1, map_smul, h2]
    rfl
  · intro x hx
    apply Subtype.ext
    funext s p
    let ev : ↥(G.Om q) →+ V [⋀^Fin q]→L[ℝ] (Fin d → ℂ) :=
      { toFun := fun w => (w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p, map_zero' := rfl,
        map_add' := fun _ _ => rfl }
    change ev (hd (fun y => Sm fun i => u (i :: y)) x) = ev (u x)
    rw [← hdFacts.2.2.2.1 I _ _ ev (fun y => Sm fun i => u (i :: y)) x]
    have hinner : ∀ i, hd (fun y => ev (u (i :: y))) x = ev (u x) := by
      intro i
      have h2 := hdFacts.2.1 I _ u i x
      rw [hhd (i :: x) (by simp [hx]), eq_comm, sub_eq_zero] at h2
      calc hd (fun y => ev (u (i :: y))) x = ev (hd (fun y => u (i :: y)) x) :=
            hdFacts.2.2.2.1 I _ _ ev (fun y => u (i :: y)) x
        _ = ev (u x) := by rw [← h2]
    by_cases hp : p ∈ G.Y
    · have hrw : (fun y => ev (Sm fun i => u (i :: y)))
          = fun y => ∑ i ∈ (hfinY s p hp).toFinset, φ i s p • ev (u (i :: y)) := by
        funext y
        show ((Sm fun i => u (i :: y) : ↥(G.Om q)) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = _
        rw [hSm]
        apply finsum_eq_sum_of_support_subset
        intro i hi
        rw [Set.Finite.coe_toFinset]
        show φ i s p ≠ 0
        intro h0
        apply hi
        simp [h0]
      rw [hrw]
      have hsplit : hd (fun y => ∑ i ∈ (hfinY s p hp).toFinset, φ i s p • ev (u (i :: y))) x
          = ∑ i ∈ (hfinY s p hp).toFinset, φ i s p • hd (fun y => ev (u (i :: y))) x := by
        simp only [UpperTheory.V.Lit.Geo.hd, Finset.smul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_comm]
      rw [hsplit]
      simp only [hinner]
      rw [← Finset.sum_smul]
      have h1 : ∑ i ∈ (hfinY s p hp).toFinset, φ i s p = 1 := by
        rw [← hφ.sum_one s p hp]
        symm
        apply finsum_eq_sum_of_support_subset
        intro i hi
        rw [Set.Finite.coe_toFinset]
        exact hi
      rw [h1, one_smul]
    · have hz : ∀ w : ↥(G.Om q), ev w = 0 := fun w => (w.2 s).2 p hp
      simp only [hz]
      simp [UpperTheory.V.Lit.Geo.hd]
  · intro x hx s p hp hx'
    rw [hSm]
    apply finsum_eq_zero_of_forall_eq_zero
    intro i
    by_cases h0 : φ i s p = 0
    · rw [h0, zero_smul]
    · have hall : ∀ i' ∈ i :: x, p ∈ C i' s := by
        intro i' hi'
        rcases List.mem_cons.mp hi' with h | h
        · rw [h]
          exact hC i s p hp h0
        · exact hx' i' h
      rw [hvan (i :: x) (by simp [hx]) s p hp hall, smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.FwdStep
section
open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.fwdStep :
    FwdStep := by
  intro Γ V S I _ _ _ _ _ d G hY r hr C hC q k u hu hcl hvan
  classical
  have hex : ∀ y : List I, y.length = k + 1 → ∃ η : G.Om q, G.dOm q η = u y ∧
      ∀ s, ∀ p ∈ {p | ∀ i ∈ y, p ∈ C i s}, (η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0 := by
    intro y hy
    obtain ⟨i0, t, rfl⟩ : ∃ i t, y = i :: t := by
      cases y with
      | nil => simp at hy
      | cons i t => exact ⟨i, t, rfl⟩
    refine relPrim Γ V S d G hY (fun s => {p | ∀ i ∈ i0 :: t, p ∈ C i s}) (fun s => ⟨?_, ?_⟩) q
      (u (i0 :: t)) (hcl _ hy) ?_
    · intro a ha b hb t1 t2 h1 h2 h i hi
      exact hC.convex i s (ha i hi) (hb i hi) h1 h2 h
    · intro p hp
      exact hC.sub i0 s (hp i0 List.mem_cons_self)
    · intro s p hp
      exact hvan _ hy s p (Set.mem_univ _) hp
  choose η hη using hex
  have hηc : ∀ (y y' : List I) (h : y.length = k + 1) (h' : y'.length = k + 1), y = y' → η y h = η y' h' := by
    rintro y _ h h' rfl
    rfl
  let g : List I → Γ := fun x => (x.head?.map r).getD 1
  have hg : ∀ (γ : Γ) (x : List I), x ≠ [] → g (x.map (γ • ·)) = γ * g x := by
    intro γ x hx
    cases x with
    | nil => exact absurd rfl hx
    | cons i t => simp [g, hr]
  have hlen : ∀ x : List I, (x.map ((g x)⁻¹ • ·)).length = x.length := fun x => List.length_map ..
  refine ⟨fun x => if h : x.length = k + 1 then
      G.act q (g x) (η (x.map ((g x)⁻¹ • ·)) ((hlen x).trans h)) else 0, ?_, ?_, ?_⟩
  · intro γ x hx
    have hx' : (x.map (γ • ·)).length = k + 1 := by simpa using hx
    have hne : x ≠ [] := by
      rintro rfl
      simp at hx
    simp only [dif_pos hx, dif_pos hx']
    have hn : (x.map (γ • ·)).map ((g (x.map (γ • ·)))⁻¹ • ·) = x.map ((g x)⁻¹ • ·) := by
      rw [hg γ x hne, List.map_map]
      congr 1
      funext i
      simp [smul_smul]
    rw [hηc _ _ _ ((hlen x).trans hx) hn, hg γ x hne, map_mul]
    rfl
  · intro x hx
    simp only [dif_pos hx]
    rw [UpperTheory.V.Lit.Dr.dEquiv Γ V S d G q, (hη _ _).1, ← hu (g x) _ ((hlen x).trans hx)]
    congr 1
    simp [List.map_map, Function.comp_def, smul_smul]
  · intro x hx s p _ hp
    simp only [dif_pos hx]
    have hp' : G.ρ (g x)⁻¹ p ∈ {p | ∀ i ∈ x.map ((g x)⁻¹ • ·), p ∈ C i ((G.σ (g x)⁻¹) s)} := by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
      exact (hC.equiv _ j s p).2 (hp j hj)
    ext v
    rw [UpperTheory.V.Lit.Dr.Geo.act_apply, (hη _ _).2 _ _ hp']
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.LevCorr
section
open UpperTheory.V.Cj.A
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

private theorem dCo_zero' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (ho : IsOpen (cone E a))
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) (q : ℕ) (α : Co Ξ q) (w : (geo ho U Ξ).Om q)
    (hw : Corr U Ξ α w.1) (hd : (geo ho U Ξ).dOm q w = 0) : dCo (smLie Ξ) α = 0 := by
  have h := corrD E a ho U Ξ q _ _ hw
  rw [hd] at h
  exact (corrUniq E a ho U Ξ (q + 1)).1 _ 0 _ h (corr_zero U Ξ)

theorem UpperTheory.V.Cj.A.levCorr :
    LevCorr := by
  intro E _ _ _ a ho U Ξ q
  refine ⟨fun α hα hd => ?_, fun w hi hd hb => ?_⟩
  · have hv : ∀ X, LeftInv (α X) ∧ RightInv U (α X) := fun X => (levelVal E a U Ξ _).1 (hα.val X)
    obtain ⟨w, hw, h0⟩ := corrFwd E a U Ξ q α hα.equiv fun X => (hv X).2
    let w' : (geo ho U Ξ).Om q := ⟨w, fun s => ⟨corrSmooth E a U Ξ q _ w hw s, h0 s⟩⟩
    have hw' : Corr U Ξ α w'.1 := hw
    refine ⟨w', hw', (corrInv E a ho U Ξ q _ _ hw').1 fun X => (hv X).1, ?_⟩
    have h := corrD E a ho U Ξ q _ _ hw'
    rw [hd] at h
    exact (corrUniq E a ho U Ξ (q + 1)).2 0 _ 0 h (corr_zero U Ξ)
  · obtain ⟨η, hη⟩ := corrBwd E a ho U Ξ q w
    have e : dCo (smLie Ξ) η = 0 := dCo_zero' ho U Ξ q η w hη hd
    have b := (corrBasic E a U Ξ _ _ _ hη).2 hb
    obtain ⟨c1, c2⟩ := corrCochain E a U Ξ q _ _ hη
    exact ⟨η, hη, ⟨c1, b, fun X => (levelVal E a U Ξ _).2 ((corrInv E a ho U Ξ q _ _ hη).2 hi X) (c2 X)
      (centralOf E a _ (smLie Ξ) q η b (fun Y i _ => by rw [e]; rfl) X)⟩, e⟩
end

