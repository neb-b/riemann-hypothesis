module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.ZigBwd
section
open UpperTheory.V.Cj.A UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

private theorem van_dOm {Γ V S I : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ}
    (G : Dr.Geo Γ V S d) (C : I → S → Set V) (F : S → Set V) (hC : ∀ i s, IsOpen (C i s))
    (hF : ∀ s, IsOpen (F s)) {q : ℕ} (k : ℕ) (b : List I → G.Om q) (hb : Van G C F k b) :
    Van G C F k (fun x => G.dOm q (b x)) := by
  intro x hx s p hp hxC
  beta_reduce
  by_cases hY : p ∈ G.Y
  · rw [G.dOm_apply (b x) s hY]
    have hW : IsOpen (F s ∩ ⋂ i ∈ {i | i ∈ x}, C i s) :=
      (hF s).inter ((List.finite_toSet x).isOpen_biInter (fun i _ => hC i s))
    have hev : ((b x : G.Om q) : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s =ᶠ[nhds p] fun _ => 0 := by
      filter_upwards [hW.mem_nhds ⟨hp, Set.mem_iInter₂.mpr hxC⟩] with y hy
      exact hb x hx s y hy.1 (fun i hi => Set.mem_iInter₂.mp hy.2 i hi)
    rw [extDeriv, hev.fderiv_eq, fderiv_const_apply]
    exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V (Fin d → ℂ))
  · exact ((G.dOm q (b x)).2 s).2 p hY

theorem UpperTheory.V.Cj.A.zigBwd :
    ZigBwd := by
  intro Γ V S I _ _ _ _ _ d G hY hne φ hφ C F hC hF hφC n c hc hdc hvc q
  obtain ⟨-, -, -, hhom, -, -⟩ := hdFacts
  obtain ⟨hi1, -, hi3⟩ := inclFacts Γ V S d G hY hne
  induction q with
  | zero =>
    intro k hk
    obtain rfl : k = n := by omega
    refine ⟨fun x => G.incl (c x), fun x _ => rfl, fun γ x hx => ?_, fun x _ => hi3.apply_apply_eq_zero _,
      fun x hx => ?_, fun x hx s p _ hp => ?_⟩
    · beta_reduce
      rw [hc γ x hx, hi1]
    · refine (hhom I _ _ G.incl.toAddMonoidHom c x).trans ?_
      rw [hdc x hx, map_zero]
    · by_cases hpY : p ∈ G.Y
      · ext1 v
        rw [G.incl_apply _ _ hpY, hvc x hx s p hp]
        rfl
      · exact ((G.incl (c x)).2 s).2 p hpY
  | succ q ih =>
    intro k hk
    obtain ⟨u, hz, hu, hdu, hhu, hvu⟩ := ih (k + 1) (by omega)
    obtain ⟨b, hb, hhb, hvb⟩ := bwdStep Γ V S I d G φ hφ C F hφC q k u hu hhu hvu
    refine ⟨fun x => G.dOm q (b x), ⟨b, hb, fun _ _ => rfl, ?_⟩, fun γ x hx => ?_,
      fun x _ => (dExact Γ V S d G hY q).apply_apply_eq_zero _, fun x hx => ?_,
      van_dOm G C F hC.isOpen hF k b hvb⟩
    · exact (zigFormal Γ V S I d G).1 q (k + 1) u (hd b) c (fun x hx => (hhb x hx).symm) hz
    · beta_reduce
      rw [hb γ x hx, dEquiv]
    · refine (hhom I _ _ (G.dOm q).toAddMonoidHom b x).trans ?_
      rw [hhb x hx]
      exact hdu x hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.ZigFwd
section
open UpperTheory.V.Cj.A UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

theorem UpperTheory.V.Cj.A.zigFwd :
    ZigFwd := by
  intro Γ V S I _ _ _ _ _ d G hc hne r hr C hC q
  obtain ⟨hdd, -, -, hmap, hloc, heq⟩ := hdFacts
  obtain ⟨hact, hinj, hex⟩ := inclFacts Γ V S d G hc hne
  induction q with
  | zero =>
    intro k n hn u hu hd0 hh hv
    obtain rfl : k = n := by simpa using hn
    have key : ∀ x : List I, ∃ f, x.length = k + 1 → u x = G.incl f := fun x => by
      by_cases hx : x.length = k + 1
      · obtain ⟨f, hf⟩ := (hex (u x)).1 (hd0 x hx)
        exact ⟨f, fun _ => hf.symm⟩
      · exact ⟨0, fun h => absurd h hx⟩
    choose c hcu using key
    refine ⟨c, hcu, fun γ x hx => hinj ?_, fun x hx => hinj ?_, fun x hx s p hp => ?_⟩
    · rw [hact, ← hcu x hx, ← hcu _ (by simpa using hx), hu γ x hx]
    · have h1 := hmap I _ _ G.incl.toAddMonoidHom c x
      have h2 := hloc I _ (fun y => G.incl.toAddMonoidHom (c y)) u x
        (fun y hy _ => (hcu y (by omega)).symm)
      rw [map_zero, ← hh x hx, ← h2, h1]
      rfl
    · obtain ⟨i, hi⟩ := List.exists_mem_of_length_eq_add_one hx
      have hY : p ∈ G.Y := hC.sub i s (hp i hi)
      rw [← G.incl_apply (c x) s hY Fin.elim0, ← hcu x hx, hv x hx s p trivial hp]
      rfl
  | succ q ih =>
    intro k n hn u hu hd0 hh hv
    obtain ⟨b, hb, hdb, hvb⟩ := fwdStep Γ V S I d G hc r hr C hC q k u hu hd0 hv
    obtain ⟨c, hz, hrest⟩ := ih (k + 1) n (by omega) (hd b) (heq Γ I _ (G.act q) k b hb)
      (fun x hx => by
        have h1 := hmap I _ _ (G.dOm q).toAddMonoidHom b x
        have h2 := hloc I _ (fun y => (G.dOm q).toAddMonoidHom (b y)) u x
          (fun y hy _ => hdb y (by omega))
        rw [← hh x hx, ← h2, h1]
        rfl)
      (fun x _ => hdd I _ b x)
      (fun x hx s p _ hp => by
        let ev : G.Om q →+ (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) :=
          { toFun := fun w => w.1 s p, map_zero' := rfl, map_add' := fun _ _ => rfl }
        have h1 := hmap I _ _ ev b x
        have h2 := hloc I _ (fun y => ev (b y)) (fun y => ev ((fun _ => (0 : G.Om q)) y)) x
          (fun y hy hyx => hvb y (by omega) s p trivial fun i hi => hp i (hyx i hi))
        change ev (hd b x) = 0
        rw [← h1, h2]
        simp [hd])
    exact ⟨c, ⟨b, hb, hdb, hz⟩, hrest⟩
end

