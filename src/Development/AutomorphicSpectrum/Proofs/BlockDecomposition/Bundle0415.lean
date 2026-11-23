module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0393
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0378
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0321
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0303
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetKernelSpanTwistedCharacter
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.Kernel

section Abstract

variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup W] [Module ℂ W]

theorem cInd_ext {H : Subgroup G} {σ : Representation ℂ H W} {a b : cIndSpace H σ}
    (h : ∀ g, a.1.1.1 g = b.1.1.1 g) : a = b :=
  Subtype.ext (Subtype.ext (Subtype.ext (funext h)))

theorem cInd_left {H : Subgroup G} {σ : Representation ℂ H W} (a : cIndSpace H σ) {h : G}
    (hh : h ∈ H) (g : G) : a.1.1.1 (h * g) = σ ⟨h, hh⟩ (a.1.1.1 g) :=
  a.1.1.2 ⟨h, hh⟩ g

theorem indicator_mem (H U : Subgroup G) (hUH : U ≤ H) (hU : U.Normal) (θ : U →* ℂˣ)
    (σ : Representation ℂ H W) {E : Set G} (hE : IsHK H E) (a : cIndSpace H σ)
    (ha : a ∈ twKer (cInd H σ) U θ) :
    ∀ a' : cIndSpace H σ, (∀ g ∈ E, a'.1.1.1 g = a.1.1.1 g) → (∀ g, g ∉ E → a'.1.1.1 g = 0) →
      a' ∈ twKer (cInd H σ) U θ := by
  have hR : ∀ (g : G) (u : U), g * (u : G) ∈ E ↔ g ∈ E := by
    intro g u
    have e : g * (u : G) = (g * (u : G) * g⁻¹) * g := by group
    rw [e]
    exact hE.1 _ (hUH (hU.conj_mem _ u.2 g)) g
  unfold twKer at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, v, rfl⟩ := hx
    intro a' h1 h2
    obtain ⟨v', hv1, hv2⟩ := exists_indicator H σ hE v
    have e : a' = cInd H σ (u : G) v' - (θ u : ℂ) • v' := by
      apply cInd_ext
      intro g
      by_cases hg : g ∈ E
      · rw [h1 g hg]
        show v.1.1.1 (g * u) - (θ u : ℂ) • v.1.1.1 g = v'.1.1.1 (g * u) - (θ u : ℂ) • v'.1.1.1 g
        rw [hv1 g hg, hv1 _ ((hR g u).2 hg)]
      · rw [h2 g hg]
        show (0 : W) = v'.1.1.1 (g * u) - (θ u : ℂ) • v'.1.1.1 g
        rw [hv2 g hg, hv2 _ (fun c => hg ((hR g u).1 c))]
        simp
    rw [e]
    exact Submodule.subset_span ⟨u, v', rfl⟩
  | zero =>
    intro a' h1 h2
    have e : a' = 0 := by
      apply cInd_ext
      intro g
      by_cases hg : g ∈ E
      · exact h1 g hg
      · exact h2 g hg
    rw [e]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    intro a' h1 h2
    obtain ⟨x', hx1, hx2⟩ := exists_indicator H σ hE x
    obtain ⟨y', hy1, hy2⟩ := exists_indicator H σ hE y
    have e : a' = x' + y' := by
      apply cInd_ext
      intro g
      by_cases hg : g ∈ E
      · rw [h1 g hg]
        show x.1.1.1 g + y.1.1.1 g = x'.1.1.1 g + y'.1.1.1 g
        rw [hx1 g hg, hy1 g hg]
      · rw [h2 g hg]
        show (0 : W) = x'.1.1.1 g + y'.1.1.1 g
        rw [hx2 g hg, hy2 g hg, add_zero]
    rw [e]
    exact Submodule.add_mem _ (hx x' hx1 hx2) (hy y' hy1 hy2)
  | smul c x _ hx =>
    intro a' h1 h2
    obtain ⟨x', hx1, hx2⟩ := exists_indicator H σ hE x
    have e : a' = c • x' := by
      apply cInd_ext
      intro g
      by_cases hg : g ∈ E
      · rw [h1 g hg]
        show c • x.1.1.1 g = c • x'.1.1.1 g
        rw [hx1 g hg]
      · rw [h2 g hg]
        show (0 : W) = c • x'.1.1.1 g
        rw [hx2 g hg, smul_zero]
    rw [e]
    exact Submodule.smul_mem _ c (hx x' hx1 hx2)

theorem exists_local (H U : Subgroup G) (hUH : U ≤ H) (hU : U.Normal) (θ : U →* ℂˣ)
    (σ : Representation ℂ H W) (f f' : cIndSpace H σ) (hf' : f' ∈ twKer (cInd H σ) U θ) (g₀ : G)
    (he : f'.1.1.1 g₀ = f.1.1.1 g₀) :
    ∃ E : Set G, g₀ ∈ E ∧ IsHK H E ∧ ∃ b ∈ twKer (cInd H σ) U θ,
      (∀ g ∈ E, b.1.1.1 g = f.1.1.1 g) ∧ (∀ g, g ∉ E → b.1.1.1 g = 0) := by
  obtain ⟨K, hK, hKi⟩ := cInd_right_inv H σ (f - f')
  have hE := isHK_doubleCoset H K hK g₀
  refine ⟨{g | ∃ a ∈ H, ∃ x ∈ K, g = a * g₀ * x}, ⟨1, one_mem H, 1, one_mem K, by simp⟩, hE, ?_⟩
  obtain ⟨b, hb1, hb2⟩ := exists_indicator H σ hE f'
  refine ⟨b, indicator_mem H U hUH hU θ σ hE f' hf' b hb1 hb2, ?_, hb2⟩
  rintro g ⟨a, ha, x, hx, rfl⟩
  rw [hb1 _ ⟨a, ha, x, hx, rfl⟩]
  have h0 : (f - f').1.1.1 g₀ = 0 := by
    show f.1.1.1 g₀ - f'.1.1.1 g₀ = 0
    rw [he, sub_self]
  have h1 : (f - f').1.1.1 (a * g₀ * x) = 0 := by
    rw [hKi _ x hx, cInd_left (f - f') ha, h0, map_zero]
  have h2 : f.1.1.1 (a * g₀ * x) - f'.1.1.1 (a * g₀ * x) = 0 := h1
  exact (sub_eq_zero.1 h2).symm

theorem mem_of_local (H U : Subgroup G) (hUH : U ≤ H) (hU : U.Normal) (θ : U →* ℂˣ)
    (σ : Representation ℂ H W) (f : cIndSpace H σ)
    (hloc : ∀ g₀ : G, ∃ E : Set G, g₀ ∈ E ∧ IsHK H E ∧ ∃ b ∈ twKer (cInd H σ) U θ,
      (∀ g ∈ E, b.1.1.1 g = f.1.1.1 g) ∧ (∀ g, g ∉ E → b.1.1.1 g = 0)) :
    f ∈ twKer (cInd H σ) U θ := by
  obtain ⟨C, hC, hf⟩ := f.2
  have key : ∃ E : Set G, C ⊆ E ∧ IsHK H E ∧ ∃ b ∈ twKer (cInd H σ) U θ,
      (∀ g ∈ E, b.1.1.1 g = f.1.1.1 g) ∧ (∀ g, g ∉ E → b.1.1.1 g = 0) := by
    refine hC.induction_on (p := fun S => ∃ E : Set G, S ⊆ E ∧ IsHK H E ∧
      ∃ b ∈ twKer (cInd H σ) U θ,
        (∀ g ∈ E, b.1.1.1 g = f.1.1.1 g) ∧ (∀ g, g ∉ E → b.1.1.1 g = 0)) ?_ ?_ ?_ ?_
    · refine ⟨∅, subset_rfl, ⟨by simp, ⊤, isOpen_univ, by simp⟩, 0, Submodule.zero_mem _, by simp,
        fun g _ => rfl⟩
    · rintro S T hST ⟨E, hTE, r⟩
      exact ⟨E, hST.trans hTE, r⟩
    · rintro S T ⟨E, hSE, hE, b, hb, hb1, hb2⟩ ⟨E', hTE, hE', b', hb', hb1', hb2'⟩
      obtain ⟨c, hc1, hc2⟩ := exists_indicator H σ hE.compl b'
      refine ⟨E ∪ E', Set.union_subset_union hSE hTE, hE.union hE', b + c,
        Submodule.add_mem _ hb (indicator_mem H U hUH hU θ σ hE.compl b' hb' c hc1 hc2), ?_, ?_⟩
      · intro g hg
        show b.1.1.1 g + c.1.1.1 g = f.1.1.1 g
        by_cases h : g ∈ E
        · rw [hb1 g h, hc2 g (fun c => c h), add_zero]
        · rw [hb2 g h, hc1 g h, zero_add]
          exact hb1' g (hg.resolve_left h)
      · intro g hg
        show b.1.1.1 g + c.1.1.1 g = 0
        have h : g ∉ E := fun c => hg (Or.inl c)
        have h' : g ∉ E' := fun c => hg (Or.inr c)
        rw [hb2 g h, hc1 g h, hb2' g h', add_zero]
    · intro x _
      obtain ⟨E, hx, hE, r⟩ := hloc x
      exact ⟨E, mem_nhdsWithin_of_mem_nhds (hE.isOpen.mem_nhds hx), E, subset_rfl, hE, r⟩
  obtain ⟨E, hCE, hE, b, hb, hb1, hb2⟩ := key
  have e : f = b := by
    apply cInd_ext
    intro g
    by_cases hg : g ∈ E
    · exact (hb1 g hg).symm
    · rw [hb2 g hg]
      by_contra h0
      obtain ⟨h, hh, c, hc, rfl⟩ := hf g h0
      exact hg ((hE.1 h hh c).2 (hCE hc))
  rw [e]
  exact hb

end Abstract

theorem mem_twKer_of_restrict_zero {G G' W W' : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group G']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H U : Subgroup G) (hUH : U ≤ H) (hU : U.Normal) (θ : U →* ℂˣ) (ι : G' →* G)
    (hst : ∀ (m : G') (n : U), ∃ h : ι m * (n : G) * (ι m)⁻¹ ∈ U, θ ⟨_, h⟩ = θ n)
    (σ : Representation ℂ H W) (q : W →ₗ[ℂ] W') (hσ : IsSmooth σ)
    (hq : ∀ w, q w = 0 ↔ w ∈ Submodule.span ℂ {y | ∃ (u : U) (v : W), y = σ ⟨u, hUH u.2⟩ v - (θ u : ℂ) • v})
    (hdich : ∀ g : G, (∃ h ∈ H, ∃ x : G', g = h * ι x) ∨
      ∃ u : U, ∃ hx : g * (u : G) * g⁻¹ ∈ H, (∀ w, σ ⟨_, hx⟩ w = w) ∧ θ u ≠ 1)
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (f : cIndSpace H σ) (hf : ∀ x, q (f.1.1.1 (ι x)) = 0) : f ∈ twKer (cInd H σ) U θ := by
  refine mem_of_local H U hUH hU θ σ f fun g₀ => ?_
  suffices hp : ∃ f' ∈ twKer (cInd H σ) U θ, f'.1.1.1 g₀ = f.1.1.1 g₀ by
    obtain ⟨f', hf', he⟩ := hp
    exact exists_local H U hUH hU θ σ f f' hf' g₀ he
  rcases hdich g₀ with ⟨h, hh, x, rfl⟩ | ⟨u, hx, hfix, hθ⟩
  · have hval : ∀ y ∈ Submodule.span ℂ {y | ∃ (u : U) (v : W), y = σ ⟨u, hUH u.2⟩ v - (θ u : ℂ) • v},
        ∃ f' ∈ twKer (cInd H σ) U θ, f'.1.1.1 (ι x) = y := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨v, w, rfl⟩ := hy
        obtain ⟨hm, hθ⟩ := hst x⁻¹ v
        obtain ⟨e, he⟩ := exists_cInd_value H σ hσ hbase (ι x) w
        refine ⟨cInd H σ _ e - (θ ⟨_, hm⟩ : ℂ) • e, Submodule.subset_span ⟨⟨_, hm⟩, e, rfl⟩, ?_⟩
        have e1 : ι x * (ι x⁻¹ * (v : G) * (ι x⁻¹)⁻¹) = (v : G) * ι x := by
          simp only [map_inv]
          group
        show e.1.1.1 (ι x * (ι x⁻¹ * (v : G) * (ι x⁻¹)⁻¹)) - (θ ⟨_, hm⟩ : ℂ) • e.1.1.1 (ι x) = _
        rw [e1, cInd_left e (hUH v.2), he, hθ]
      | zero => exact ⟨0, Submodule.zero_mem _, rfl⟩
      | add a b _ _ ha hb =>
        obtain ⟨a', ha', ea⟩ := ha
        obtain ⟨b', hb', eb⟩ := hb
        refine ⟨a' + b', Submodule.add_mem _ ha' hb', ?_⟩
        show a'.1.1.1 (ι x) + b'.1.1.1 (ι x) = _
        rw [ea, eb]
      | smul c a _ ha =>
        obtain ⟨a', ha', ea⟩ := ha
        refine ⟨c • a', Submodule.smul_mem _ c ha', ?_⟩
        show c • a'.1.1.1 (ι x) = _
        rw [ea]
    obtain ⟨f', hf', he⟩ := hval _ ((hq _).1 (hf x))
    exact ⟨f', hf', by rw [cInd_left f' hh, cInd_left f hh, he]⟩
  · have hne : (1 : ℂ) - (θ u : ℂ) ≠ 0 := by
      intro h0
      apply hθ
      apply Units.ext
      simpa using (sub_eq_zero.1 h0).symm
    obtain ⟨e, he⟩ := exists_cInd_value H σ hσ hbase g₀ (((1 : ℂ) - (θ u : ℂ))⁻¹ • f.1.1.1 g₀)
    refine ⟨cInd H σ (u : G) e - (θ u : ℂ) • e, Submodule.subset_span ⟨u, e, rfl⟩, ?_⟩
    have e1 : g₀ * (u : G) = (g₀ * (u : G) * g₀⁻¹) * g₀ := by group
    show e.1.1.1 (g₀ * u) - (θ u : ℂ) • e.1.1.1 g₀ = _
    rw [e1, cInd_left e hx, hfix, he]
    have e2 : ∀ y : W, y - (θ u : ℂ) • y = ((1 : ℂ) - (θ u : ℂ)) • y := fun y => by
      rw [sub_smul, one_smul]
    rw [e2, smul_smul, mul_inv_cancel₀ hne, one_smul]

end GlobalTheory.CompanionTheory.LeibPhi.Kernel

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySublistPadding
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd

universe u

theorem sub_positions_univ {α : Type u} {h : ℕ} (W : List α) (c : Fin W.length → Fin h) (i : Fin h) :
    ∃ o : Fin (sub W c i).length → Fin W.length, StrictMono o ∧ (∀ j, c j = i ↔ j ∈ Set.range o) ∧
      ∀ a, (sub W c i).get a = W.get (o a) := by
  have key : ∀ L : List (Fin W.length), L.Pairwise (· < ·) → (∀ j, j ∈ L ↔ c j = i) →
      ∃ o : Fin (L.map W.get).length → Fin W.length, StrictMono o ∧ (∀ j, c j = i ↔ j ∈ Set.range o) ∧
        ∀ a, (L.map W.get).get a = W.get (o a) := by
    intro L hpw hmem
    have hlen : (L.map W.get).length = L.length := by simp
    refine ⟨fun a => L.get (Fin.cast hlen a), ?_, ?_, ?_⟩
    · intro a b hab
      have hab' : Fin.cast hlen a < Fin.cast hlen b := by
        first
        | exact hab
        | simpa [Fin.lt_def] using hab
      exact List.pairwise_iff_get.1 hpw (Fin.cast hlen a) (Fin.cast hlen b) hab'
    · intro j
      constructor
      · intro hj
        obtain ⟨n, hn⟩ := List.mem_iff_get.1 ((hmem j).2 hj)
        refine ⟨Fin.cast hlen.symm n, ?_⟩
        first
        | exact hn
        | simpa using hn
      · rintro ⟨a, rfl⟩
        exact (hmem _).1 (List.mem_iff_get.2 ⟨_, rfl⟩)
    · intro a
      simp [List.get_eq_getElem]
  exact key ((List.finRange W.length).filter (fun p => decide (c p = i)))
    ((List.pairwise_lt_finRange _).filter _) (fun j => by simp)

end GlobalTheory.CompanionTheory.FineProd

namespace GlobalTheory.CompanionTheory.FineProd

theorem jm_row : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (W : List (IrrGL (k := k))) (c : Fin W.length → Fin h) (i : Fin h) (Y : Fin W.length → IrrGL (k := k)), (∀ j, c j = i → Y j = W.get j) → (∀ j, c j ≠ i → (Y j).1 = 0) → ∀ (hd : ∑ j, (Y j).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), jm Y hd π = jmL (sub W c i) π := by
  intro k _ _ _ _ h N W c i Y hY h0 hd V _ _ π
  obtain ⟨o, ho, hr, hg⟩ := sub_positions_univ W c i
  have hget : (sub W c i).get = fun a => Y (o a) := by
    funext a
    rw [hg a, hY (o a) ((hr (o a)).2 ⟨a, rfl⟩)]
  have hsum : ∑ a, (Y (o a)).1 = N := by
    rw [← hd]
    have himg : ∑ j ∈ Finset.univ.image o, (Y j).1 = ∑ a, (Y (o a)).1 :=
      Finset.sum_image (fun a _ b _ e => ho.injective e)
    rw [← himg]
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro j _ hj
    refine h0 j ?_
    intro e
    obtain ⟨a, rfl⟩ := (hr j).1 e
    exact hj (Finset.mem_image_of_mem o (Finset.mem_univ a))
  have hnz : ∀ j, (Y j).1 ≠ 0 → j ∈ Set.range o := by
    intro j hj
    refine (hr j).1 ?_
    by_contra e
    exact hj (h0 j e)
  have hdeg : ∑ a, ((sub W c i).get a).1 = N := by
    rw [hget]
    exact hsum
  have hcongr : ∀ {r : ℕ} (x y : Fin r → IrrGL (k := k)) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N),
      x = y → jm x hx π = jm y hy π := by
    intro r x y hx hy e
    subst e
    rfl
  rw [GlobalTheory.T.jacquet_multiplicity_drop_zero_blocks Y hd o ho hnz hsum π, jmL, dite_eq_left hdeg]
  exact hcongr _ _ _ _ hget.symm

end GlobalTheory.CompanionTheory.FineProd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductProperSmooth
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem resU_self_bij {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    (U : ObjectProperty C) (k : U ≤ U) (n : ℕ) : Function.Bijective ((resU F k).pull n) := by
  have h : ∀ x, (resU F k).pull n x = x := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  exact ⟨fun x y e => by simpa only [h] using e, fun y => ⟨y, h y⟩⟩

theorem resU_bij_congr {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    {U V V' : ObjectProperty C} (e : V = V') (k : V ≤ U) (k' : V' ≤ U) (n : ℕ)
    (h : Function.Bijective ((resU F k').pull n)) : Function.Bijective ((resU F k).pull n) := by
  subst e
  exact h

theorem kun_congr {K : Type} [Field K] (E : XD K) {U₁ U₁' : ObjectProperty E.C₁} {U₂ : ObjectProperty E.C₂}
    {U₃ U₃' : ObjectProperty E.D} (e₁ : U₁ = U₁') (e₃ : U₃ = U₃')
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T))
    (h₁' : ∀ T, U₃' T → U₁' (E.L₁.obj T)) (h₂' : ∀ T, U₃' T → U₂ (E.L₂.obj T))
    (h : E.Kun U₁ U₂ U₃ h₁ h₂) : E.Kun U₁' U₂ U₃' h₁' h₂' := by
  subst e₁ e₃
  exact h

theorem glue_top (hMV : MVBij) (hCD : CovDesc) {K : Type} [Field K] (E : XD K) (U₁ : ObjectProperty E.C₁)
    (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D) {ι : Type} [DecidableEq ι] [Fintype ι]
    (V : ι → ObjectProperty E.C₁) (W : ι → ObjectProperty E.D) (hV : ∀ α, Cosieve (V α)) (hW : ∀ α, Cosieve (W α))
    (h₁ : ∀ S : Finset ι, ∀ T, capU W S T → capU V S (E.L₁.obj T))
    (h₂ : ∀ S : Finset ι, ∀ T, capU W S T → U₂ (E.L₂.obj T))
    (hK : ∀ S : Finset ι, S.Nonempty → E.Kun (capU V S) U₂ (capU W S) (h₁ S) (h₂ S))
    (k₁ : capU V ∅ ≤ U₁) (k₃ : capU W ∅ ≤ U₃)
    (b₁ : ∀ a n, Function.Bijective ((resU (E.F₁ a) k₁).pull n))
    (b₃ : ∀ a n, Function.Bijective ((resU (E.F₃ a) k₃).pull n))
    (g₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (g₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) : E.Kun U₁ U₂ U₃ g₁ g₂ :=
  (GlobalTheory.T.kuenneth_of_restrict_bijective E g₁ g₂ (h₁ ∅) (h₂ ∅) k₁ (le_refl U₂) k₃ b₁ (fun a n => resU_self_bij _ _ _ n) b₃).2
    (_root_.GlobalTheory.CompanionTheory.KunGlue.glue_l hMV hCD E U₂ V W hV hW h₁ h₂ hK)

section Site

variable {K : Type} [CommRing K] {Z Y : Scheme.{0}}

theorem inU_pull (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) {r : Y ⟶ Spec (CommRingCat.of K)} (u : Y ⟶ Z)
    (hu : u ≫ q = r) (A : Z.Opens) (T) : inU r (u ⁻¹ᵁ A) T ↔ inU q A ((smS u hu).G.obj T) := by
  subst hu
  exact (hS K Z Z Y q (𝟙 Z) u).2.2.2.2.1 A T

theorem inU_cos (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) (A : Z.Opens) : Cosieve (inU q A) :=
  (hS K Z Z Z q (𝟙 Z) (𝟙 Z)).1 A

theorem inU_top (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) (T) : inU q ⊤ T :=
  (hS K Z Z Z q (𝟙 Z) (𝟙 Z)).2.2.1 T

theorem inU_inf (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) (A B : Z.Opens) (T) :
    inU q (A ⊓ B) T ↔ inU q A T ∧ inU q B T :=
  (hS K Z Z Z q (𝟙 Z) (𝟙 Z)).2.2.2.1 A B T

theorem inU_biInf (hS : SiteLaws) (q : Z ⟶ Spec (CommRingCat.of K)) {ι : Type} [DecidableEq ι] (A : ι → Z.Opens)
    (S : Finset ι) (T) : inU q (⨅ α ∈ S, A α) T ↔ ∀ α ∈ S, inU q (A α) T := by
  induction S using Finset.induction_on with
  | empty => simpa using inU_top hS q T
  | insert a S _ ih =>
    rw [Finset.iInf_insert, inU_inf hS, ih]
    simp

end Site

theorem kun_left : SiteLaws → MVBij → CovDesc → ZarAbs → AffOm → KunAff → ∀ (K : Type) [Field K] [CharZero K] (X X' P : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) [IsProper q] [Smooth q] [IsProper q'] [Smooth q'] (p₁ : P ⟶ X) (p₂ : P ⟶ X') (hP : IsPullback p₁ p₂ q q'), ∀ (h₁ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₁.obj T)) (h₂ : ∀ T, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hP.w.symm).L₂.obj T)), (hodgeXD q q' p₁ p₂ hP.w.symm).Kun (inU q ⊤) (inU q' ⊤) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤)) h₁ h₂ := by
  intro hS hMV hCD hZ hA hKA K _ _ X X' P q q' _ _ _ _ p₁ p₂ hP g₁ g₂
  classical
  obtain ⟨U⟩ := (cov_ex q).1 inferInstance
  have hw := hP.w.symm
  have inP : ∀ (A : X.Opens) (B : X'.Opens) (T),
      inU (p₁ ≫ q) (p₁ ⁻¹ᵁ A ⊓ p₂ ⁻¹ᵁ B) T ↔
        inU q A ((hodgeXD q q' p₁ p₂ hw).L₁.obj T) ∧ inU q' B ((hodgeXD q q' p₁ p₂ hw).L₂.obj T) := by
    intro A B T
    rw [inU_inf hS, inU_pull hS q p₁ rfl, inU_pull hS q' p₂ hw]
    rfl
  let V : U.ι → ObjectProperty (hodgeXD q q' p₁ p₂ hw).C₁ := fun α => inU q (U.U α)
  let W : U.ι → ObjectProperty (hodgeXD q q' p₁ p₂ hw).D := fun α => inU (p₁ ≫ q) (p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤)
  have h₁ : ∀ S : Finset U.ι, ∀ T, capU W S T → capU V S ((hodgeXD q q' p₁ p₂ hw).L₁.obj T) := by
    rintro S T ⟨⟨α, hα⟩, h⟩
    exact ⟨⟨α, ((inP _ _ T).1 hα).1⟩, fun β hβ => ((inP _ _ T).1 (h β hβ)).1⟩
  have h₂ : ∀ S : Finset U.ι, ∀ T, capU W S T → inU q' ⊤ ((hodgeXD q q' p₁ p₂ hw).L₂.obj T) :=
    fun S T _ => inU_top hS q' _
  have eV : ∀ S : Finset U.ι, S.Nonempty → inU q (⨅ α ∈ S, U.U α) = capU V S := by
    rintro S ⟨α₀, h₀⟩
    funext T
    refine propext ((inU_biInf hS q U.U S T).trans ⟨fun h => ⟨⟨α₀, h α₀ h₀⟩, h⟩, fun h => h.2⟩)
  have eW : ∀ S : Finset U.ι, S.Nonempty →
      inU (p₁ ≫ q) (p₁ ⁻¹ᵁ (⨅ α ∈ S, U.U α) ⊓ p₂ ⁻¹ᵁ ⊤) = capU W S := by
    rintro S ⟨α₀, h₀⟩
    funext T
    refine propext ((inP _ _ T).trans ⟨fun h => ?_, fun h => ?_⟩)
    · have a : ∀ α ∈ S, W α T := fun α hα =>
        (inP _ _ T).2 ⟨(inU_biInf hS q U.U S _).1 h.1 α hα, h.2⟩
      exact ⟨⟨α₀, a α₀ h₀⟩, a⟩
    · exact ⟨(inU_biInf hS q U.U S _).2 fun α hα => ((inP _ _ T).1 (h.2 α hα)).1, inU_top hS q' _⟩
  have hK : ∀ S : Finset U.ι, S.Nonempty →
      (hodgeXD q q' p₁ p₂ hw).Kun (capU V S) (inU q' ⊤) (capU W S) (h₁ S) (h₂ S) := by
    intro S hSn
    obtain ⟨α₀, h₀⟩ := id hSn
    obtain ⟨c, -⟩ := coord_res (U.c α₀) (iInf₂_le α₀ h₀) (U.inter S hSn)
    exact kun_congr _ (eV S hSn) (eW S hSn) _ _ _ _
      (_root_.GlobalTheory.CompanionTheory.KunGlue.Right.kun_right hS hMV hCD hZ hA hKA K X X' P q q' p₁ p₂ hP _ _ ⟨c⟩
        (fun T h => ((inP _ _ T).1 h).1) (fun T h => ((inP _ _ T).1 h).2))
  have e₁ : capU V ∅ = fun T => ∃ α, inU q (U.U α) T := by
    funext T
    exact propext ⟨fun h => h.1, fun h => ⟨h, fun _ h' => absurd h' (Finset.notMem_empty _)⟩⟩
  have e₃ : capU W ∅ = fun T => ∃ α, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤) T := by
    funext T
    exact propext ⟨fun h => h.1, fun h => ⟨h, fun _ h' => absurd h' (Finset.notMem_empty _)⟩⟩
  have k₁ : capU V ∅ ≤ inU q ⊤ := fun T _ => inU_top hS q T
  have k₃ : capU W ∅ ≤ inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) := by
    rintro T ⟨⟨α, hα⟩, -⟩
    exact (inP _ _ T).2 ⟨inU_top hS q _, inU_top hS q' _⟩
  have hc : (⨆ α, p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤) = p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤ := by
    refine le_antisymm (iSup_le fun α => inf_le_inf_right _ ((TopologicalSpace.Opens.map p₁.base).monotone le_top)) ?_
    intro x _
    have hx : p₁ x ∈ (⨆ α, U.U α) := by
      rw [U.cover]
      trivial
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨α, hα, trivial⟩
  have l₁ : (fun T => ∃ α, inU q (U.U α) T) ≤ inU q ⊤ := fun T _ => inU_top hS q T
  have l₃ : (fun T => ∃ α, inU (p₁ ≫ q) (p₁ ⁻¹ᵁ U.U α ⊓ p₂ ⁻¹ᵁ ⊤) T) ≤ inU (p₁ ≫ q) (p₁ ⁻¹ᵁ ⊤ ⊓ p₂ ⁻¹ᵁ ⊤) := by
    rintro T ⟨α, hα⟩
    exact (inP _ _ T).2 ⟨inU_top hS q _, inU_top hS q' _⟩
  exact glue_top hMV hCD (hodgeXD q q' p₁ p₂ hw) (inU q ⊤) (inU q' ⊤) _ V W
    (fun α => inU_cos hS q _) (fun α => inU_cos hS _ _) h₁ h₂ hK k₁ k₃
    (fun a n => resU_bij_congr _ e₁ k₁ l₁ n (hZ K X q U.ι ⊤ U.U U.cover l₁ a n))
    (fun a n => resU_bij_congr _ e₃ k₃ l₃ n (hZ K P (p₁ ≫ q) U.ι _ _ hc l₃ a n)) g₁ g₂

end GlobalTheory.CompanionTheory.KunGlue
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittFrame
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin.FrameLoc

theorem hR_colV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (X Y : Matrix (Fin n) (Fin r) E)
    (v : HeightOneSpectrum (𝓞 F)) (i j : Fin r) :
    hR (Fv F v) σ J (colV v X i) (colV v Y j) = inclR (F := F) (Fv F v) ((cT (σ : E →+* E) X * J * Y) i j) := by
  have hs : ∀ t : E, sigR (Fv F v) σ (inclR (F := F) (Fv F v) t) = inclR (F := F) (Fv F v) (σ t) := by
    intro t; simp [sigR, inclR]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, Formalism.UG.hform, colV, JR, Matrix.map_apply, hs, Matrix.mul_apply, cT, Matrix.transpose_apply,
    map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem isFrame_colV : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)), IsFrame (hR (Fv F v) σ J) (colV v X) (colV v Y) := by
  intro F E _ _ _ _ _ σ n J r X Y _ _ hW v
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · rw [hR_colV, hW.xx]; simp
  · rw [hR_colV, hW.yy]; simp
  · rw [hR_colV, hW.xy, Matrix.one_apply]; split_ifs <;> simp

end GlobalTheory.CompanionTheory.KFin.FrameLoc
end

