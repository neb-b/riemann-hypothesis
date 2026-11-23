module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HalvesFreeAndAdjoint
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmTypeLetterFrameColumnDictionary
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.FrameUnif

theorem exists_letter_equiv {E : Type} [Field E] (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (p q r : ℕ) (hr : r = p + q)
    (ρ : (E →+* ℂ) → (E →+* ℂ)) (hρ : Function.Bijective ρ) (m : (E →+* ℂ) → ℕ)
    (hp : ∀ τ, ρ τ ∈ Ψ → m τ = p) (hq : ∀ τ, ρ τ ∉ Ψ → m τ = q) :
    ∃ f : (Σ τ, Fin (m τ)) ≃ Ψ × Fin r, ∀ s,
      (ρ s.1 ∈ Ψ ∧ (f s).1.1 = ρ s.1 ∧ ((f s).2 : ℕ) = q + s.2) ∨
      (ρ s.1 ∉ Ψ ∧ (f s).1.1 = ComplexEmbedding.conjugate (ρ s.1) ∧ ((f s).2 : ℕ) = q - 1 - s.2 ∧ (s.2 : ℕ) < q) := by
  classical
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  have hf : ∀ s : Σ τ, Fin (m τ), ∃ t : Ψ × Fin r,
      (ρ s.1 ∈ Ψ ∧ t.1.1 = ρ s.1 ∧ (t.2 : ℕ) = q + s.2) ∨
      (ρ s.1 ∉ Ψ ∧ t.1.1 = ComplexEmbedding.conjugate (ρ s.1) ∧ (t.2 : ℕ) = q - 1 - s.2 ∧ (s.2 : ℕ) < q) := by
    rintro ⟨τ, i⟩
    have hi := i.2
    by_cases h : ρ τ ∈ Ψ
    · have := hp τ h
      exact ⟨(⟨ρ τ, h⟩, ⟨q + i, by omega⟩), Or.inl ⟨h, rfl, rfl⟩⟩
    · have := hq τ h
      have h' : ComplexEmbedding.conjugate (ρ τ) ∈ Ψ := by
        by_contra h'
        exact h ((hΨ _).2 h')
      exact ⟨(⟨_, h'⟩, ⟨q - 1 - i, by omega⟩), Or.inr ⟨h, rfl, rfl, by show (i : ℕ) < q; omega⟩⟩
  choose f hf using hf
  have hext : ∀ s s' : Σ τ, Fin (m τ), ρ s.1 = ρ s'.1 → (s.2 : ℕ) = s'.2 → s = s' := by
    rintro ⟨τ, i⟩ ⟨τ', i'⟩ h1 h2
    obtain rfl : τ = τ' := hρ.1 h1
    obtain rfl : i = i' := Fin.ext h2
    rfl
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, hf⟩
  · intro s s' hss
    have h1 := hf s
    have h2 := hf s'
    rw [← hss] at h2
    rcases h1 with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1, d1⟩ <;> rcases h2 with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2, d2⟩
    · exact hext _ _ (b1.symm.trans b2) (by omega)
    · omega
    · omega
    · refine hext _ _ ?_ (by omega)
      rw [← hcc (ρ s.1), ← b1, b2, hcc]
  · rintro ⟨⟨τ, hτ⟩, j⟩
    have hj := j.2
    by_cases h : (j : ℕ) < q
    · obtain ⟨τ0, h0⟩ := hρ.2 (ComplexEmbedding.conjugate τ)
      have hn : ρ τ0 ∉ Ψ := h0 ▸ (hΨ τ).1 hτ
      have := hq τ0 hn
      refine ⟨⟨τ0, ⟨q - 1 - j, by omega⟩⟩, ?_⟩
      rcases hf ⟨τ0, ⟨q - 1 - j, by omega⟩⟩ with ⟨a, -⟩ | ⟨-, b, c, -⟩
      · exact absurd a hn
      · refine Prod.ext (Subtype.ext ?_) (Fin.ext ?_)
        · rw [b]; show ComplexEmbedding.conjugate (ρ τ0) = τ; rw [h0, hcc]
        · rw [c]; show q - 1 - (q - 1 - j) = j; omega
    · obtain ⟨τ0, h0⟩ := hρ.2 τ
      have hn : ρ τ0 ∈ Ψ := h0 ▸ hτ
      have := hp τ0 hn
      refine ⟨⟨τ0, ⟨j - q, by omega⟩⟩, ?_⟩
      rcases hf ⟨τ0, ⟨j - q, by omega⟩⟩ with ⟨-, b, c⟩ | ⟨a, -⟩
      · refine Prod.ext (Subtype.ext ?_) (Fin.ext ?_)
        · rw [b]; exact h0
        · rw [c]; show q + (j - q) = j; omega
      · exact absurd hn a

theorem letter_column_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r), GoodEmb c σ → ModelBase M → NegXi M → ∀ k, (∃ idx : Fin g ≃ (M.X k).Ψ × Fin r, (∀ j, relab c σ (e j).1 = if ((idx j).2 : ℕ) < (F.Di k).q then ComplexEmbedding.conjugate (idx j).1.1 else (idx j).1.1) ∧ (∀ j, ((idx j).2 : ℕ) = if ((idx j).2 : ℕ) < (F.Di k).q then (F.Di k).q - 1 - (e j).2 else (F.Di k).q + (e j).2) ∧ ∀ (x : Frame (M.X k).Ψ r) (v : Fin r → E) j, perFr (M.X k) x v (relab c σ (e j).1) (e j).2 = if ((idx j).2 : ℕ) < (F.Di k).q then hermC (idx j).1.1 (M.X k).Gm (col (mat x (idx j).1) (idx j).2) (Data.emb (idx j).1.1 v) else ((mat x (idx j).1)⁻¹ *ᵥ Data.emb (idx j).1.1 v) (idx j).2) ∧ (M.X k).p0 = (F.Di k).q ∧ r = (F.Di k).p + (F.Di k).q ∧ cc (-(M.X k).ξ0) = -(-(M.X k).ξ0) ∧ (∀ τ ∈ (M.X k).Ψ, 0 < (τ (-(M.X k).ξ0)).im) ∧ ∀ φ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E), (∀ a, φ a = (M.φ k a : Fin r → E)) → LinearMap.range φ = (M.X k).Λ ∧ (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc ((M.X k).Gm a b) = (M.X k).Gm b a) ∧ (M.X k).Gm.det ≠ 0 ∧ ∀ x y, (((F.Di k).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-(M.X k).ξ0 * herm (M.X k).Gm (φ x) (φ y))) := by
  intro E _ _ _ H Dw l Xo c σ g e F r M hσ hB hN k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp, hq⟩ := F.sig k
  obtain ⟨hp0, hty⟩ := hB.type k
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := fun τ =>
    ComplexEmbedding.involutive_conjugate E τ
  refine ⟨?_, hp0.trans hq.symm, by rw [hp, hq]; exact hB.rank, ?_, ?_, ?_⟩
  · obtain ⟨f, hf⟩ := exists_letter_equiv (M.X k).Ψ (M.X k).cmType Dw.p Dw.q r hB.rank (relab c σ) hbij Dw.mult
      (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
      (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
    obtain ⟨idx, hi⟩ : ∃ idx : Fin g ≃ (M.X k).Ψ × Fin r, ∀ j,
        (relab c σ (e j).1 ∈ (M.X k).Ψ ∧ (idx j).1.1 = relab c σ (e j).1 ∧ ((idx j).2 : ℕ) = Dw.q + (e j).2) ∨
        (relab c σ (e j).1 ∉ (M.X k).Ψ ∧ (idx j).1.1 = ComplexEmbedding.conjugate (relab c σ (e j).1) ∧
          ((idx j).2 : ℕ) = Dw.q - 1 - (e j).2 ∧ ((e j).2 : ℕ) < Dw.q) := ⟨e.trans f, fun j => hf (e j)⟩
    rw [hq]
    refine ⟨idx, fun j => ?_, fun j => ?_, fun x v j => ?_⟩
    · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
      · rw [if_neg (by omega), b]
      · rw [if_pos (by omega), b, hcc]
    · rcases hi j with ⟨a, b, c'⟩ | ⟨a, b, c', d⟩
      · rw [if_neg (by omega), c']
      · rw [if_pos (by omega), c']
    · have h := hi j
      generalize idx j = t at h ⊢
      obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
      dsimp only at h ⊢
      rw [← hp0] at h ⊢
      rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
      · rw [if_neg (by omega)]
        unfold perFr
        rw [dite_eq_left a, dite_eq_left hn]
      · rw [if_pos (by omega)]
        unfold perFr
        rw [dite_eq_right a, dite_eq_left (show conjEmb (relab c σ (e j).1) ∈ (M.X k).Ψ from hτ), dite_eq_left hn]
        rfl
  · have h := (M.X k).ξ0_im
    unfold cc at h ⊢
    rw [map_neg, h]
  · intro τ hτ
    have := hN k τ hτ
    rw [map_neg, Complex.neg_im]
    linarith
  · intro φ hφ
    have hrange : LinearMap.range φ = (M.X k).Λ := by
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        rw [hφ]
        exact (M.φ k a).2
      · intro hy
        exact ⟨(M.φ k).symm ⟨y, hy⟩, by rw [hφ, LinearEquiv.apply_symm_apply]⟩
    refine ⟨hrange, ?_, ?_, (M.X k).Gm_herm, (M.X k).Gm_det, fun x y => ?_⟩
    · intro a b hab
      rw [hφ, hφ] at hab
      exact (M.φ k).injective (Subtype.ext hab)
    · rw [← LinearMap.coe_range, hrange]
      exact (M.X k).Λ_span
    · rw [hφ, hφ]
      exact hB.ef k x y

end GlobalTheory.FrameUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EigenBasisIffTangentBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem basis_iff_of_split {S N J : Type} [CommRing S] [AddCommGroup N] [Module S N] [Fintype J]
    (m : J → ℕ) (M : J → Submodule S N)
    (hs : ∀ n : N, ∃! f : J → N, (∀ τ, f τ ∈ M τ) ∧ ∑ τ, f τ = n)
    (b : ∀ τ, Fin (m τ) → N) (hb : ∀ τ i, b τ i ∈ M τ) (g : ℕ) (e : Fin g ≃ Σ τ : J, Fin (m τ)) :
    (∀ τ n, n ∈ M τ → ∃! a : Fin (m τ) → S, n = ∑ i, a i • b τ i) ↔
      ∀ n : N, ∃! a : Fin g → S, n = ∑ j, a j • b (e j).1 (e j).2 := by
  classical
  have key : ∀ a : ∀ τ, Fin (m τ) → S,
      ∑ j, a (e j).1 (e j).2 • b (e j).1 (e j).2 = ∑ τ, ∑ i, a τ i • b τ i := by
    intro a
    rw [e.sum_comp (fun p : Σ τ : J, Fin (m τ) => a p.1 p.2 • b p.1 p.2), Fintype.sum_sigma]
  have key' : ∀ a : Fin g → S,
      ∑ j, a j • b (e j).1 (e j).2 = ∑ τ, ∑ i, a (e.symm ⟨τ, i⟩) • b τ i := by
    intro a
    rw [← key (fun τ i => a (e.symm ⟨τ, i⟩))]
    simp
  have hmem : ∀ τ (a : Fin (m τ) → S), ∑ i, a i • b τ i ∈ M τ := fun τ a =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hb τ i)
  constructor
  · intro h n
    obtain ⟨f, ⟨hf, hfn⟩, hu⟩ := hs n
    choose a ha hau using fun τ => h τ (f τ) (hf τ)
    refine ⟨fun j => a (e j).1 (e j).2, ?_, ?_⟩
    · change n = ∑ j, a (e j).1 (e j).2 • b (e j).1 (e j).2
      rw [key, ← hfn]
      exact Finset.sum_congr rfl fun τ _ => ha τ
    · intro a' ha'
      rw [key'] at ha'
      have h1 := hu (fun τ => ∑ i, a' (e.symm ⟨τ, i⟩) • b τ i) ⟨fun τ => hmem τ _, ha'.symm⟩
      funext j
      have h2 := hau (e j).1 (fun i => a' (e.symm ⟨(e j).1, i⟩)) (congrFun h1 (e j).1).symm
      have h3 := congrFun h2 (e j).2
      simpa using h3
  · intro h τ n hn
    obtain ⟨a', ha', hu'⟩ := h n
    have hA : ∀ a : Fin (m τ) → S, n = ∑ i, a i • b τ i →
        (fun j => (Pi.single τ a : ∀ σ, Fin (m σ) → S) (e j).1 (e j).2) = a' := by
      intro a ha
      apply hu'
      change n = ∑ j, (Pi.single τ a : ∀ σ, Fin (m σ) → S) (e j).1 (e j).2 • b (e j).1 (e j).2
      rw [key, Finset.sum_eq_single τ]
      · simpa using ha
      · intro σ _ hσ
        simp [Pi.single_eq_of_ne hσ]
      · simp
    refine ⟨fun i => a' (e.symm ⟨τ, i⟩), ?_, ?_⟩
    · have ha2 : n = ∑ j, a' j • b (e j).1 (e j).2 := ha'
      rw [key'] at ha2
      have h1 := (hs n).unique (y₁ := fun τ => ∑ i, a' (e.symm ⟨τ, i⟩) • b τ i)
        (y₂ := Pi.single τ n) ⟨fun τ => hmem τ _, ha2.symm⟩ ⟨fun σ => by
          by_cases hσ : σ = τ
          · subst hσ; simpa using hn
          · simp [Pi.single_eq_of_ne hσ], by simp⟩
      have h2 := congrFun h1 τ
      simpa using h2.symm
    · intro a ha
      funext i
      have h1 := congrFun (hA a ha) (e.symm ⟨τ, i⟩)
      rw [← h1, Equiv.apply_symm_apply]
      simp

theorem eigBasis_iff_tanBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (x : Sp S ⟶ Xo.X) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), (∀ τ i, IsTanAt x (u τ i)) → (∀ τ i, IsEigAt c τ (u τ i)) → ((∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → S, IsCombAt x (u τ) a w) ↔ TanBasis x (fun j => u (e j).1 (e j).2)) := by
  intro E _ _ _ H Dw l Xo c S _ _ x u g e ht he
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, hρ, hsm⟩ := _root_.GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S x
  choose b hb using fun τ i => (htan (u τ i)).1 (ht τ i)
  obtain rfl : u = fun τ i => v (b τ i) := by funext τ i; exact (hb τ i).symm
  let M : (E →+* ℂ) → Submodule S N := fun τ =>
    ⨅ a : 𝓞 E, Module.End.eigenspace (ρ a) (algebraMap c.F S (embK c τ a))
  have hM : ∀ τ n, n ∈ M τ ↔ ∀ a, ρ a n = algebraMap c.F S (embK c τ a) • n := by
    intro τ n
    simp only [M, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  have hE : ∀ τ n, IsEigAt c τ (v n) ↔ n ∈ M τ := by
    intro τ n
    rw [hM]
    refine forall_congr' fun a => ?_
    rw [← hρ, ← hsm, hinj.eq_iff]
  have hs : ∀ n : N, ∃! f : (E →+* ℂ) → N, (∀ τ, f τ ∈ M τ) ∧ ∑ τ, f τ = n := by
    intro n
    simp only [hM]
    exact _root_.GlobalTheory.Frames.existsUnique_eigen_sum E H l c S N ρ n
  have hmain := basis_iff_of_split (fun τ => Dw.mult τ) M hs b (fun τ i => (hE τ _).1 (he τ i)) g e
  have hT : ∀ n, IsTanAt x (v n) := fun n => (htan _).2 ⟨n, rfl⟩
  have hC : ∀ (k : ℕ) (b : Fin k → N) (a : Fin k → S) (n : N),
      IsCombAt x (fun i => v (b i)) a (v n) ↔ n = ∑ i, a i • b i := by
    intro k b a n
    rw [hcomb, hinj.eq_iff]
  constructor
  · intro h
    refine ⟨fun j => hT _, fun w hw => ?_⟩
    obtain ⟨n, rfl⟩ := (htan w).1 hw
    have h1 := hmain.1 (fun τ n hn => by
      have h2 := h τ (v n) (hT n) ((hE τ n).2 hn)
      simpa only [hC] using h2) n
    simpa only [hC] using h1
  · rintro ⟨-, h⟩ τ w hw hew
    obtain ⟨n, rfl⟩ := (htan w).1 hw
    have h1 := hmain.2 (fun n => by
      have h2 := h (v n) (hT n)
      simpa only [hC] using h2) τ n ((hE τ n).1 hew)
    simpa only [hC] using h1

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory

theorem exists_equivariant_fun_on_spanning_families {R M G F : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Group G] [Field F] {r n : ℕ} (hrn : r ≤ n)
    (h0 : ∃ x₀ : Fin r → M, Submodule.span R (Set.range x₀) = ⊤)
    (h1 : ∀ x x' : Fin r → M, Submodule.span R (Set.range x) = ⊤ → Submodule.span R (Set.range x') = ⊤ →
      ∃! g : M ≃ₗ[R] M, ∀ b, g (x b) = x' b)
    (adj : (M ≃ₗ[R] M) → G) (hadj : ∀ g g', adj (g * g') = adj g' * adj g) (ψ : G →* Fˣ) :
    ∃ (ph : (Fin n → M) → F) (x₀ : Fin n → M),
      (∀ x x' : Fin n → M, (∀ b : Fin n, b.val < r → x b = x' b) → ph x = ph x') ∧
      (∀ x, ph x ≠ 0 → Submodule.span R (x '' {b | b.val < r}) = ⊤) ∧
      (∀ (kst : M ≃ₗ[R] M) x, ph (fun b => kst (x b)) = (((ψ (adj kst))⁻¹ : Fˣ) : F) * ph x) ∧
      ph x₀ = 1 ∧ Submodule.span R (x₀ '' {b | b.val < r}) = ⊤ := by
  classical
  obtain ⟨y, hy⟩ := h0
  have himg : ∀ x : Fin n → M, x '' {b | b.val < r} = Set.range (fun b : Fin r => x (Fin.castLE hrn b)) := by
    intro x
    ext m
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b.val, hb⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨Fin.castLE hrn b, b.2, rfl⟩
  have hadj1 : adj 1 = 1 := by
    have := hadj 1 1
    rw [mul_one] at this
    exact (mul_eq_left.mp this.symm)
  let f : (Fin r → M) → F := fun z =>
    if h : Submodule.span R (Set.range z) = ⊤ then (((ψ (adj (h1 y z hy h).exists.choose))⁻¹ : Fˣ) : F) else 0
  have hf : ∀ (z : Fin r → M) (g : M ≃ₗ[R] M), Submodule.span R (Set.range z) = ⊤ → (∀ b, g (y b) = z b) →
      f z = (((ψ (adj g))⁻¹ : Fˣ) : F) := by
    intro z g hz hg
    have : (h1 y z hy hz).exists.choose = g :=
      (h1 y z hy hz).unique (h1 y z hy hz).exists.choose_spec hg
    simp only [f, dif_pos hz, this]
  have hspan : ∀ (z : Fin r → M) (k : M ≃ₗ[R] M), Submodule.span R (Set.range z) = ⊤ →
      Submodule.span R (Set.range fun b => k (z b)) = ⊤ := by
    intro z k hz
    have e : (Set.range fun b => k (z b)) = (k : M →ₗ[R] M) '' Set.range z := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, hz, Submodule.map_top, LinearEquiv.range]
  let x₀ : Fin n → M := fun b => if h : b.val < r then y ⟨b.val, h⟩ else 0
  have hx₀ : (fun b : Fin r => x₀ (Fin.castLE hrn b)) = y := by
    funext b
    simp [x₀]
  refine ⟨fun x => f (fun b => x (Fin.castLE hrn b)), x₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro x x' h
    have : (fun b : Fin r => x (Fin.castLE hrn b)) = fun b => x' (Fin.castLE hrn b) :=
      funext fun b => h _ b.2
    simp only [this]
  · intro x hx
    rw [himg]
    by_contra hz
    exact hx (by simp only [f, dif_neg hz])
  · intro k x
    set z : Fin r → M := fun b => x (Fin.castLE hrn b) with hzdef
    change f (fun b => k (z b)) = _ * f z
    by_cases hz : Submodule.span R (Set.range z) = ⊤
    · obtain ⟨g, hg, -⟩ := h1 y z hy hz
      rw [hf z g hz hg, hf _ (k * g) (hspan z k hz) (fun b => by simp [hg b]), hadj, map_mul, mul_inv,
        Units.val_mul, mul_comm]
    · have hz' : ¬ Submodule.span R (Set.range fun b => k (z b)) = ⊤ := by
        intro h
        have := hspan _ k.symm h
        simp only [LinearEquiv.symm_apply_apply] at this
        exact hz this
      simp only [f, dif_neg hz, dif_neg hz', mul_zero]
  · change f (fun b : Fin r => x₀ (Fin.castLE hrn b)) = 1
    rw [hx₀, hf y 1 hy (fun b => rfl), hadj1]
    simp
  · rw [himg, hx₀, hy]

theorem exists_phiPin_of_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → Dw.p + Dw.q ≤ n → ∀ ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ, ∃ (φ : (Fin n → LevQ Dw d.l₂) → c.F) (ph : (Fin n → LaJ Xo c d) → c.F) (x₀ : Fin n → LaJ Xo c d), DeltaDat.PhiPin { d with φδ := φ } ph ψ x₀ := by
  intro E _ _ _ H Dw l Xo c n d hd hn ψ
  obtain ⟨h0, h1, adj, hadj, hiff⟩ := GlobalTheory.HalfPairing.halves_free_and_adjoint E H Dw l Xo c n d hd
  obtain ⟨ph, x₀, ha, hb, hc, hd1, hd2⟩ :=
    exists_equivariant_fun_on_spanning_families hn h0 h1 adj hadj ψ
  refine ⟨fun q => d.eF.symm (∑ᶠ x : Fin n → LaJ Xo c d, d.eF (ph x) *
      ((⟨zeta d.l₂.M', d.c₂.zeta_mem⟩ : d.c₂.F) ^ (d.l₂.M' / d.pd)) ^
        (∑ b, Dw.EF (qRep (x b)) (cHalf H d.I • levRep (q b)))), ph, x₀, ha, hb, ?_, hd1, hd2, ?_⟩
  · intro k kst h x
    have := (hiff k kst).mp h
    subst this
    exact hc kst x
  · intro q
    exact d.eF.apply_symm_apply _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

section

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem exists_mulEquiv_of_isGrpPullback (h : IsGrpPullback G' G f φ) {X : Scheme.{0}} (a : X ⟶ S') (b : X ⟶ S)
    (hb : b = a ≫ f) :
    ∃ e : (Over.mk a ⟶ G') ≃* (Over.mk b ⟶ G), ∀ x, (e x).left = x.left ≫ φ := by
  subst hb
  let ρ : (Over.mk a ⟶ G') →* (Over.mk (a ≫ f) ⟶ G) :=
    MonoidHom.mk' (pushPt h.1.w) fun x y => Over.OverMorphism.ext (h.2 (Over.mk a) x y _ _ rfl rfl).symm
  have hρ : ∀ x, (ρ x).left = x.left ≫ φ := fun _ => rfl
  refine ⟨MulEquiv.ofBijective ρ ⟨fun x y hxy => ?_, fun y => ?_⟩, hρ⟩
  · refine Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w x).trans (Over.w y).symm))
    exact (hρ x).symm.trans ((congrArg (fun z => z.left) hxy).trans (hρ y))
  · exact ⟨Over.homMk (h.1.lift y.left a (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext ((hρ _).trans (h.1.lift_fst _ _ _))⟩

variable {k : Type} [Field k]

theorem spMap_epsScale_comp_algebraMap (c : k) :
    spMap (epsScale c) ≫ spMap (algebraMap k (DualNumber k)) = spMap (algebraMap k (DualNumber k)) := by
  rw [← Spec.map_comp]
  congr 1
  ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]

theorem spMap_fstHom_comp_algebraMap :
    spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 (Sp k) := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1

theorem lieMult_iff_of_isGrpPullback (h : IsGrpPullback G' G f φ) {O : Type} [CommRing O] (act' : OAct O G')
    (act : OAct O G) (hact : ∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) (x : Sp k ⟶ S') (τ : O →+* k)
    (n : ℕ) : LieMult act' x τ n ↔ LieMult act (x ≫ f) τ n := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback h (spMap (algebraMap k (DualNumber k)) ≫ x)
    (spMap (algebraMap k (DualNumber k)) ≫ x ≫ f) (Category.assoc _ _ _).symm
  obtain ⟨e₀, he₀⟩ := exists_mulEquiv_of_isGrpPullback h x (x ≫ f) rfl
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ G').left ≫ φ := by
    rw [← he₀, map_one]
  have scale : ∀ (c : k) (u v : epsPt x ⟶ G'),
      u.left = spMap (epsScale c) ≫ v.left ↔ (e u).left = spMap (epsScale c) ≫ (e v).left := by
    intro c u v
    rw [he, he, ← Category.assoc]
    refine ⟨fun huv => congrArg (· ≫ φ) huv, fun huv => h.1.hom_ext huv ?_⟩
    refine (Over.w u).trans (Eq.symm ?_)
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w v)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) (spMap_epsScale_comp_algebraMap c))
  have eact : ∀ (a : O) (v : epsPt x ⟶ G'), e (v ≫ act'.act a) = e v ≫ act.act a := by
    intro a v
    refine Over.OverMorphism.ext ?_
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc]
  have eig : ∀ v : epsPt x ⟶ G', IsLieEigen act' x τ v ↔ IsLieEigen act (x ≫ f) τ (e v) := by
    intro v
    refine and_congr ?_ (forall_congr' fun a => by rw [scale, eact])
    rw [he, one, ← Category.assoc]
    refine ⟨fun hv => by rw [hv], fun hv => h.1.hom_ext hv ?_⟩
    refine Eq.trans ?_ (Over.w (1 : Over.mk x ⟶ G')).symm
    refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w v)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ x) spMap_fstHom_comp_algebraMap).trans (Category.id_comp _))
  have prod : ∀ u : Fin n → (epsPt x ⟶ G'), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := by
    intro u
    rw [map_list_prod, List.map_ofFn]
    rfl
  have key : ∀ (v : Fin n → (epsPt x ⟶ G')) (w : epsPt x ⟶ G') (c : Fin n → k),
      (∃ u : Fin n → (epsPt x ⟶ G'),
        (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod) ↔
      ∃ u : Fin n → (epsPt (x ≫ f) ⟶ G),
        (∀ i, (u i).left = spMap (epsScale (c i)) ≫ (e (v i)).left) ∧ e w = (List.ofFn u).prod := by
    intro v w c
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => e (u i), fun i => (scale _ _ _).1 (hu i), prod u⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => e.symm (u i), fun i => (scale _ _ _).2 ?_, e.injective ?_⟩
      · rw [e.apply_symm_apply]; exact hu i
      · rw [prod, hw]
        simp only [e.apply_symm_apply]
  constructor
  · rintro ⟨v, hv, hw⟩
    refine ⟨fun i => e (v i), fun i => (eig _).1 (hv i), fun w hw' => ?_⟩
    obtain ⟨w, rfl⟩ := e.surjective w
    exact (existsUnique_congr (key v w)).1 (hw w ((eig w).2 hw'))
  · rintro ⟨v, hv, hw⟩
    obtain ⟨v, rfl⟩ : ∃ v' : Fin n → (epsPt x ⟶ G'), v = fun i => e (v' i) :=
      ⟨fun i => e.symm (v i), funext fun i => (e.apply_symm_apply _).symm⟩
    exact ⟨v, fun i => (eig _).2 (hv i), fun w hw' => (existsUnique_congr (key v w)).2 (hw _ ((eig w).1 hw'))⟩

end

theorem detCond_iff_of_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S), Nonempty (SABMap t' t f) →
    ∀ (k : Type) [Field k] (x : Sp k ⟶ S') (ρ : k), DetCond D t'.act x ρ ↔ DetCond D t.act (x ≫ f) ρ := by
  rintro E _ _ _ H D S S' t t' f ⟨m⟩ k _ x ρ
  refine forall_congr' fun τ => ?_
  rw [lieMult_iff_of_isGrpPullback m.cart t'.act t.act m.act x τ D.p,
    lieMult_iff_of_isGrpPullback m.cart t'.act t.act m.act x τ D.q]

end GlobalTheory
end
end

