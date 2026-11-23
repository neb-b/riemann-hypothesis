module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0024
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagChartGenericField
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem inChart_flagCoord_ratios : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (S : Type) [Fintype S] (r n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (p' : Cpt ξ') (c₁ : κ) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)), InChart ξ' (flagCoord κ x φ c) ((c₁, J) : FlagIx κ n r) p' → algebraMap Ω (GenField Ω r) (x c₁) ≠ 0 ∧ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p' ∧ ∀ q : Σ s, Fin (r s), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ≠ 0 ∧ ∀ l j, ((flagMat φ c q.1).submatrix (Function.update (J q) l j) (Fin.castLE q.2.2)).det / ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ∈ regAt ξ' p' := by
  intro Ω _ E _ _ κ x S _ r n φ c X' ξ' p' c₁ J h
  classical
  simp only [InChart] at h ⊢
  obtain ⟨hne, hreg⟩ := h
  have hF : ∀ (k : κ) (J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      flagCoord κ x φ c ((k, J') : FlagIx κ n r) = algebraMap Ω (GenField Ω r) (x k) *
        ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J' q) (Fin.castLE q.2.2)).det :=
    fun _ _ => rfl
  rw [hF] at hne
  have hx : algebraMap Ω (GenField Ω r) (x c₁) ≠ 0 := left_ne_zero_of_mul hne
  have hP : ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (J q) (Fin.castLE q.2.2)).det ≠ 0 :=
    right_ne_zero_of_mul hne
  refine ⟨hx, ⟨hx, fun k => ?_⟩, fun q => ⟨?_, fun l j => ?_⟩⟩
  · have hq := hreg ((k, J) : FlagIx κ n r)
    rw [hF, hF] at hq
    rwa [mul_div_mul_right _ _ hP] at hq
  · exact (Finset.prod_ne_zero_iff.mp hP) q (Finset.mem_univ q)
  · have hsplit : ∀ J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1),
        ∏ q' : (Σ s, Fin (r s)), ((flagMat φ c q'.1).submatrix (J' q') (Fin.castLE q'.2.2)).det =
        ((flagMat φ c q.1).submatrix (J' q) (Fin.castLE q.2.2)).det *
          ∏ q' ∈ Finset.univ.erase q, ((flagMat φ c q'.1).submatrix (J' q') (Fin.castLE q'.2.2)).det := by
      intro J'
      rw [← Finset.mul_prod_erase Finset.univ
        (fun q' : (Σ s, Fin (r s)) => ((flagMat φ c q'.1).submatrix (J' q') (Fin.castLE q'.2.2)).det)
        (Finset.mem_univ q)]
    have hrest : ∏ q' ∈ Finset.univ.erase q,
          ((flagMat φ c q'.1).submatrix (Function.update J q (Function.update (J q) l j) q')
            (Fin.castLE q'.2.2)).det =
        ∏ q' ∈ Finset.univ.erase q, ((flagMat φ c q'.1).submatrix (J q') (Fin.castLE q'.2.2)).det :=
      Finset.prod_congr rfl fun q' hq' => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hq')]
    have hR : ∏ q' ∈ Finset.univ.erase q,
        ((flagMat φ c q'.1).submatrix (J q') (Fin.castLE q'.2.2)).det ≠ 0 := by
      intro h0
      apply hP
      rw [hsplit J, h0, mul_zero]
    have hq := hreg ((c₁, Function.update J q (Function.update (J q) l j)) : FlagIx κ n r)
    rw [hF, hF, hsplit (Function.update J q (Function.update (J q) l j)), hsplit J, hrest,
      Function.update_self] at hq
    rwa [mul_div_mul_left _ _ hx, mul_div_mul_right _ _ hR] at hq

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameChangeByUnitMatrix
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem adjugate_entry_mem {Ω : Type} [Field Ω] (R : Subring Ω) {r : ℕ}
    (P : Matrix (Fin r) (Fin r) Ω) (hP : ∀ a b, P a b ∈ R) (i j : Fin r) :
    P.adjugate i j ∈ R := by
  let P' : Matrix (Fin r) (Fin r) R := fun a b => ⟨P a b, hP a b⟩
  have hPP : P = (R.subtype).mapMatrix P' := by
    ext a b
    rfl
  rw [hPP, ← RingHom.map_adjugate]
  exact (P'.adjugate i j).2

theorem linearIndependent_matrix_comb {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
    {β : Fin r → E} (hβ : LinearIndependent Ω β) (P : Matrix (Fin r) (Fin r) Ω) (hd : P.det ≠ 0) :
    LinearIndependent Ω (fun k => ∑ a, P a k • β a) := by
  rw [Fintype.linearIndependent_iff] at hβ ⊢
  intro g hg
  have h1 : ∀ a, ∑ k, P a k * g k = 0 := by
    apply hβ
    refine Eq.trans ?_ hg
    simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm]
  have h2 : Matrix.mulVec P g = 0 := by
    funext a
    exact h1 a
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hd h2
  intro i
  rw [h3]
  rfl

theorem span_matrix_comb {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] (R : Subring Ω) {r : ℕ}
    (β : Fin r → E) (P : Matrix (Fin r) (Fin r) Ω) (hP : ∀ a b, P a b ∈ R) (hd : P.det ≠ 0)
    (hdi : P.det⁻¹ ∈ R) :
    Submodule.span R (Set.range fun k => ∑ a, P a k • β a) = Submodule.span R (Set.range β) := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro k
    show ∑ a, P a k • β a ∈ Submodule.span R (Set.range β)
    refine sum_mem fun a _ => ?_
    exact Submodule.smul_mem _ (⟨P a k, hP a k⟩ : R) (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le, Set.range_subset_iff]
    intro b
    show β b ∈ Submodule.span R (Set.range fun k => ∑ a, P a k • β a)
    have hm : ∀ a, ∑ k, P a k * P.adjugate k b = (P * P.adjugate) a b := fun a =>
      (Matrix.mul_apply).symm
    have hdet : ∑ k, P.adjugate k b • ∑ a, P a k • β a = P.det • β b := by
      calc ∑ k, P.adjugate k b • ∑ a, P a k • β a
          = ∑ a, (∑ k, P a k * P.adjugate k b) • β a := by
            simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
            rw [mul_comm]
        _ = ∑ a, (P * P.adjugate) a b • β a := by
            simp only [hm]
        _ = P.det • β b := by
            rw [Matrix.mul_adjugate]
            simp [Matrix.one_apply]
    have key : β b = ∑ k, (P.det⁻¹ * P.adjugate k b) • ∑ a, P a k • β a := by
      simp only [← smul_smul, ← Finset.smul_sum]
      rw [hdet, smul_smul, inv_mul_cancel₀ hd, one_smul]
    rw [key]
    refine sum_mem fun k _ => ?_
    exact Submodule.smul_mem _
      (⟨P.det⁻¹ * P.adjugate k b, R.mul_mem hdi (adjugate_entry_mem R P hP k b)⟩ : R)
      (Submodule.subset_span ⟨k, rfl⟩)

theorem isFrameAt_matrix_comb : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (β : Fin r → E) (q : Cpt ξ)
    (P : Matrix (Fin r) (Fin r) Ω), L.IsFrameAt β q → (∀ a b, P a b ∈ regAt ξ q) → unitAt ξ q P.det →
    L.IsFrameAt (fun k => ∑ a, P a k • β a) q := by
  intro X Ω _ ξ E _ _ L r β q P h1 h2 h3
  obtain ⟨hli, hspan⟩ := h1
  obtain ⟨hne, -, hinv⟩ := h3
  show LinearIndependent Ω (fun k => ∑ a, P a k • β a) ∧
    L q = Submodule.span (regAt ξ q) (Set.range fun k => ∑ a, P a k • β a)
  refine ⟨linearIndependent_matrix_comb hli P hne, ?_⟩
  rw [hspan]
  exact (span_matrix_comb (regAt ξ q) β P h2 hne hinv).symm

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoeffsRegularInChart
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

theorem twist_left_inverse : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (m n r : ℕ) (φ : Fin n → Module.Dual Ω E),
    IsTwistGen ξ x L m φ → ∀ (p : Cpt ξ) (c₁ : κ), InChart ξ x c₁ p → ∀ β : Fin r → E, L.IsFrameAt β p →
    ∃ B : Matrix (Fin r) (Fin n) Ω, (∀ a j, B a j ∈ regAt ξ p) ∧ (∀ j a, φ j (β a) / x c₁ ^ m ∈ regAt ξ p) ∧
      B * Matrix.of (fun j a => φ j (β a) / x c₁ ^ m) = 1 := by
  intro X Ω _ ξ E _ _ κ x L m n r φ hT p c₁ hc β hβ
  have hβmem : ∀ a, β a ∈ L p := fun a => by
    rw [hβ.2]
    exact Submodule.subset_span ⟨a, rfl⟩
  have hw : ∀ a : Fin r, ∃ w : Module.Dual Ω E, ∀ b, w (β b) = if a = b then 1 else 0 := by
    intro a
    obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hβ.1).coord a)
    refine ⟨g, fun b => ?_⟩
    have h1 : g (β b) = ((Module.Basis.span hβ.1).coord a) ((Module.Basis.span hβ.1) b) := by
      rw [← hg, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply]
    rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self]
    by_cases h : a = b
    · subst h
      simp
    · simp [Finsupp.single_apply, h, Ne.symm h]
  choose w hw using hw
  have hwR : ∀ a, ∀ e ∈ L p, w a e ∈ regAt ξ p := by
    intro a e he
    rw [hβ.2] at he
    induction he using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      rw [hw]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add y z _ _ hy hz =>
      rw [map_add (f := _)]
      exact add_mem hy hz
    | smul s y _ hy =>
      rw [Subring.smul_def, map_smul, smul_eq_mul]
      exact mul_mem s.2 hy
  have hg := fun a => hT.2 p c₁ hc (w a) (hwR a)
  choose g hgR hgw using hg
  refine ⟨Matrix.of fun a j => g a j, fun a j => hgR a j, fun j a => hT.1 j p c₁ hc (β a) (hβmem a), ?_⟩
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.of_apply]
  rw [← hgw a (β b) (hβmem b), hw]

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameNearGenericPoint
section
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen

theorem mem_regAt_genPt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hξ : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ (⟨genPt ξ, specializes_rfl⟩ : Cpt ξ) := by
  obtain ⟨g, hg⟩ := hξ.bij.2 a
  refine ⟨g, ?_⟩
  have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  show (X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫
    Scheme.stalkClosedPointTo ξ).hom g = a
  rw [e]
  exact hg

theorem exists_open_forall_mem_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hξ : IsCptGen ξ) (S : Finset Ω) :
    ∃ W : X.Opens, genPt ξ ∈ W ∧ ∀ q : Cpt ξ, q.1 ∈ W → ∀ a ∈ S, a ∈ regAt ξ q := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨⊤, trivial, fun _ _ _ h => absurd h (Finset.notMem_empty _)⟩
  | insert a S _ ih =>
    obtain ⟨W, hW, H⟩ := ih
    obtain ⟨U, hU, HU⟩ := exists_open_mem_regAt ξ ⟨genPt ξ, specializes_rfl⟩ a (mem_regAt_genPt hξ a)
    refine ⟨W ⊓ U, ⟨hW, hU⟩, fun q hq c hc => ?_⟩
    rcases Finset.mem_insert.1 hc with rfl | hc
    · exact HU q hq.2
    · exact H q hq.1 c hc

theorem span_regAt_le {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ} (q : Cpt ξ) (b e : Fin r → E) (M : Fin r → Fin r → Ω)
    (hM : ∀ i, ∑ j, M i j • e j = b i) (hreg : ∀ i j, M i j ∈ regAt ξ q) :
    Submodule.span (regAt ξ q) (Set.range b) ≤ Submodule.span (regAt ξ q) (Set.range e) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  rw [← hM i]
  refine sum_mem fun j _ => ?_
  exact Submodule.smul_mem _ (⟨M i j, hreg i j⟩ : regAt ξ q) (Submodule.subset_span ⟨j, rfl⟩)

theorem isFrameAt_near_genPt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E) (b : Fin r → E), IsCptGen ξ → (⟨genPt ξ, specializes_rfl⟩ : Cpt ξ) ∈ T → L.IsVBOn T r V → LinearIndependent Ω b → Submodule.span Ω (Set.range b) = V → ∃ W : X.Opens, genPt ξ ∈ W ∧ ∀ q ∈ T, q.1 ∈ W → L.IsFrameAt b q := by
  classical
  intro X Ω _ ξ E _ _ L T r V b hξ hT hVB hb hspan
  obtain ⟨U, hU, e, he, hfr⟩ := hVB _ hT
  have hbe : ∀ i, ∃ c : Fin r → Ω, ∑ j, c j • e j = b i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (he ▸ hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
  have heb : ∀ i, ∃ c : Fin r → Ω, ∑ j, c j • b j = e i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (hspan ▸ he ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose M hM using hbe
  choose N hN using heb
  let S : Finset Ω := Finset.univ.image (fun ij : Fin r × Fin r => M ij.1 ij.2) ∪
    Finset.univ.image (fun ij : Fin r × Fin r => N ij.1 ij.2)
  obtain ⟨W, hW, H⟩ := exists_open_forall_mem_regAt hξ S
  refine ⟨U ⊓ W, ⟨hU, hW⟩, fun q hq hqW => ⟨hb, ?_⟩⟩
  have hMr : ∀ i j, M i j ∈ regAt ξ q := fun i j => H q hqW.2 _
    (Finset.mem_union_left _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))
  have hNr : ∀ i j, N i j ∈ regAt ξ q := fun i j => H q hqW.2 _
    (Finset.mem_union_right _ (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))
  rw [(hfr q hq hqW.1).2]
  exact le_antisymm (span_regAt_le q e b N hN hNr) (span_regAt_le q b e M hM hMr)

end GlobalTheory.CompanionTheory.Ar.Flat.FrameOpen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameViaTwistedGenerators
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

theorem regAt_generic_eq_top {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hg : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨s, hs⟩ := hg.bij.2 a
  refine (RingHom.mem_range).2 ⟨s, ?_⟩
  show (X.presheaf.stalkSpecializes (specializes_refl (genPt ξ)) ≫ Scheme.stalkClosedPointTo ξ).hom s = a
  rw [TopCat.Presheaf.stalkSpecializes_refl]
  exact hs

theorem exists_leftInverse_flagForms (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (L : Lat ξ E) (r : ℕ)
    (V : Submodule Ω E) (m n : ℕ) (φ : Fin n → Module.Dual Ω E) (c : Fin r → E)
    (hT : CoordTie ℤ ξ x) (hV : L.IsVB r V) (hG : IsTwistGen ξ x L m φ)
    (hc : LinearIndependent Ω c) (hs : Submodule.span Ω (Set.range c) = V) :
    ∃ B : Matrix (Fin r) (Fin n) Ω, B * Matrix.of (fun j l => φ j (c l)) = 1 := by
  let p₀ : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  have hreg : ∀ a : Ω, a ∈ regAt ξ p₀ := fun a => regAt_generic_eq_top hT.gen a
  obtain ⟨k, hk⟩ := hT.cover p₀
  unfold Lat.IsVB Lat.IsVBOn at hV
  obtain ⟨U, hU, b, hbV, hbF⟩ := hV p₀ (Set.mem_univ _)
  obtain ⟨-, hLp⟩ := hbF p₀ (Set.mem_univ _) hU
  obtain ⟨-, hG2⟩ := hG
  have hw0 : ∀ i : Fin r, ∃ w : Module.Dual Ω E, ∀ l, w (c l) = if i = l then 1 else 0 := by
    intro i
    obtain ⟨w, hwf⟩ := LinearMap.exists_extend ((Module.Basis.span hc).coord i)
    refine ⟨w, fun l => ?_⟩
    have h1 : w (c l) = (Module.Basis.span hc).coord i (Module.Basis.span hc l) := by
      rw [← hwf]
      simp [Module.Basis.span_apply]
    rw [h1, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = l
    · subst h
      simp
    · simp [h, Ne.symm h]
  choose w hw using hw0
  have hg0 : ∀ i, ∃ g : Fin n → Ω, (∀ j, g j ∈ regAt ξ p₀) ∧
      ∀ e ∈ L p₀, w i e = ∑ j, g j * (φ j e / x k ^ m) :=
    fun i => hG2 p₀ k hk (w i) (fun e _ => hreg _)
  choose g hgr hg using hg0
  have key : ∀ i, ∀ e ∈ V, w i e = ∑ j, g i j / x k ^ m * φ j e := by
    intro i
    obtain ⟨ψ, hψdef⟩ : ∃ ψ : E →ₗ[Ω] Ω, ψ = ∑ j, (g i j / x k ^ m) • φ j := ⟨_, rfl⟩
    have hψ : ∀ e, ψ e = ∑ j, g i j / x k ^ m * φ j e := by
      intro e
      rw [hψdef]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    have heq : Set.EqOn (w i) ψ (Set.range b) := by
      rintro _ ⟨t, rfl⟩
      have hbt : b t ∈ L p₀ := by
        rw [hLp]
        exact Submodule.subset_span ⟨t, rfl⟩
      rw [hg i (b t) hbt, hψ]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    intro e he
    rw [← hbV] at he
    rw [LinearMap.eqOn_span' heq he, hψ]
  refine ⟨Matrix.of fun i j => g i j / x k ^ m, ?_⟩
  ext i l
  have hcl : c l ∈ V := by
    rw [← hs]
    exact Submodule.subset_span ⟨l, rfl⟩
  simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [← key i (c l) hcl, hw i l]

end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FunctionFieldRatioGenerators
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart

theorem exists_eq_div_adjoin (X : Scheme.{0}) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω) (c : κ)
    (hT : CoordTie ℤ ξ x) (hc : x c ≠ 0) (a : Ω) :
    ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c),
      ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c), h ≠ 0 ∧ a = g / h := by
  obtain ⟨U, hU, hUc⟩ := hT.affine c hc
  have hreg0 : ∀ b : Ω, b ∈ regAt ξ ⟨genPt ξ, specializes_refl _⟩ := by
    intro b
    obtain ⟨s, hs⟩ := hT.gen.bij.2 b
    show b ∈ (genMap ξ _).range
    refine RingHom.mem_range.mpr ⟨s, ?_⟩
    simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
    first
      | exact hs
      | (rw [Category.id_comp]; exact hs)
      | simpa using hs
  have hgU : genPt ξ ∈ U :=
    (hUc (genPt ξ)).mpr ⟨specializes_refl _, And.intro hc fun _ => hreg0 _⟩
  let φ : Γ(X, U) →+* Ω := (X.presheaf.germ U (genPt ξ) hgU ≫ Scheme.stalkClosedPointTo ξ).hom
  have key : ∀ r : Γ(X, U), φ r ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
    intro r
    refine (hT.ring c hc (φ r)).mpr fun p hp => ?_
    have hpU : p.1 ∈ U := (hUc p.1).mpr ⟨p.2, hp⟩
    show φ r ∈ (genMap ξ p).range
    refine RingHom.mem_range.mpr ⟨(X.presheaf.germ U p.1 hpU).hom r, ?_⟩
    have e0 : X.presheaf.germ U p.1 hpU ≫ X.presheaf.stalkSpecializes p.2 =
        X.presheaf.germ U (genPt ξ) hgU := by
      first
        | simp
        | exact TopCat.Presheaf.germ_stalkSpecializes X.presheaf hpU p.2
        | exact TopCat.Presheaf.germ_stalkSpecializes hpU p.2
    show (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ).hom
        ((X.presheaf.germ U p.1 hpU).hom r) = φ r
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
    first
      | exact congrArg (fun (m : Γ(X, U) ⟶ CommRingCat.of Ω) => CommRingCat.Hom.hom m r)
          ((reassoc_of% e0) (Scheme.stalkClosedPointTo ξ))
      | (simp only [reassoc_of% e0]; rfl)
  have gres : ∀ {W W' : X.Opens} (hle : W ≤ W') (hw : genPt ξ ∈ W) (z : Γ(X, W')),
      (X.presheaf.germ W (genPt ξ) hw).hom ((X.presheaf.map (homOfLE hle).op).hom z) =
        (X.presheaf.germ W' (genPt ξ) (hle hw)).hom z := by
    intro W W' hle hw z
    have e : X.presheaf.map (homOfLE hle).op ≫ X.presheaf.germ W (genPt ξ) hw =
        X.presheaf.germ W' (genPt ξ) (hle hw) := by
      first
        | simp
        | exact TopCat.Presheaf.germ_res _ _ _ _
    exact congrArg (fun m => m.hom z) e
  obtain ⟨s0, hs0⟩ : ∃ s0 : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom s0 = a :=
    hT.gen.bij.2 a
  obtain ⟨V, hV, f, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf s0
  obtain ⟨t, htV, hgt⟩ := hU.exists_basicOpen_le ⟨genPt ξ, hV⟩ hgU
  have hD : genPt ξ ∈ X.basicOpen t := hgt
  obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen X U hU t
    ((X.presheaf.map (homOfLE htV).op).hom f)
  have hy' : (X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom y =
      ((X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom t) ^ n *
        (X.presheaf.map (homOfLE htV).op).hom f := hy
  have h2 : (X.presheaf.germ U (genPt ξ) hgU).hom y =
      ((X.presheaf.germ U (genPt ξ) hgU).hom t) ^ n * (X.presheaf.germ V (genPt ξ) hV).hom f := by
    have h2' := congrArg (X.presheaf.germ (X.basicOpen t) (genPt ξ) hD).hom hy'
    simp only [map_mul, map_pow, gres] at h2'
    exact h2'
  let ψ : X.presheaf.stalk (genPt ξ) →+* Ω := (Scheme.stalkClosedPointTo ξ).hom
  have hφ : ∀ r, φ r = ψ ((X.presheaf.germ U (genPt ξ) hgU).hom r) := by
    intro r
    first
      | rfl
      | simp [φ, ψ]
  have hs0' : ψ ((X.presheaf.germ V (genPt ξ) hV).hom f) = a := hs0
  have h3 : φ y = φ t ^ n * a := by
    rw [hφ, hφ, h2, map_mul, map_pow, hs0']
  have hunit : IsUnit ((X.presheaf.germ U (genPt ξ) hgU).hom t) :=
    (X.mem_basicOpen t (genPt ξ) hgU).mp hD
  have hφt : φ t ≠ 0 := by
    rw [hφ]
    exact (hunit.map ψ).ne_zero
  refine ⟨φ y, key y, φ (t ^ n), key (t ^ n), ?_, ?_⟩
  · rw [map_pow]
    exact pow_ne_zero _ hφt
  · rw [map_pow]
    exact eq_div_of_mul_eq (pow_ne_zero _ hφt) (by rw [h3]; ring)

end GlobalTheory.CompanionTheory.Ar.FlagBun.FracChart
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodProjExistsStatementHolds
section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem goodProjExistsStatement_holds : ReciprocityTheory.ChartRestriction.G.Geo.GoodProjExistsStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.goodProjExists

end GlobalTheory.CompanionTheory.Ar.Link
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeTensorPowerLineBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_tensor_power_line_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (I : Type) [Fintype I] (Λ : I → Lat ξ Ω) (T : Set (Cpt ξ)), (∀ i, (Λ i).IsVBOn T 1 ⊤) → ∀ a : I → ℤ, (Lat.tens Λ a).IsVBOn T 1 ⊤ ∧ ∀ p ∈ T, ∀ s : I → Ω, (∀ i, (Λ i).IsGenAt p (s i)) → (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LatTens.tens_isVBOn | exact GlobalTheory.CompanionTheory.Ar.LatTens.tens_isVBOn | (intros; apply GlobalTheory.CompanionTheory.Ar.LatTens.tens_isVBOn <;> assumption)
end

