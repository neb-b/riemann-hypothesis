module

public import Mathlib
public import Development.AutomorphicArithmetic.LocalEmbeddings.ArchSz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0617
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0615
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0060

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.HaarVolKOLeResCardPowOfCongruenceLe
section
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel GlobalTheory.ConjSize

open GlobalTheory.FunObj.GivenAdm in
theorem UpperTheory.haarVol_KO_le_resCard_pow_of_congruence_le :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A : Type} [Fintype A] [DecidableEq A] {J : Subgroup (GL A k)}, IsOpen (J : Set (GL A k)) → J ≤ GlobalTheory.SplitWeil.KO k A → ∀ {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) ≤ J → (haarVol J).real (GlobalTheory.SplitWeil.KO k A : Set (GL A k)) ≤ (resCard k : ℝ) ^ (e * Fintype.card A * Fintype.card A) := by
  intro k _ _ _ _ _ _ A _ _ J hJo hJK ϖ e hϖ hN
  classical
  let red : GL A k → Matrix A A (Res k e) := fun g i j =>
    if h : (g : Matrix A A k) i j ∈ 𝒪[k] then Ideal.Quotient.mk (𝓂[k] ^ e) ⟨_, h⟩ else 0
  have key : ∀ g ∈ KO k A, ∀ h ∈ KO k A, red g = red h →
      h⁻¹ * g ∈ glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) := by
    intro g hg h hh hgh
    rw [GlobalTheory.FunObj.GivenAdm.mem_glLatCong]
    refine ⟨mul_mem (inv_mem hh) hg, ?_⟩
    have hg' := (mem_KO_iff g).1 hg
    have hh' := (mem_KO_iff h).1 hh
    have e1 : ((h⁻¹ * g : GL A k) : Matrix A A k) - 1
        = ((h⁻¹ : GL A k) : Matrix A A k) * ((g : Matrix A A k) - (h : Matrix A A k)) := by
      rw [Matrix.mul_sub, Units.val_mul, ← Units.val_mul h⁻¹ h, inv_mul_cancel, Units.val_one]
    rw [e1]
    refine GlobalTheory.FunObj.GivenAdm.CongM.mul_left ?_ (fun i j => hh'.2 i j)
    intro i j
    have hij := congrFun (congrFun hgh i) j
    simp only [red, dif_pos (hg'.1 i j), dif_pos (hh'.1 i j)] at hij
    rw [Ideal.Quotient.eq] at hij
    have hv := (Model.val_le_iff_mem hϖ e _).1 hij
    simpa [Matrix.sub_apply] using hv
  haveI := isHaarMeasure_haarVol hJo hJK
  have hNJ : haarVol J (glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) : Set (GL A k)) ≤ 1 := by
    rw [← haarVol_self hJo hJK]
    exact measure_mono hN
  have piece : ∀ M : Matrix A A (Res k e), haarVol J {g | g ∈ KO k A ∧ red g = M} ≤ 1 := by
    intro M
    by_cases hne : ∃ g0, g0 ∈ KO k A ∧ red g0 = M
    · obtain ⟨g0, hg0, hM⟩ := hne
      calc haarVol J {g | g ∈ KO k A ∧ red g = M}
          ≤ haarVol J ((fun h => g0⁻¹ * h) ⁻¹'
              (glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) : Set (GL A k))) := by
            apply measure_mono
            rintro g ⟨hg, hgM⟩
            exact key g hg g0 hg0 (hgM.trans hM.symm)
        _ = haarVol J (glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) : Set (GL A k)) :=
            measure_preimage_mul _ _ _
        _ ≤ 1 := hNJ
    · calc haarVol J {g | g ∈ KO k A ∧ red g = M} ≤ haarVol J ∅ := by
            apply measure_mono
            intro g hg
            exact absurd ⟨g, hg⟩ hne
        _ = 0 := measure_empty
        _ ≤ 1 := zero_le_one
  have hKO : haarVol J (KO k A : Set (GL A k))
      ≤ (Fintype.card (Matrix A A (Res k e)) : ENNReal) := by
    calc haarVol J (KO k A : Set (GL A k))
        ≤ haarVol J (⋃ M ∈ (Finset.univ : Finset (Matrix A A (Res k e))),
            {g | g ∈ KO k A ∧ red g = M}) := by
          apply measure_mono
          intro g hg
          simp only [Set.mem_iUnion]
          exact ⟨red g, Finset.mem_univ _, hg, rfl⟩
      _ ≤ ∑ M ∈ (Finset.univ : Finset (Matrix A A (Res k e))),
            haarVol J {g | g ∈ KO k A ∧ red g = M} := measure_biUnion_finset_le _ _
      _ ≤ ∑ M ∈ (Finset.univ : Finset (Matrix A A (Res k e))), (1 : ENNReal) :=
          Finset.sum_le_sum (fun M _ => piece M)
      _ = (Fintype.card (Matrix A A (Res k e)) : ENNReal) := by
          simp [Finset.card_univ]
  have hcard : Fintype.card (Matrix A A (Res k e))
      = resCard k ^ (e * Fintype.card A * Fintype.card A) := by
    have h1 : Fintype.card (Matrix A A (Res k e))
        = Fintype.card (Res k e) ^ (Fintype.card A * Fintype.card A) := by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]
      show Nat.card (A → A → Res k e) = _
      rw [Nat.card_fun, Nat.card_fun, ← pow_mul, mul_comm]
    rw [h1, GlobalTheory.FlipMatch.FourierInv.card_res_pow, ← pow_mul, mul_assoc]
  rw [measureReal_def]
  have := ENNReal.toReal_mono (by simp) hKO
  rw [hcard] at this
  simpa using this
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.LocalGridTensorSizeLeOneOfUnimodular
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.ConjSize
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace UpperTheory.IteratedPhiSize

open GlobalTheory.StepData ValuativeRel Formalism.L2.Host GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim MeasureTheory

section Local

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {K : Type} [Field K] (ι τ : K →+* ℂ)

private theorem lam_principal_un {a : Type*} [Fintype a] [DecidableEq a] (g : (TypeDatum.principal k a).J) :
    Un ι τ (((TypeDatum.principal k a).lam g : ℂˣ) : ℂ) := by
  change Un ι τ ((1 : ℂˣ) : ℂ)
  rw [Units.val_one]
  exact Un.one

private theorem lam_reindex_un {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (P : TypeDatum k a)
    (e : a ≃ b) (hP : ∀ g, Un ι τ ((P.lam g : ℂˣ) : ℂ)) (g : (P.reindex e).J) :
    Un ι τ (((P.reindex e).lam g : ℂˣ) : ℂ) :=
  hP _

private theorem lam_step_un {a t : Type*} [Fintype a] [DecidableEq a] [Fintype t] [DecidableEq t] (P : TypeDatum k a)
    (μ : kˣ →* ℂˣ) (hμ : IsTame μ) (hP : ∀ g, Un ι τ ((P.lam g : ℂˣ) : ℂ)) (hμF : ∀ x, Un ι τ ((μ x : ℂˣ) : ℂ))
    (h : (P.step t μ hμ).J) : Un ι τ (((P.step t μ hμ).lam h : ℂˣ) : ℂ) := by
  rw [P.step_lam μ hμ h (P.corner h) (P.corner_val h), Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
  exact ((hP _).mul (hμF _).inv).mul (hμF _)

private theorem lam_iter_un {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hP : ∀ g, Un ι τ ((P.lam g : ℂˣ) : ℂ))
    (hμF : ∀ j x, Un ι τ ((μ j x : ℂˣ) : ℂ)) (j : ℕ) : ∀ g, Un ι τ (((P.iter t μ hμ j).lam g : ℂˣ) : ℂ) := by
  induction j with
  | zero => exact lam_reindex_un ι τ P _ hP
  | succ j ih => exact lam_reindex_un ι τ _ _ (lam_step_un ι τ _ _ _ ih (hμF _))

private theorem Phi_sz {a t : Type*} [Fintype a] [DecidableEq a] (P : TypeDatum k a) (μ : kˣ →* ℂˣ)
    (hP : ∀ g, Un ι τ ((P.lam g : ℂˣ) : ℂ)) (hμF : ∀ x, Un ι τ ((μ x : ℂˣ) : ℂ)) (x : Matrix (a ⊕ t) a k) :
    Sz ι τ (P.Phi t μ x) 1 := by
  by_cases h : P.Phi t μ x = 0
  · rw [h]; exact Sz.zero zero_le_one
  · obtain ⟨⟨g, hg, e⟩, h2⟩ := (P.Phi_ne_zero_iff μ).1 h
    rw [P.Phi_of_mem μ ⟨g, hg⟩ e h2, Units.val_inv_eq_inv_val]
    exact ((hP _).mul (hμF _).inv).sz

private theorem iterPhi_sz {r t : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum k r)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (hP : ∀ g, Un ι τ ((P.lam g : ℂˣ) : ℂ))
    (hμF : ∀ j x, Un ι τ ((μ j x : ℂˣ) : ℂ)) (j : ℕ) (x : Matrix (Ix r t (j + 1)) (Ix r t j) k) :
    Sz ι τ (P.iterPhi t μ hμ j x) 1 :=
  Phi_sz ι τ _ _ (lam_iter_un ι τ P μ hμ hP hμF j) (hμF _) _

private theorem parPhi_sz {r s s' : Type*} [Fintype r] [DecidableEq r] (δ : kˣ →* ℂˣ)
    (hδ : ∀ x, Un ι τ ((δ x : ℂˣ) : ℂ)) (x : Matrix (r ⊕ s) (r ⊕ s') k) : Sz ι τ (parPhi δ x) 1 := by
  by_cases h : parPhi δ x = 0
  · rw [h]; exact Sz.zero zero_le_one
  · obtain ⟨⟨g, hg, e⟩, h21, h12, h22⟩ := (parPhi_ne_zero_iff δ).1 h
    rw [parPhi_of_mem δ hg e h21 h12 h22, Units.val_inv_eq_inv_val]
    exact (hδ _).inv.sz

private theorem indicator_one_sz {X : Type*} (S : Set X) (x : X) : Sz ι τ (S.indicator (1 : X → ℂ) x) 1 := by
  classical
  rw [Set.indicator_apply]
  split_ifs
  · exact Sz.one
  · exact Sz.zero zero_le_one

end Local

section Global

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {K : Type} [Field K] (ι τ : K →+* ℂ)
  (w : Pl D.host.E)

private theorem muBase_un (hmu : ∀ j x, Un ι τ ((L.C.mu0 j).loc w x : ℂ)) (c : ℕ) (x : (Kw w)ˣ) :
    Un ι τ (((muBase L c).loc w x : ℂˣ) : ℂ) := by
  rcases c with _ | c
  · simpa [muBase, HChar.loc] using (Un.one : Un ι τ 1)
  · simp only [muBase]
    split_ifs with h
    · exact hmu _ _
    · simpa [HChar.loc] using (Un.one : Un ι τ 1)

variable {t : T} (hmu : ∀ j x, Un ι τ ((L.C.mu0 j).loc w x : ℂ)) (hxi : ∀ x, Un ι τ ((L.xiH t).loc w x : ℂ))
include hmu hxi

private theorem stepFn_sz (j : ℕ) (x) : Sz ι τ (stepFn L t w j x) 1 := by
  unfold stepFn
  split_ifs
  · refine iterPhi_sz ι τ _ _ _ (lam_principal_un ι τ) (fun c y => ?_) _ _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact (muBase_un ι τ w hmu c y).inv
  · refine parPhi_sz ι τ _ (fun y => ?_) _
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    exact (hxi y).inv
  · exact indicator_one_sz ι τ _ _

private theorem givenDatum_sz (B : Frames G) (Φ : G.Datum) (b : Edge) (x) : Sz ι τ (givenDatum t w B Φ b x) 1 := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩
  · rcases i with _ | i
    · simp only [givenDatum]
      exact stepFn_sz ι τ w hmu hxi _ _
    · simp only [givenDatum]
      exact Sz.zero zero_le_one
  · rcases j with _ | j
    · simp only [givenDatum]
      split_ifs
      · exact indicator_one_sz ι τ _ _
      · exact Sz.zero zero_le_one
    · simp only [givenDatum]
      exact Sz.zero zero_le_one

end Global

end UpperTheory.IteratedPhiSize

theorem UpperTheory.localGrid_tensor_size_le_one_of_unimodular :
    ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {K : Type} [Field K] (ι τ : K →+* ℂ) (B : Frames G) (t : T) (Φ : G.Datum) (w : Pl D.host.E), (∀ j x, Un ι τ ((L.C.mu0 j).loc w x : ℂ)) → (∀ x, Un ι τ ((L.xiH t).loc w x : ℂ)) → ∀ z : (locGrid G t w).Args, Sz ι τ ((givenStage t w B Φ).tensor z) 1 := by
  intro D T L sc G K _ ι τ B t Φ w hmu hxi z
  show Sz ι τ ((GlobalTheory.SplitFlip.givenPath D.R.m).map fun b => givenDatum t w B Φ b (z b)).prod 1
  refine Sz.list_prod fun y hy => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
  exact UpperTheory.IteratedPhiSize.givenDatum_sz ι τ w hmu hxi B Φ b _
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.UnramifiedCharacterInvariant
section
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel GlobalTheory.ConjSize

open scoped Pointwise in
private theorem sum_rightInv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKt : μ K ≠ ⊤) {S : Set G} (hS : IsCompact S)
    (hSK : ∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) :
    ∃ t : Finset (G ⧸ K), (∀ Q ∈ t, Q.out ∈ S) ∧ ∀ f : G → ℂ, (∀ s ∈ S, ∀ k ∈ K, f (s * k) = f s) →
      ∫ g in S, f g ∂μ = ∑ Q ∈ t, f Q.out * μ.real K :=
  _root_.UpperTheory.Reformulated.B.SumRightInverse.sum_rightInv μ K hKo hKt hS hSK

section
variable {k : Type} [Field k] [ValuativeRel k] {A : Type} [Fintype A] [DecidableEq A]

private theorem inv_small (g : GL A k) (c : k)
    (hdet : ∀ y : Matrix A A k, (∀ i j, valuation k (y i j - g.val i j) ≤ valuation k c) → y.det ≠ 0) (i j : A) :
    valuation k ((g⁻¹).val i j) * valuation k c ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  set a := (g⁻¹).val i j with ha
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at hlt; simp at hlt
  have hv0 : 0 < valuation k a := zero_lt_iff.2 (by simpa using ha0)
  have hd : valuation k a⁻¹ ≤ valuation k c := by
    rw [map_inv₀, inv_le_iff_one_le_mul₀' hv0]; exact hlt.le
  refine hdet (g.val - Matrix.single j i a⁻¹) (fun p q => ?_) ?_
  · rw [Matrix.sub_apply, sub_sub_cancel_left, Valuation.map_neg, Matrix.single_apply]
    split_ifs
    · exact hd
    · simp
  · rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun l => (g⁻¹).val l j, fun h => ha0 (congrFun h i), ?_⟩
    rw [Matrix.sub_mulVec, Matrix.single_mulVec, ← ha, inv_mul_cancel₀ ha0]
    funext p
    have : (g.val * (g⁻¹).val) p j = (1 : Matrix A A k) p j := by rw [Units.mul_inv]
    rw [Matrix.mul_apply] at this
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, this, Matrix.one_apply, Function.update_apply,
      Pi.zero_apply, sub_self]

private theorem val_sub_le {x y z c : k} (h : valuation k (y - x) ≤ valuation k c)
    (h' : valuation k (z - x) ≤ valuation k c) : valuation k (y - z) ≤ valuation k c := by
  have : y - z = (y - x) - (z - x) := by ring
  rw [this]
  exact ((valuation k).map_sub _ _).trans (max_le h h')

private theorem inv_mul_int (x : Matrix A A k) (c : k)
    (hdet : ∀ y : Matrix A A k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k c) → y.det ≠ 0)
    (g h : GL A k) (hg : ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k c)
    (hh : ∀ i j, valuation k (h.val i j - x i j) ≤ valuation k c) (i j : A) : (g⁻¹ * h).val i j ∈ 𝒪[k] := by
  have e : (g⁻¹ * h).val = 1 + (g⁻¹).val * (h.val - g.val) := by
    rw [Matrix.mul_sub, Units.inv_mul, Units.val_mul, add_sub_cancel]
  have hs := inv_small g c fun y hy => hdet y fun p q =>
    val_sub_le (hy p q) (by rw [Valuation.map_sub_swap]; exact hg p q)
  rw [e, Matrix.add_apply, Matrix.mul_apply]
  refine add_mem ?_ (Subring.sum_mem _ fun l _ => ?_)
  · rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [Valuation.mem_integer_iff, map_mul]
    exact (mul_le_mul_right (val_sub_le (hh l j) (hg l j)) _).trans (hs i l)

end

open scoped Pointwise in
theorem UpperTheory.unramified_character_invariant :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A : Type} [Fintype A] [DecidableEq A] {K : Type} [Field K] (ι τ : K →+* ℂ) {J : Subgroup (GL A k)}, IsOpen (J : Set (GL A k)) → J ≤ GlobalTheory.SplitWeil.KO k A → ∀ (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → CondLE ϖ e ν → (∀ u, Un ι τ (ν u : ℂ)) → (∀ u : kˣ, apow u (1 / 2) ∈ Set.range ι) → ∀ (n : ℕ) (x : Matrix A A k), (∀ i j, valuation k (x i j) ≤ 1) → (∀ y : Matrix A A k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) → y.det ≠ 0) → Sz ι τ (∫ g in {g : GL A k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)}, (ν (gdet g) : ℂ) * apow (gdet g) ((n : ℂ) / 2) ∂(haarVol J)) ((haarVol J).real (GlobalTheory.SplitWeil.KO k A : Set (GL A k))) := by
  intro k _ _ _ _ _ _ A _ _ K _ ι τ J hJo hJK ν ϖ e hϖ hcond hν hap n x hx hdet
  haveI := isHaarMeasure_haarVol hJo hJK
  obtain ⟨hSc, hSo⟩ := GlobalTheory.GLBallInt.isCompact_isOpen_glBall x (ϖ ^ e) hdet
  set S := {g : GL A k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)} with hSdef
  set K' : Subgroup (GL A k) :=
    J ⊓ GlobalTheory.SplitFlip.glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) ⊓ GlobalTheory.GLBallInt.rightStab S with hKdef
  have hKo : IsOpen (K' : Set (GL A k)) := by
    simp only [hKdef, Subgroup.coe_inf]
    exact (hJo.inter (GlobalTheory.FunObj.GivenAdm.isOpen_glLatCong _)).inter (GlobalTheory.GLBallInt.isOpen_rightStab hSc hSo)
  have hKJ : K' ≤ J := inf_le_left.trans inf_le_left
  have hJc : IsCompact (J : Set (GL A k)) := isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJo) hJK
  have hKt : haarVol J K' ≠ ⊤ :=
    ((measure_mono (show (K' : Set (GL A k)) ⊆ J from hKJ)).trans_lt (by simp [haarVol_self hJo hJK])).ne
  have hinv : ∀ s ∈ S, ∀ k' ∈ K', ((ν (gdet (s * k')) : ℂ) * apow (gdet (s * k')) ((n : ℂ) / 2)) =
      (ν (gdet s) : ℂ) * apow (gdet s) ((n : ℂ) / 2) := by
    intro s _ k' hk
    have hu : gdet k' ∈ unitCong (ϖ ^ e) :=
      GlobalTheory.FunObj.GivenAdm.gdet_mem_unitCong (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).1).2
    rw [gdet_mul, map_mul, Units.val_mul, apow_mul, hcond _ hu, apow_of_valuation_eq_one hu.1]
    simp
  obtain ⟨t, htS, ht⟩ := sum_rightInv (haarVol J) K' hKo hKt hSc
    (fun s hs k' hk => ((Subgroup.mem_inf.1 hk).2 s).1 hs)
  rw [ht (fun g => (ν (gdet g) : ℂ) * apow (gdet g) ((n : ℂ) / 2)) hinv]
  have h1 := ht (fun _ => (1 : ℂ)) (fun _ _ _ _ => rfl)
  rw [setIntegral_const, Finset.sum_const, nsmul_eq_mul, one_mul, Complex.real_smul, mul_one] at h1
  have h1' : (haarVol J).real S = t.card * (haarVol J).real K' := by exact_mod_cast h1
  obtain ⟨m, hm⟩ := GlobalTheory.GLBallInt.measureReal_eq_inv_natCast (haarVol J) hJc (haarVol_self hJo hJK) hKo hKJ
  have hϖe : valuation k ((ϖ ^ e : kˣ) : k) ≤ 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_one' (hϖ.trans_lt uniformizer_lt_one).le _
  have hdv : ∀ g ∈ S, valuation k ((gdet g : kˣ) : k) ≤ 1 := by
    intro g hg
    have hint : ∀ i j, g.val i j ∈ 𝒪[k] := fun i j => by
      have : g.val i j = (g.val i j - x i j) + x i j := by ring
      rw [this]
      exact add_mem ((Valuation.mem_integer_iff _ _).2 ((hg i j).trans hϖe))
        ((Valuation.mem_integer_iff _ _).2 (hx i j))
    have : g.val.det ∈ 𝒪[k] := by
      rw [Matrix.det_apply']
      exact Subring.sum_mem _ fun σ _ => mul_mem (intCast_mem _ _) (Subring.prod_mem _ fun i _ => hint _ _)
    exact (Valuation.mem_integer_iff _ _).1 this
  have hsz : Sz ι τ (∑ Q ∈ t, (ν (gdet Q.out) : ℂ) * apow (gdet Q.out) ((n : ℂ) / 2) * ((haarVol J).real K' : ℝ))
      (t.card * (haarVol J).real K') := by
    refine Sz.sum_card t fun Q hQ => ?_
    have h2 := (hν (gdet Q.out)).mul_sz (sz_apow_of_le_one (τ := τ) _ (hap _) n (hdv _ (htS Q hQ)))
    have h3 := h2.mul (Sz.inv_nat (ι := ι) (τ := τ) m)
    rw [hm]
    simpa using h3
  refine hsz.mono ?_
  rw [← h1']
  let x' : GL A k := Matrix.GeneralLinearGroup.mkOfDetNeZero x (hdet x fun i j => by simp)
  have hx' : ∀ i j, valuation k (x'.val i j - x i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) := fun i j => by
    show valuation k (x i j - x i j) ≤ _
    simp
  have hsub : S ⊆ x' • (GlobalTheory.SplitWeil.KO k A : Set (GL A k)) := fun g hg =>
    ⟨x'⁻¹ * g, (mem_KO_iff _).2 ⟨inv_mul_int x _ hdet x' g hx' hg, by
      rw [mul_inv_rev, inv_inv]; exact inv_mul_int x _ hdet g x' hg hx'⟩, by simp⟩
  rw [measureReal_def, measureReal_def]
  refine ENNReal.toReal_mono isCompact_KO.measure_lt_top.ne ?_
  exact (measure_mono hsub).trans (measure_smul _ _ _).le
end

