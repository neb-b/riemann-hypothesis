module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOpenMirabolicConjInfIntegralGLUnipotent
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.UnipLevelTopo

theorem isOpen_inf_isCompact : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A] {c : ℕ} (J : Subgroup (GL (A ⊕ Fin c) k)) (g : GL (A ⊕ Fin c) k), IsOpen (J : Set (GL (A ⊕ Fin c) k)) → IsCompact (J : Set (GL (A ⊕ Fin c) k)) → IsOpen ((((Cgrp J g).subgroupOf (N k A c 1)) ⊓ ((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1)) : Subgroup (N k A c 1)) : Set (N k A c 1)) ∧ IsCompact (((Cgrp J g).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) ∧ IsCompact (((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) := by
  intro k _ _ _ _ A _ _ c J g hJo hJc
  obtain ⟨h1, h2⟩ := isOpen_isCompact_conj g hJo hJc
  have hemb : Topology.IsClosedEmbedding (Subtype.val : N k A c 1 → GL (A ⊕ Fin c) k) :=
    (GlobalTheory.RootEx.VolN.isClosed_N (k := k) (n := A) (c := c) 1).isClosedEmbedding_subtypeVal
  have eC : (((Cgrp J g).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) =
      Subtype.val ⁻¹' (J.comap (MulAut.conj g⁻¹).toMonoidHom : Set (GL (A ⊕ Fin c) k)) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage, Cgrp, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨Subgroup.mem_sup_right x.2, h⟩⟩
  have eK : (((KO k (A ⊕ Fin c)).subgroupOf (N k A c 1) : Subgroup (N k A c 1)) : Set (N k A c 1)) =
      Subtype.val ⁻¹' (KO k (A ⊕ Fin c) : Set (GL (A ⊕ Fin c) k)) := by
    ext x; simp [Subgroup.mem_subgroupOf]
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.coe_inf, eC, eK]
    exact (h1.inter GlobalTheory.SplitFlip.isOpen_KO).preimage continuous_subtype_val
  · rw [eC]; exact hemb.isCompact_preimage h2
  · rw [eK]; exact hemb.isCompact_preimage GlobalTheory.SplitFlip.isCompact_KO

end GlobalTheory.UnipLevelTopo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOpenMirabolicProjectionToGL
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.OpenPr

theorem continuous_embX {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    {A : Type} [Fintype A] [DecidableEq A] (c : ℕ) :
    Continuous (embX c : GL A k → GL (A ⊕ Fin c) k) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GL A k => (fromBlocks (x : Matrix A A k) 0 0 1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k)
    exact (Units.continuous_val).matrix_fromBlocks continuous_const continuous_const continuous_const
  · change Continuous fun x : GL A k => (fromBlocks ((x⁻¹ : GL A k) : Matrix A A k) 0 0 1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k)
    exact (Units.continuous_coe_inv).matrix_fromBlocks continuous_const continuous_const continuous_const

theorem isOpen_prX : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A] {c : ℕ} (Ck : Subgroup (GL (A ⊕ Fin c) k)) (O : Set (GL (A ⊕ Fin c) k)), IsOpen O → (1 : GL (A ⊕ Fin c) k) ∈ O → (∀ z ∈ R k A c 1, z ∈ O → z ∈ Ck) → IsOpen (prX Ck : Set (GL A k)) := by
  intro k _ _ _ _ A _ _ c Ck O hO h1 hCk
  have hc : Continuous (embX c : GL A k → GL (A ⊕ Fin c) k) := continuous_embX c
  have hU : IsOpen ((embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O) := hO.preimage hc
  have h1U : (1 : GL A k) ∈ (embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O := by
    simp only [Set.mem_preimage, map_one]; exact h1
  have hsub : (embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O ⊆ (prX Ck : Set (GL A k)) := by
    intro x hx
    refine ⟨1, one_mem _, ?_⟩
    rw [one_mul]
    exact hCk _ (Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨x, rfl⟩)) hx
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU.mem_nhds h1U) hsub)

end GlobalTheory.OpenPr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastStepTestFunctionsAgreeRationalPoints
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.TopAgree
variable {E K k : Type} [Field E] [NumberField E] [StarRing E] [Field K] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdOrd_top {κ τ s : ℕ} (b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 1)) :
    ∃ b', stdOrd (Fin κ) (Fin τ) (s + 1) 0 rfl b = Sum.inl b' ∧ xPos b' = zPos b := by
  rcases b with (i | i) | p
  · exact ⟨_, stdOrd_eps _ _ _ _ _ i, rfl⟩
  · have h := stdOrd_f (Fin κ) (Fin τ) (s + 1) 0 rfl i
    have e : (⟨0 + i.val, by omega⟩ : Fin (s + 1)) = i := Fin.ext (by simp)
    rw [e] at h
    exact ⟨_, h, rfl⟩
  · exact ⟨_, stdOrd_d _ _ _ _ _ p, rfl⟩

theorem top_entries (q : ℕ) (ι : E →+* k) {s κ : ℕ} (S : SymData k s κ) (τ n' n : ℕ)
    (e' : XIx (Fin κ) (Fin τ) (s + 1) ⊕ Fin 0 ≃ Fin (n' + 0)) (e : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ≃ Fin (n + 0))
    (he' : IsOrd (yPos xPos n') e') (he : IsOrd zPos e) (x : (Fin (n' + 0) → E) →ₗ[E] (Fin (n + 0) → E)) :
    (S.T (Fin τ)).PhiTop (toLoc ι e e' x) = S.P.iterPhi (Fin τ) S.μ S.tame (s + 1)
      (Matrix.of fun a b => ι (LocE.entB q κ 0 n' 0 n (fun i => i + 1) (fun i => i + 1) x (zPos a) (zPos b))) := by
  simp only [SymData.T, typeChain, Chain.ofType, LatFrame.transport, LatFrame.coords]
  congr 1
  have hb : (typeFrame S.ϖ (stdOrd (Fin κ) (Fin τ) (s + 1) 0 rfl)).bas.val = 1 := by
    ext (u | u) (v | v)
    · simp [typeFrame, embA, Matrix.one_apply]
    · exact v.elim0
    · exact u.elim0
    · exact u.elim0
  ext a b
  obtain ⟨b', hb1, hb2⟩ := stdOrd_top (κ := κ) (τ := τ) (s := s) b
  have ha : zPos a < n := by have := (e a).isLt; rw [he a] at this; omega
  have hb' : zPos b < n' := by
    have := (e' (Sum.inl b')).isLt; rw [he' (Sum.inl b')] at this; simp [yPos] at this; omega
  have h1 : ∀ p N, (if p < κ then p else if p < κ + 0 then N + (p - κ) else p - 0) = p := by
    intro p N; split_ifs <;> omega
  rw [hb]
  simp only [LatFrame.refl, Units.val_one, inv_one, Matrix.one_mul, Matrix.mul_one, Matrix.submatrix_apply, id,
    Equiv.refl_apply, Matrix.of_apply, typeFrame, hb1, toLoc, LocE.entB, LocE.fIdx, LocE.scE, h1, if_pos ha, if_pos hb',
    sub_self, zpow_zero, mul_one, Loc.atN, dif_pos (show zPos a < n + 0 from ha)]
  have hv : (Pi.single (e' (Sum.inl b')) 1 : Fin (n' + 0) → E) = Loc.eN E (n' + 0) (zPos b) := by
    funext l
    simp only [Loc.eN, Pi.single_apply, Fin.ext_iff, he' (Sum.inl b'), yPos, Sum.elim_inl, hb2]
  rw [hv, show e a = ⟨zPos a, by omega⟩ from Fin.ext (he a)]

theorem bottom_iff {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ} (hC : IsCompl P q ι ϖ)
    (hU : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (κ l τ j : ℕ) (M : ℕ → ℕ → E) :
    MaxM ((Matrix.of fun a b => ι (M (zPos a) (zPos b)) :
        Matrix (Ix (Fin κ ⊕ Fin l) (Fin τ) (j + 1)) (Ix (Fin κ ⊕ Fin l) (Fin τ) j) k).submatrix
          (ixSucc (Fin κ ⊕ Fin l) (Fin τ) j) id).toRows₂ ↔
      ∀ p p', κ + l + j * τ ≤ p → p < κ + l + (j + 1) * τ → p' < κ + l + j * τ → IntAt P (M p p' / (q : E)) := by
  have res := _root_.GlobalTheory.SymBridge.ComplRes.residues E k P q ι ϖ hC hU
  constructor
  · intro h p p' hp hp' hp''
    have := h ⟨p - (κ + l + j * τ), by rw [Nat.add_mul] at hp'; omega⟩ ((zEquiv κ l τ j).symm ⟨p', hp''⟩)
    simp only [Matrix.toRows₂, Matrix.submatrix_apply, id, Matrix.of_apply, zPos_ixSucc_inr] at this
    rw [← zEquiv_val, Equiv.apply_symm_apply] at this
    rw [← (res.1 _)]
    convert this using 4
    omega
  · intro h u b
    simp only [Matrix.toRows₂, Matrix.submatrix_apply, id, Matrix.of_apply, zPos_ixSucc_inr]
    rw [res.1]
    exact h _ _ (by omega) (by rw [Nat.add_mul]; omega) (zPos_lt b)

theorem unit_char {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {σ₀ : K →+* ℂ} {ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K}
    {χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ} {s κ : ℕ} {S : SymData k s κ} (hT : Comparison₂ P q ι σ₀ ψ₀ χ S) (i : ℕ) (d : E) (u : kˣ)
    (hd : IntAt P d) (hu : valuation k (u : k) = 1) (e : (u : k) = ι d) :
    (S.μ (i + 1) u : ℂ) = σ₀ (LocE.unitV (χ i) d) := by
  have res := _root_.GlobalTheory.SymBridge.ComplRes.residues E k P q ι S.ϖ hT.compl S.unif
  exact hT.chi i d u hd ((res.2.2.1 d hd).1 (e ▸ hu)) e

theorem intAt_div {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {a : E} (h : IntAt P (a / (q : E))) (hq : (q : E) ≠ 0) :
    IntAt P a := by
  have := h.mul (IntAt.coe P (q : 𝓞 E))
  simpa [div_mul_cancel₀ _ hq] using this

theorem core (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {s κ : ℕ} (S : SymData k s κ) (hT : Comparison₂ P q ι σ₀ ψ₀ χ S) (τ j N : ℕ)
    (hN : N = κ + s + 1 + (j + 1) * τ) (M : ℕ → ℕ → E) :
    S.P.iterPhi (Fin τ) S.μ S.tame j (Matrix.of fun a b => ι (M (zPos a) (zPos b))) =
      σ₀ (phiM q ψ₀ χ κ S.ρ (κ + s + 1) τ j N M) := by
  subst hN
  have hC := hT.compl
  have res := _root_.GlobalTheory.SymBridge.ComplRes.residues E k P q ι S.ϖ hC S.unif
  have hq : (q : E) ≠ 0 := res.2.2.2.1
  have hpat := _root_.GlobalTheory.SymChain.pattern_iter k s κ S (Fin τ) j
  set T : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k :=
    Matrix.of fun a b => ι (M (zPos a) (zPos b)) with hTdef
  have hTop : ((Matrix.of fun a b => ι (M (zPos a) (zPos b)) :
      Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (j + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k).submatrix
        (ixSucc (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) id).toRows₁ = T := by
    ext a b; simp [Matrix.toRows₁, hTdef, zPos_ixSucc_inl]
  have hB := bottom_iff hC S.unif κ (s + 1) τ j M

  have hpatM := _root_.GlobalTheory.PatResidue.pattern_iff_places E k P q ι S.ϖ hC S.unif κ (s + 1) S.ρ τ j M
  have hKO := _root_.GlobalTheory.SymBridge.mem_KO_iff_intAt_isUnit_det E k P q ι S.ϖ hC S.unif κ (s + 1) τ j M
  simp only [TypeDatum.iterPhi, TypeDatum.Phi, hTop]
  unfold phiM
  by_cases hb : MaxM ((Matrix.of fun a b => ι (M (zPos a) (zPos b)) :
      Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (j + 1)) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k).submatrix
        (ixSucc (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) id).toRows₂
  swap
  · rw [if_neg hb, if_neg, map_zero]
    rintro ⟨-, h2, -⟩
    exact hb (hB.2 fun p p' h1 h1' h1'' => h2 p p' h1 (by rw [Nat.add_mul] at h1' ⊢; omega) h1'')
  rw [if_pos hb]
  have h2 := hB.1 hb
  have hzT : ∀ a b, T a b = ι (M (zPos a) (zPos b)) := fun a b => rfl
  have hdet : ∀ g : GL (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k, g.val = T →
      ((Matrix.GeneralLinearGroup.det g : kˣ) : k) =
        ι (Matrix.det (Matrix.of fun s' s'' : Fin (κ + s + 1 + j * τ) => M s'.1 s''.1)) := by
    intro g hg
    rw [Matrix.GeneralLinearGroup.val_det_apply, hg, hTdef,
      det_of_places ι (zEquiv κ (s + 1) τ j) zPos 0 (fun x => by simp [zEquiv_val]) M]
    simp only [zero_add]
    rfl
  have hintdet : ∀ g : GL (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k, g ∈ KO k _ → g.val = T →
      IntAt P (Matrix.det (Matrix.of fun s' s'' : Fin (κ + s + 1 + j * τ) => M s'.1 s''.1)) := by
    intro g hg hgT
    rw [← hC.int, ← hdet g hgT, Valuation.mem_integer_iff, valuation_det_of_mem_KO hg]
  by_cases hJ : ∃ g ∈ (S.P.iter (Fin τ) S.μ S.tame j).J, g.val = T
  · obtain ⟨g, hgJ, hgT⟩ := hJ
    obtain ⟨hgKO, hgpat⟩ := (hpat g).1 hgJ
    obtain ⟨hint, -⟩ := hKO.1 ⟨g, hgKO, hgT⟩
    have hpat' : ∀ (a b : Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j),
        ¬FreeIx S.ρ a b → (valuation k) (ι (M (zPos a) (zPos b)) -
          (1 : Matrix (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) (Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) j) k) a b) < 1 := by
      intro a b hf; have := hgpat a b hf; rwa [hgT] at this
    obtain ⟨h3, h4⟩ := (hpatM hint).1 hpat'
    have hcond : (∀ p p', p < κ + s + 1 + (j + 1) * τ → p' < κ + s + 1 + j * τ → IntAt P (M p p')) ∧
        (∀ p p', κ + s + 1 + j * τ ≤ p → p < κ + s + 1 + (j + 1) * τ → p' < κ + s + 1 + j * τ →
          IntAt P (M p p' / (q : E))) ∧
        (∀ p', p' < κ + s + 1 → redP P (M p' p') = 1 ∧ ∀ p, p < κ + s + 1 + j * τ → p ≠ p' →
          (κ + s + 1 ≤ p ∨ symIdx κ S.ρ p' < symIdx κ S.ρ p ∨ (p' = κ + S.ρ ∧ p < κ)) → redP P (M p p') = 0) ∧
        (∀ p p', κ + s + 1 ≤ p' → p' < κ + s + 1 + j * τ → p < κ + s + 1 + j * τ →
          (p' - (κ + s + 1)) / τ < (p - (κ + s + 1)) / τ → redP P (M p p') = 0) := by
      refine ⟨fun p p' hp hp' => ?_, fun p p' hp hp' hp'' => h2 p p' hp hp' hp'', h3, h4⟩
      by_cases hpa : p < κ + s + 1 + j * τ
      · exact hint p p' hpa hp'
      · exact intAt_div (h2 p p' (by omega) hp hp') hq
    rw [if_pos hcond, ← hgT, extZ_coe _ _ ⟨g, hgJ⟩, TypeDatum.rho_apply]
    obtain ⟨g₀, D, hg₀, hD, hlam⟩ := _root_.GlobalTheory.SymBridge.iter_lam_closed k _ (Fin τ) S.P S.μ S.tame j ⟨g, hgJ⟩
    rw [hlam]
    simp only [Units.val_mul, Units.coe_prod, Units.val_inv_eq_inv_val, LocE.lamGvS, map_mul, map_prod, map_inv₀]
    congr 2
    · refine _root_.GlobalTheory.symLevel_lam_residue_elim E K k P q ι σ₀ ψ₀ χ s κ S hT M (fun p p' hp hp' => hint p p' (by omega) (by omega)) g₀ ?_
      rw [hg₀, hgT]
      ext (x | x) (y | y) <;> rfl
    · rw [← Fin.prod_univ_eq_prod_range]
      refine Finset.prod_congr rfl fun i _ => ?_
      have hdi : ((Matrix.GeneralLinearGroup.det (D i) : kˣ) : k) =
          ι (Matrix.det (Matrix.of fun u v : Fin τ =>
            M (κ + s + 1 + i.val * τ + u.val) (κ + s + 1 + i.val * τ + v.val))) := by
        rw [Matrix.GeneralLinearGroup.val_det_apply, (hD i).2, Ix.diagonalBlockOfMatrix, hgT]
        exact det_of_places ι (Equiv.refl _) (fun u : Fin τ => κ + s + 1 + i.val * τ + u.val) (κ + s + 1 + i.val * τ)
          (fun _ => rfl) M
      refine unit_char hT i _ _ ?_ (valuation_det_of_mem_KO (hD i).1) hdi
      rw [← hC.int, ← hdi, Valuation.mem_integer_iff, valuation_det_of_mem_KO (hD i).1]
    · exact unit_char hT j _ _ (hintdet g hgKO hgT) (valuation_det_of_mem_KO hgKO) (hdet g hgT)
  · rw [extZ_of_not _ _ hJ]
    split_ifs with hc
    · have hnu : ¬ IsUnit (redP P (Matrix.det (Matrix.of fun s' s'' : Fin (κ + s + 1 + j * τ) => M s'.1 s''.1))) := by
        intro hu
        have hint : ∀ p p', p < κ + (s + 1) + j * τ → p' < κ + (s + 1) + j * τ → IntAt P (M p p') :=
          fun p p' hp hp' => hc.1 p p' (by rw [Nat.add_mul]; omega) hp'
        obtain ⟨g, hgKO, hgT⟩ := hKO.2 ⟨hint, hu⟩
        refine hJ ⟨g, (hpat g).2 ⟨hgKO, fun a b hf => ?_⟩, hgT⟩
        rw [hgT]
        exact (hpatM hint).2 ⟨hc.2.2.1, hc.2.2.2⟩ a b hf
      rw [LocE.unitV, dite_eq_right hnu, _root_.inv_zero, mul_zero, map_zero]
    · rw [map_zero]

end GlobalTheory.SymBridge.TopAgree


open GlobalTheory.SymBridge.TopAgree in
theorem GlobalTheory.SymBridge.phiTopAgree_of_tie : ∀ (E K k : Type) [Field E] [NumberField E] [StarRing E] [Field K] [Field k]
    [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k)
    (σ₀ : K →+* ℂ) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (s κ : ℕ) (S : SymData k s κ),
    Comparison₂ P q ι σ₀ ψ₀ χ S → PhiTopAgree P q ι σ₀ ψ₀ χ S := by
  intro E K k _ _ _ _ _ _ _ _ P q ι σ₀ ψ₀ χ s κ S hT τ n' c' n hn' hc' hn e' e he' he x
  subst hc'
  rw [top_entries q ι S τ n' n e' e he' he x,
    core P q ι σ₀ ψ₀ χ S hT τ (s + 1) (n + 0) (by omega)]
  exact congrArg σ₀ (PhiGS_eq q ψ₀ χ κ S.ρ (κ + s + 1) τ (s + 1) 0 n' 0 n x).symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMirabolicProjectionIffColSpaceAutToLocalGL
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.VolBridge

section PrXIff
variable {E : Type} [Field E] {M c' : ℕ}

theorem inX_castAdd (v : Sp E M) (i : Fin M) : Loc.inX E M c' v (Fin.castAdd c' i) = v i := by
  simp [Loc.inX]

theorem inX_natAdd (v : Sp E M) (i : Fin c') : Loc.inX E M c' v (Fin.natAdd M i) = 0 := by
  simp [Loc.inX]

theorem extX_inX (y : Sp E M ≃ₗ[E] Sp E M) (v : Sp E M) :
    extX c' y (Loc.inX E M c' v) = Loc.inX E M c' (y v) := by
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · rw [extX_castAdd, inX_castAdd]
    have h : (fun j => Loc.inX E M c' v (Fin.castAdd c' j)) = v := funext fun j => inX_castAdd v j
    rw [h]
  · rw [extX_natAdd, inX_natAdd, inX_natAdd]

variable {A : Type} {c : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c)
  (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)

include he in
theorem e_inl (a : A) : e (Sum.inl a) = Fin.castAdd c' (eX e hcc he a) := Fin.ext (by simp [eX_val])

include he in
theorem e_inr (i : Fin c) : e (Sum.inr i) = Fin.natAdd M (⟨i.val, hcc ▸ i.isLt⟩ : Fin c') := Fin.ext (by simp [he])

theorem single_inl (a : A) :
    (Pi.single (e (Sum.inl a)) 1 : Sp E (M + c')) = Loc.inX E M c' (Pi.single (eX e hcc he a) 1) := by
  rw [e_inl e hcc he]
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · rw [inX_castAdd]
    by_cases h : i = eX e hcc he a
    · subst h; simp
    · rw [Pi.single_eq_of_ne (fun h' => h (Fin.castAdd_injective _ _ h')), Pi.single_eq_of_ne h]
  · rw [inX_natAdd, Pi.single_eq_of_ne]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega

end PrXIff

section Blocks
variable {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ}
  (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)

theorem locHom_inl_inl (r : Sp E (M + c') ≃ₗ[E] Sp E (M + c')) (y : Sp E M ≃ₗ[E] Sp E M)
    (hr : ∀ v, r (Loc.inX E M c' v) = Loc.inX E M c' (y v)) (a b : A) :
    (locHom ι e r).val (Sum.inl a) (Sum.inl b) = (locHom ι (eX e hcc he) y).val a b := by
  show ι (r (Pi.single (e (Sum.inl b)) 1) (e (Sum.inl a))) = ι (y (Pi.single (eX e hcc he b) 1) (eX e hcc he a))
  rw [single_inl e hcc he, hr, e_inl e hcc he, inX_castAdd]

theorem locHom_extX (y : Sp E M ≃ₗ[E] Sp E M) :
    locHom ι e (extX c' y) = embX c (locHom ι (eX e hcc he) y) := by
  ext i j
  rw [GlobalTheory.RootEx.VolN.val_embX]
  show ι (extX c' y (Pi.single (e j) 1) (e i)) = _
  rcases i with a | s
  · rw [e_inl e hcc he, extX_castAdd]
    rcases j with b | t
    · rw [single_inl e hcc he]
      have h : (fun l => Loc.inX E M c' (Pi.single (eX e hcc he b) (1 : E)) (Fin.castAdd c' l)) = Pi.single (eX e hcc he b) 1 :=
        funext fun l => inX_castAdd _ l
      rw [h]
      rfl
    · have h : (fun l => (Pi.single (e (Sum.inr t)) (1 : E) : Sp E (M + c')) (Fin.castAdd c' l)) = 0 := by
        funext l
        rw [Pi.single_eq_of_ne]
        · rfl
        intro h'
        have := congrArg Fin.val h'
        simp [he] at this
        omega
      rw [h, map_zero]
      simp
  · rw [e_inr e hcc he, extX_natAdd]
    rcases j with b | t
    · rw [Pi.single_eq_of_ne]
      · simp
      intro h'
      have := congrArg Fin.val h'
      simp [eX_val] at this
      have := eX_lt e hcc he b
      omega
    · rw [e_inr e hcc he]
      by_cases h : s = t
      · subst h; simp
      · rw [Pi.single_eq_of_ne]
        · simp [Matrix.one_apply, h]
        intro h'
        have := congrArg Fin.val h'
        simp at this
        exact h (Fin.ext this)

end Blocks

theorem prX_iff_locHom : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val), (∀ x, x ∈ Loc.N1 E M c' ↔ locHom ι e x ∈ N k A c 1) → (∀ u ∈ N k A c 1, ∀ V : Set (GL (A ⊕ Fin c) k), IsOpen V → u ∈ V → ∃ x ∈ Loc.N1 E M c', locHom ι e x ∈ V) → ∀ (CE : Subgroup (Sp E (M + c') ≃ₗ[E] Sp E (M + c'))) (Ck : Subgroup (GL (A ⊕ Fin c) k)) (O : Set (GL (A ⊕ Fin c) k)), IsOpen O → (∀ z ∈ R k A c 1, z ∈ Ck ↔ z ∈ O) → Ck ≤ R k A c 1 → (∀ x, x ∈ CE ↔ locHom ι e x ∈ Ck) → ∀ y, y ∈ Loc.prX CE ↔ locHom ι (eX e hcc he) y ∈ prX Ck := by
  intro E k _ _ _ _ _ ι A _ _ M c c' e hcc he hN hdense CE Ck O hO hCkO hCkR hCE y
  constructor
  · rintro ⟨r, hr, hry⟩
    have hg : locHom ι e r ∈ Ck := (hCE r).1 hr
    obtain ⟨x', u, hu, hxu⟩ := GlobalTheory.RootEx.VolN.exists_of_mem_R (hCkR hg)
    have hu' := GlobalTheory.RootEx.Model.mem_N_iff.1 hu
    have hx' : x' = locHom ι (eX e hcc he) y := by
      ext a b
      rw [← locHom_inl_inl ι e hcc he r y hry a b, hxu, Units.val_mul, GlobalTheory.RootEx.VolN.val_embX, Matrix.mul_apply,
        Fintype.sum_sum_type]
      have h1 : ∀ a', u.val (Sum.inl a') (Sum.inl b) = if a' = b then 1 else 0 := fun a' => by
        rw [hu' (Sum.inl a') (Sum.inl b) le_rfl]
        simp [Matrix.one_apply]
      simp [h1]
    refine ⟨embX c x' * u * (embX c x')⁻¹, ?_, ?_⟩
    · have := GlobalTheory.RootEx.Model.conj_mem hu x'⁻¹
      simpa [map_inv, inv_inv] using this
    · rw [← hx']
      simpa [mul_assoc, ← hxu] using hg
  · rintro ⟨u, hu, huC⟩
    set x := locHom ι (eX e hcc he) y with hx
    have huO : u * embX c x ∈ O := (hCkO _ (hCkR huC)).1 huC
    have hV : IsOpen {v : GL (A ⊕ Fin c) k | v * embX c x ∈ O} := hO.preimage (continuous_mul_const _)
    obtain ⟨x₀, hx₀, hx₀V⟩ := hdense u hu _ hV huO
    refine ⟨x₀ * extX c' y, ?_, fun v => ?_⟩
    · rw [hCE, map_mul, locHom_extX ι e hcc he]
      have hR : locHom ι e x₀ * embX c x ∈ R k A c 1 :=
        mul_mem (Subgroup.mem_sup_right ((hN x₀).1 hx₀)) (Subgroup.mem_sup_left ⟨x, rfl⟩)
      exact (hCkO _ hR).2 hx₀V
    · show x₀ (extX c' y (Loc.inX E M c' v)) = _
      rw [extX_inX]
      exact (Subgroup.mem_inf.1 hx₀).2 (y v)

end GlobalTheory.VolBridge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemStabLocalizedStdLatticeIffIntegralGL
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

noncomputable section
namespace GlobalTheory.VolBridge.StabRead

variable {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k]
  {P : HeightOneSpectrum (𝓞 E)} {ι : E →+* k}

theorem mem_stdAt_iff_int (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {M : ℕ} (v : Sp E M) :
    v ∈ stdAt E M P ↔ ∀ i, ι (v i) ∈ 𝒪[k] := by
  rw [GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.mem_stdAt]
  exact forall_congr' fun i => (hι _).symm

theorem single_mem_stdAt (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {M : ℕ} (m : Fin M) :
    (Pi.single m 1 : Sp E M) ∈ stdAt E M P := by
  rw [mem_stdAt_iff_int hι]
  intro i
  rw [Pi.single_apply]
  split_ifs
  · rw [map_one]; exact Subring.one_mem _
  · rw [map_zero]; exact Subring.zero_mem _

theorem map_mem_stdAt (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {M : ℕ} (y : Sp E M ≃ₗ[E] Sp E M)
    (hy : ∀ i m, ι (y (Pi.single m 1) i) ∈ 𝒪[k]) {v : Sp E M} (hv : v ∈ stdAt E M P) : y v ∈ stdAt E M P := by
  rw [mem_stdAt_iff_int hι] at hv ⊢
  intro i
  have e : y v = LinearMap.toMatrix' (y : Sp E M →ₗ[E] Sp E M) *ᵥ v := (LinearMap.toMatrix'_mulVec _ v).symm
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, LinearMap.toMatrix'_apply, map_sum, map_mul]
  exact Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hy i m) (hv m)

end GlobalTheory.VolBridge.StabRead


open GlobalTheory.VolBridge.StabRead in
theorem GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k)
    (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M)
    (x : Sp E M ≃ₗ[E] Sp E M) : x ∈ stabL E M (stdAt E M P) ↔ locHom ι e x ∈ KO k A := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  constructor
  · intro hx
    have hx' : x⁻¹ ∈ stabL E M (stdAt E M P) := inv_mem hx
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · change ι (x (Pi.single (e b) 1) (e a)) ∈ 𝒪[k]
      exact (mem_stdAt_iff_int hι _).1 ((hx _).2 (single_mem_stdAt hι _)) _
    · change ι ((x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (Pi.single (e b) 1) (e a)) ∈ 𝒪[k]
      exact (mem_stdAt_iff_int hι _).1 ((hx' _).2 (single_mem_stdAt hι _)) _
  · rintro ⟨h1, h2⟩
    have i1 : ∀ i m, ι (x (Pi.single m 1) i) ∈ 𝒪[k] := fun i m => by
      have h := h1 (e.symm i) (e.symm m)
      change ι (x (Pi.single (e (e.symm m)) 1) (e (e.symm i))) ∈ 𝒪[k] at h
      simpa only [Equiv.apply_symm_apply] using h
    have i2 : ∀ i m, ι ((x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (Pi.single m 1) i) ∈ 𝒪[k] := fun i m => by
      have h := h2 (e.symm i) (e.symm m)
      change ι ((x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (Pi.single (e (e.symm m)) 1) (e (e.symm i))) ∈ 𝒪[k] at h
      simpa only [Equiv.apply_symm_apply] using h
    intro v
    constructor
    · intro hv
      have h := map_mem_stdAt hι _ i2 hv
      have ev : (x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (x v) = v := x.symm_apply_apply v
      rwa [ev] at h
    · exact map_mem_stdAt hι x i1
end
end

