module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicAdelicFormOfBoundedSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCuspFormTransvectionConstantTermsZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedSectionOfBoundedHolomorphicForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicCuspFormOfAdelicConstantTermsZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Formalism.HarderNarasimhan.StatementPl
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTotallyRealEvenNegPlacesLocalNorm
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.NormSignEven

variable {M : Type} [Field M] [NumberField M]

lemma cc (φ : M →+* ℂ) : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := star_star φ

lemma conj_re (φ : M →+* ℂ) (x : M) : (ComplexEmbedding.conjugate φ x).re = (φ x).re := by
  rw [ComplexEmbedding.conjugate_coe_eq]; simp

lemma conj_ne {σ : M →+* M} (hσ : σ ≠ RingHom.id M)
    (hc : ∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) (φ : M →+* ℂ) :
    ComplexEmbedding.conjugate φ ≠ φ := by
  intro h
  apply hσ
  ext x
  apply φ.injective
  rw [hc, RingHom.id_apply]
  have := congrArg (fun ψ : M →+* ℂ => ψ x) h
  simpa [ComplexEmbedding.conjugate_coe_eq] using this

lemma im_eq_zero {σ : M →+* M}
    (hc : ∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) (φ : M →+* ℂ) {x : M} (hx : σ x = x) :
    (φ x).im = 0 := by
  have h := hc φ x
  rw [hx] at h
  exact Complex.conj_eq_iff_im.mp h.symm

lemma re_mul {σ : M →+* M}
    (hc : ∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) (φ : M →+* ℂ) {x y : M}
    (hx : σ x = x) :
    (φ (x * y)).re = (φ x).re * (φ y).re := by
  rw [map_mul, Complex.mul_re, im_eq_zero hc φ hx, zero_mul, sub_zero]

end GlobalTheory.NormSignEven

open GlobalTheory.NormSignEven in
theorem GlobalTheory.NormSign.exists_neg_even_norm_away : ∀ (M : Type) [Field M] [NumberField M] (σ : M →+* M), σ ≠ RingHom.id M → (∀ (φ : M →+* ℂ) (x : M), φ (σ x) = (starRingEnd ℂ) (φ x)) → ∀ (S : Finset (M →+* ℂ)), (∀ φ ∈ S, ComplexEmbedding.conjugate φ ∈ S) → 4 ∣ S.card → ∀ (p : ℕ) [Fact p.Prime], ∃ a : M, a ≠ 0 ∧ σ a = a ∧ (∀ φ ∈ S, (φ a).re < 0) ∧ (∀ φ : M →+* ℂ, φ ∉ S → 0 < (φ a).re) ∧ ∃ u : (AfP p ⊗[ℚ] M)ˣ, (u : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom u = 1 ⊗ₜ a := by
  intro M _ _ σ hσ hc S hS h4 p _
  obtain ⟨n, hn⟩ := h4
  induction n generalizing S with
  | zero =>
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (by simpa using hn)
    subst hS0
    refine ⟨1, one_ne_zero, map_one σ, by simp, fun φ _ => by simp, 1, ?_⟩
    simp [Algebra.TensorProduct.one_def]
  | succ n ih =>
    obtain ⟨ε, hε⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    have hε1 : ComplexEmbedding.conjugate ε ∈ (S.erase ε) :=
      Finset.mem_erase.mpr ⟨conj_ne hσ hc ε, hS ε hε⟩
    have hT : 0 < ((S.erase ε).erase (ComplexEmbedding.conjugate ε)).card := by
      rw [Finset.card_erase_of_mem hε1, Finset.card_erase_of_mem hε]; omega
    obtain ⟨ε', hε'⟩ := Finset.card_pos.mp hT
    simp only [Finset.mem_erase] at hε'
    obtain ⟨h1, h2, hε'S⟩ := hε'
    have hcc : ∀ φ ψ : M →+* ℂ, ComplexEmbedding.conjugate φ = ψ → φ = ComplexEmbedding.conjugate ψ := by
      intro φ ψ h; rw [← h, cc]
    have h3 : ε ≠ ComplexEmbedding.conjugate ε' := by
      intro h; apply h1; rw [h, cc]
    set S' := (((S.erase ε).erase (ComplexEmbedding.conjugate ε)).erase ε').erase
      (ComplexEmbedding.conjugate ε') with hS'def
    have hmem : ∀ φ, φ ∈ S' ↔ φ ≠ ComplexEmbedding.conjugate ε' ∧ φ ≠ ε' ∧
        φ ≠ ComplexEmbedding.conjugate ε ∧ φ ≠ ε ∧ φ ∈ S := by
      intro φ; simp [hS'def, Finset.mem_erase]
    have hcard : S'.card = 4 * n := by
      have e1 : ε' ∈ ((S.erase ε).erase (ComplexEmbedding.conjugate ε)) := by
        simp [Finset.mem_erase]; exact ⟨h1, h2, hε'S⟩
      have e2 : ComplexEmbedding.conjugate ε' ∈
          ((S.erase ε).erase (ComplexEmbedding.conjugate ε)).erase ε' := by
        simp only [Finset.mem_erase]
        refine ⟨conj_ne hσ hc ε', ?_, fun h => h3 h.symm, hS _ hε'S⟩
        intro h
        exact h2 (by have := congrArg ComplexEmbedding.conjugate h; simpa [cc] using this)
      rw [hS'def, Finset.card_erase_of_mem e2, Finset.card_erase_of_mem e1,
        Finset.card_erase_of_mem hε1, Finset.card_erase_of_mem hε]
      omega
    have hS'stab : ∀ φ ∈ S', ComplexEmbedding.conjugate φ ∈ S' := by
      intro φ hφ
      rw [hmem] at hφ ⊢
      obtain ⟨a1, a2, a3, a4, a5⟩ := hφ
      refine ⟨fun h => a2 ?_, fun h => a1 ?_, fun h => a4 ?_, fun h => a3 ?_, hS φ a5⟩
      · have := congrArg ComplexEmbedding.conjugate h; simpa [cc] using this
      · exact hcc _ _ h
      · have := congrArg ComplexEmbedding.conjugate h; simpa [cc] using this
      · exact hcc _ _ h
    obtain ⟨b, hb0, hbσ, hbneg, hbpos, ub, hub⟩ := ih S' hS'stab hcard
    obtain ⟨c, hc0, hcσ, hcε, hcε', hcpos, uc, huc⟩ :=
      GlobalTheory.T.exists_realSubfield_negative_twoPlaces_normEverywhere M σ hσ hc ε ε' (Ne.symm h2) h3 p
    have hcneg : ∀ φ, φ = ε ∨ φ = ComplexEmbedding.conjugate ε ∨ φ = ε' ∨ φ = ComplexEmbedding.conjugate ε' →
        (φ c).re < 0 := by
      rintro φ (rfl | rfl | rfl | rfl)
      · exact hcε
      · rw [conj_re]; exact hcε
      · exact hcε'
      · rw [conj_re]; exact hcε'
    refine ⟨b * c, mul_ne_zero hb0 hc0, by rw [map_mul, hbσ, hcσ], ?_, ?_, ub * uc, ?_⟩
    · intro φ hφ
      rw [re_mul hc φ hbσ]
      by_cases hφ' : φ ∈ S'
      · exact mul_neg_of_neg_of_pos (hbneg φ hφ') (hcpos φ (by rw [hmem] at hφ'; exact hφ'.2.2.2.1)
          (by rw [hmem] at hφ'; exact hφ'.2.2.1) (by rw [hmem] at hφ'; exact hφ'.2.1)
          (by rw [hmem] at hφ'; exact hφ'.1))
      · refine mul_neg_of_pos_of_neg (hbpos φ hφ') (hcneg φ ?_)
        rw [hmem] at hφ'
        by_contra hne
        push_neg at hne
        exact hφ' ⟨hne.2.2.2, hne.2.2.1, hne.2.1, hne.1, hφ⟩
    · intro φ hφ
      rw [re_mul hc φ hbσ]
      have hφ' : φ ∉ S' := fun h => hφ (((hmem φ).mp h).2.2.2.2)
      refine mul_pos (hbpos φ hφ') (hcpos φ ?_ ?_ ?_ ?_)
      · rintro rfl; exact hφ hε
      · rintro rfl; exact hφ (hS ε hε)
      · rintro rfl; exact hφ hε'S
      · rintro rfl; exact hφ (hS ε' hε'S)
    · rw [Units.val_mul, map_mul]
      calc (ub : AfP p ⊗[ℚ] M) * uc * (Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom ub *
            Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom uc)
          = ((ub : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom ub) *
            ((uc : AfP p ⊗[ℚ] M) * Algebra.TensorProduct.map (AlgHom.id ℚ (AfP p)) σ.toRatAlgHom uc) := by ring
        _ = 1 ⊗ₜ (b * c) := by rw [hub, huc, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorEvalMultiplicitySpaceOntoHolomorph
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem HolForm.congr_level {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}
    {w : D.what₂.Tau → Fin V.rank → ℤ} {J : Set (GA D V)} {χ χ' φ : GA D V → ℂ} (h : HolForm θ M w J χ φ)
    (e : ∀ k ∈ J, χ k = χ' k) : HolForm θ M w J χ' φ :=
  ⟨h.aut, h.bdd, fun k hk g => by rw [← e k hk]; exact h.lev k hk g, h.hol⟩

theorem mult_eval_eq_adel_holSub0 : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → WtIs M w → ∀ v : M.Vec, IsExtVec M v → ∀ χ : GA D V → ℂ, (∀ k ∈ Kf, χ k = 1) → (∀ P ∈ Formalism.L2.Pj.holSub0 X la, ∃ T ∈ Mult θ M (Kf : Set (GA D V)) χ, T v = adel V dict (muPin V dict mu c) P) ∧ ∀ T ∈ Mult θ M (Kf : Set (GA D V)) χ, ∃ P ∈ Formalism.L2.Pj.holSub0 X la, adel V dict (muPin V dict mu c) P = T v := by
  intro hdec hvol D θ V S M w r hr Comp X la dict mu c Kf hS hG hw v hv χ hχ
  refine ⟨fun P hP => ?_, fun T hT => ?_⟩
  · have hP1 : P ∈ Submodule.span ℂ {P | IsHolCusp X la P} := hP.1
    clear hP
    induction hP1 using Submodule.span_induction with
    | mem P hP =>
      have h1 := _root_.GlobalTheory.HolDict.BackHol.holForm_adel D θ V S M w r hr Comp X la dict mu c Kf hS hG P (fun k => (hP k).1)
      have h2 := _root_.GlobalTheory.HolDict.TransvCusp.zCusp_adel D θ V S M w r hr Comp X la dict mu c Kf hS hG P hP
      obtain ⟨T, hT, hTv⟩ := GlobalTheory.T.boundedHolomorphicForm_eq_multiplicitySpace_value D θ V S M w v hG.inf hS hw hv (exists_finPair hvol D V)
        (Kf : Set (GA D V)) χ _ hG.levFin (h1.congr_level fun k hk => (hχ k hk).symm) h2
      exact ⟨T, Submodule.subset_span hT, hTv⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add P Q _ _ hP hQ =>
      obtain ⟨T, hT, hTv⟩ := hP
      obtain ⟨T', hT', hTv'⟩ := hQ
      exact ⟨T + T', Submodule.add_mem _ hT hT', by rw [map_add (f := _), _root_.add_apply, hTv, hTv']⟩
    | smul a P _ hP =>
      obtain ⟨T, hT, hTv⟩ := hP
      exact ⟨a • T, Submodule.smul_mem _ a hT, by rw [map_smul, _root_.smul_apply, hTv]⟩
  · obtain ⟨h1, h2⟩ := _root_.GlobalTheory.HolDict.holForm_zCusp_of_mem_mult hdec D θ V S M w v hG.inf hS hw hv (Kf : Set (GA D V)) χ T hT
    obtain ⟨P, hP0, hPb, hPe⟩ := _root_.GlobalTheory.HolDict.IntoSec.exists_bddSec_adel_eq D θ V S M w r hr Comp X la dict mu c Kf hS hG (T v)
      (h1.congr_level hχ)
    have hc := _root_.GlobalTheory.HolDict.IntoCusp.isHolCusp_of_zCusp D θ V S M w r hr Comp X la dict mu c Kf hS hG P hPb (hPe ▸ h2)
    exact ⟨P, ⟨holCusp_mem_holSub X la hc, hP0⟩, hPe⟩

end GlobalTheory.HolDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilMonoOfKerRes
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

namespace GlobalTheory.HSCore

theorem mulPow_mulVar {K : Type} [Field K] [NumberField K] (G : Geo K) (s : Fin G.D → Fin G.N → K) {a j l : ℕ}
    (h : j + (a + 1) = l) (h' : (j + 1) + a = l) (α : MonoDeg (Fin G.D) a) (i : Fin G.D) (m : G.Sec j) :
    mulPow G s h (MonoDeg.mulVar i α) m = mulPow G s h' α (G.mulW j (s i) m) := by
  rw [G.mulW_apply]
  unfold mulPow
  refine tw_ext (isLB_tens G.K.isLB G.isLBA) G.isLB fun c k y hy hc hk => ?_
  rw [germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk, germ_mulMono _ _ _ _ _ _ _ _ _ _ hc hk,
    germ_mulSec _ _ _ _ _ _ _ _ _ hc hk, monoVal_mulVar, mul_comm (secGer _ _ _ _ _), mul_assoc]

theorem filMono_of_kerRes : KerRes → FilMono := by
  intro H K _ _ G hnef hbig s hs a
  induction a with
  | zero =>
    intro j l h _ f hf
    obtain rfl : j = l := h
    have : Subsingleton (MonoDeg (Fin G.D) 0) := ⟨fun α β => Subtype.ext
      (((Finsupp.degree_eq_zero_iff _).1 α.2).trans ((Finsupp.degree_eq_zero_iff _).1 β.2).symm)⟩
    refine ⟨fun _ => f, fun _ => hf.1, ?_⟩
    rw [Fintype.sum_subsingleton _ (⟨0, rfl⟩ : MonoDeg (Fin G.D) 0)]
    exact (mulMono_zero _ _ _ _ _ f).symm
  | succ a ih =>
    classical
    intro j l h hj f hf
    have h' : (j + 1) + a = l := by omega
    have hfa : f ∈ Fil (G.ideal s) a (G.global l) := Fil_anti (Nat.le_succ a) hf
    obtain ⟨m, hm, e⟩ := ih (j + 1) l h' (by omega) f hfa
    have h0 : hs.sym h' (G.global l) ⟨f, hfa⟩ = 0 := (sym_eq_zero_iff _ _ _ _ _ _ _ _ _ _ _).2 hf
    have h1 : hs.sym h' (G.global l) ⟨f, hfa⟩ = fun α => hs.res (j + 1) (m α) :=
      sym_sum _ _ _ _ _ _ _ _ _ _ m _ e
    have hv : ∀ α, m α ∈ Fil (G.ideal s) 1 (G.global (j + 1)) := fun α =>
      ⟨hm α, (Res_eq_zero_iff _ _ _ _ _ _ _ _ _ _).1 (congrFun (h1.symm.trans h0) α)⟩
    choose m' hm' e' using fun α => H K G hnef hbig s hs j (by omega) (m α) (hv α)
    refine ⟨fun γ => ∑ p ∈ Finset.univ.filter (fun p : MonoDeg (Fin G.D) a × Fin G.D => MonoDeg.mulVar p.2 p.1 = γ),
      m' p.1 p.2, fun γ => sum_mem fun p _ => hm' _ _, ?_⟩
    have key : ∀ γ : MonoDeg (Fin G.D) (a + 1), mulPow G s h γ
        (∑ p ∈ Finset.univ.filter (fun p : MonoDeg (Fin G.D) a × Fin G.D => MonoDeg.mulVar p.2 p.1 = γ), m' p.1 p.2) =
        ∑ p ∈ Finset.univ.filter (fun p : MonoDeg (Fin G.D) a × Fin G.D => MonoDeg.mulVar p.2 p.1 = γ),
          mulPow G s h' p.1 (G.mulW j (s p.2) (m' p.1 p.2)) := fun γ => by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [← (Finset.mem_filter.1 hp).2, mulPow_mulVar G s h h']
    rw [Finset.sum_congr rfl fun γ _ => key γ, Finset.sum_fiberwise, Fintype.sum_prod_type, e]
    refine Finset.sum_congr rfl fun α _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e' α, map_sum]

end GlobalTheory.HSCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilSpaceVEqSpaceP
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSCore

theorem spaceP_le_filTop {K : Type} [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) :
    spaceP X s ≤ filTop X.str (X.adj X.T) X.U (X.ideal s) (X.T - X.D) := by
  unfold spaceP
  refine iSup_le fun α => ?_
  rintro _ ⟨m, -, rfl⟩
  exact vanishesTo_mulMono _ _ _ α _ m

theorem fil_spaceV_eq_spaceP (hF : FilMono) (K : Type) [Field K] [NumberField K] (X : Data K)
    (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (hn : IsNef K X.LA) (hb : IsBig K X.LA) :
    Fil (X.ideal s) (X.T - X.D) (spaceV X s) = spaceP X s := by
  apply le_antisymm
  · rintro f ⟨hfV, hfv⟩
    obtain ⟨g, hg, p, hp, rfl⟩ := Submodule.mem_sup.1 hfV
    have hpv : VanishesTo (X.ideal s) (X.T - X.D) p := spaceP_le_filTop X s hp
    have hgv : VanishesTo (X.ideal s) (X.T - X.D) g := by
      have : g = (g + p) - p := by abel
      rw [this]
      exact (filTop X.str (X.adj X.T) X.U (X.ideal s) (X.T - X.D)).sub_mem hfv hpv
    obtain ⟨m, hm, hgm⟩ := hF K X.toGeo hn hb s hs (X.T - X.D) X.D X.T (add_sub_D X) (Nat.le_refl _) g ⟨hg, hgv⟩
    refine (spaceP X s).add_mem ?_ hp
    rw [hgm]
    refine Submodule.sum_mem _ fun α _ => ?_
    unfold spaceP
    exact Submodule.mem_iSup_of_mem α ⟨m α, X.global_le X.D (by have := X.le_T; omega) (hm α), rfl⟩
  · intro f hf
    exact ⟨Submodule.mem_sup_right hf, spaceP_le_filTop X s hf⟩

theorem filP : FilMono → ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K),
    X.IsGood s → IsNef K X.LA → IsBig K X.LA → Fil (X.ideal s) (X.T - X.D) (spaceV X s) = spaceP X s :=
  fun hF K _ _ X s hs hn hb => fil_spaceV_eq_spaceP hF K X s hs hn hb

end GlobalTheory.HSCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilVSymVKer
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem filV_symV_ker : ∀ (K : Type) [Field K] [NumberField K] (X : Data K) (s : Fin X.D → Fin X.N → K) (hs : X.IsGood s) (δ : ℕ) (Co : Coord X.toGeo hs δ), ∀ a < X.T - X.D, filV X s (a + 1) ≤ filV X s a ∧ ∀ x : filV X s a, symV Co a x = 0 ↔ x.1 ∈ filV X s (a + 1) := by
  intro K _ _ X s hs δ Co a ha
  have haT : a ≤ X.T := by omega
  refine ⟨Submodule.comap_mono (Vanishing.Fil_anti (Nat.le_succ a)), fun x => ?_⟩
  have key : symV Co a x = 0 ↔ hs.sym (Nat.sub_add_cancel haT) (spaceV X s)
      ((X.V X.T).subtype.restrict (fun _ hx => hx) x) = 0 := by
    unfold symV
    rw [dite_eq_left haT]
    constructor
    · intro h
      funext α
      apply (Co.ev (X.T - a)).injective
      funext p
      have := congrFun h (α, p)
      simpa using this
    · intro h
      funext q
      simp [h]
  rw [key]
  exact Vanishing.sym_eq_zero_iff _ _ _ _ _ _ _ _ _ _ _

end GlobalTheory.HSCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTranslatesSmoothFunctionOfCompact
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem finite_translates_of_isCompact (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (φ : Sm E a) (h : IsOpen {k | finRep E a k φ = φ})
    (Kf : Set (GL (Fin a) (Af E))) (hK : IsCompact Kf) :
    ∃ S : Finset (GL (Fin a) (Af E)), ∀ f ∈ Kf, ∃ f' ∈ S,
      finRep E a f φ = finRep E a f' φ := by
  have hn : ∀ f ∈ Kf, {g | finRep E a g φ = finRep E a f φ} ∈ nhds f := by
    intro f _
    have hc : Continuous (fun g : GL (Fin a) (Af E) => f⁻¹ * g) :=
      continuous_const.mul continuous_id
    have ho := h.preimage hc
    refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
    · simp
    · intro g hg
      have hg' : finRep E a (f⁻¹ * g) φ = φ := hg
      have e : g = f * (f⁻¹ * g) := by simp
      show finRep E a g φ = finRep E a f φ
      calc finRep E a g φ = finRep E a (f * (f⁻¹ * g)) φ := by rw [← e]
        _ = finRep E a f (finRep E a (f⁻¹ * g) φ) := by rw [map_mul]; rfl
        _ = finRep E a f φ := by rw [hg']
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun f => {g | finRep E a g φ = finRep E a f φ}) hn
  refine ⟨t, fun f hf => ?_⟩
  have := ht hf
  simp only [Set.mem_iUnion] at this
  obtain ⟨f', hf', h'⟩ := this
  exact ⟨f', hf', h'⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLogISupInt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore.RankOne

variable {K : Type} [Field K] [NumberField K]

theorem finsum_log_iSup_int {ι : Type} [Finite ι] {x : ι → 𝓞 K} (hx : x ≠ 0) :
    ∑ᶠ v : FinitePlace K, Real.log (⨆ i, v (x i)) = -Real.log (Ideal.absNorm (Ideal.span (Set.range x))) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hx
  have hi : (x i₀ : K) ≠ 0 := by exact_mod_cast hi₀
  have hz : (fun i => (x i : K)) ≠ 0 := Function.ne_iff.2 ⟨i₀, hi⟩
  have hpos : ∀ v : FinitePlace K, 0 < ⨆ i, v (x i) := fun v =>
    lt_of_lt_of_le (FinitePlace.pos_iff.2 hi) (le_ciSup (f := fun i => v (x i)) (Set.finite_range _).bddAbove i₀)
  have h := NumberField.absNorm_mul_finprod_finitePlace_eq_one hx
  rw [← Real.log_finprod hpos, eq_inv_of_mul_eq_one_right h, Real.log_inv]

theorem finsum_log_iSup_div {n : ℕ} {b : Fin n → 𝓞 K} (hb : b ≠ 0) {d : 𝓞 K} (hd : d ≠ 0) :
    ∑ᶠ v : FinitePlace K, Real.log (⨆ k, v ((b k : K) / d)) =
      Real.log (Ideal.absNorm (Ideal.span {d})) - Real.log (Ideal.absNorm (Ideal.span (Set.range b))) := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hb
  have hi : (b i₀ : K) ≠ 0 := by exact_mod_cast hi₀
  have hd' : (d : K) ≠ 0 := by exact_mod_cast hd
  have hz : (fun i => (b i : K)) ≠ 0 := Function.ne_iff.2 ⟨i₀, hi⟩
  have hdz : (fun _ : Unit => d) ≠ 0 := Function.ne_iff.2 ⟨(), hd⟩
  have hdz' : (fun _ : Unit => (d : K)) ≠ 0 := Function.ne_iff.2 ⟨(), hd'⟩
  have h1 := finsum_log_iSup_int hb
  have h2 := finsum_log_iSup_int hdz
  have f1 := GlobalTheory.Adelic.HeightExt.finite_support_log_iSup hz
  have f2 := GlobalTheory.Adelic.HeightExt.finite_support_log_iSup hdz'
  rw [Set.range_const] at h2
  have e : ∀ v : FinitePlace K, Real.log (⨆ k, v ((b k : K) / d)) =
      Real.log (⨆ k, v (b k : K)) - Real.log (⨆ _ : Unit, v (d : K)) := fun v => by
    have hpos : 0 < ⨆ i, v (b i : K) :=
      lt_of_lt_of_le (FinitePlace.pos_iff.2 hi) (le_ciSup (f := fun i => v (b i : K)) (Set.finite_range _).bddAbove i₀)
    have hv : 0 < v (d : K) := FinitePlace.pos_iff.2 hd'
    rw [ciSup_const, ← Real.log_div hpos.ne' hv.ne']
    congr 1
    simp only [div_eq_mul_inv, map_mul, map_inv₀]
    exact (Real.iSup_mul_of_nonneg (inv_nonneg.2 hv.le) _).symm
  simp only [e]
  rw [finsum_sub_distrib f1 f2, h1, h2]
  ring

end GlobalTheory.HSCore.RankOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockAct2DiagonalOne
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.VacuumWeight

theorem diagonal_eq_sum_Eab {r s : ℕ} (D : Ix r s → ℂ) :
    Matrix.diagonal D = ∑ c, D c • Eab c c := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, Eab, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h]; symm
    exact Finset.sum_eq_zero fun c _ => if_neg fun hc => h (hc.1.symm.trans hc.2)

theorem sum_lineSign {p q r s : ℕ} (c : Ix r s) :
    ∑ a : Ix p q, lineSign a c = ((p : ℂ) - q) * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c := by
  rcases c with c | c <;> simp [Fintype.sum_sum_type, lineSign] <;> ring

theorem fockAct2_diagonal_one (p q r s : ℕ) (D : Ix r s → ℂ) :
    fockAct2 p q r s (Matrix.diagonal D) (1 : Formalism.BasicNotions.TH.Pol p q r s) =
    ((((p : ℂ) - q) / 2) * ∑ c, D c * Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) c) • (1 : Formalism.BasicNotions.TH.Pol p q r s) := by
  have h1 : (1 : Formalism.BasicNotions.TH.Pol p q r s) = MvPolynomial.monomial 0 1 := rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [diagonal_eq_sum_Eab, map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, LinearMap.smul_apply, h1, cartan2, smul_smul]
  congr 1
  simp only [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_add]
  rw [← Finset.sum_mul, sum_lineSign]
  ring

end GlobalTheory.VacuumWeight
end

