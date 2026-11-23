module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0368
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0087
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TemperedProducts.CentredSegSqInt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0345
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0355
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0374
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0364
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0347
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0357
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0047
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0045
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0237
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0004
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
public import GroundTheory.GlobalFields.KummerTheory.LocalIndexAtPlace

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirEqOfSingularWeightVector
section
set_option maxSynthPendingDepth 1

noncomputable section

open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

variable {n : ℕ}

theorem cas_mul_sub_mem_Jp (y : U n) (τ : Fin n → ℂ)
    (hd : ∀ k, e (k, k) * y - τ k • y ∈ Jp n)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → e a * y ∈ Jp n) :
    Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * y - casC τ • y ∈ Jp n := by
  have key : ∀ a b : Fin n, e (a, b) * e (b, a) * y -
      ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y ∈ Jp n := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · have hc : e (a, b) * e (b, a) - e (b, a) * e (a, b) = e (a, a) - e (b, b) := by
        simpa using e_mul_sub_mul (a, b) (b, a)
      have hcomm : e (a, b) * e (b, a) = e (b, a) * e (a, b) + (e (a, a) - e (b, b)) := by
        rw [← hc]; abel
      have hval : e (a, b) * e (b, a) * y -
          ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y =
          e (b, a) * (e (a, b) * y) + (e (a, a) * y - τ a • y) - (e (b, b) * y - τ b • y) := by
        rw [if_neg h.ne, if_pos h, hcomm, zero_add, sub_smul]
        simp only [add_mul, sub_mul, mul_assoc]
        abel
      rw [hval]
      exact Submodule.sub_mem _ (Submodule.add_mem _ (mul_mem_Jp _ (hu _ h)) (hd a)) (hd b)
    · subst h
      have hval : e (a, a) * e (a, a) * y -
          ((if a = a then τ a ^ 2 else 0) + (if a < a then τ a - τ a else 0)) • y =
          e (a, a) * (e (a, a) * y - τ a • y) + τ a • (e (a, a) * y - τ a • y) := by
        simp only [if_true, lt_irrefl, if_false, add_zero, mul_sub, mul_smul_comm, smul_sub,
          smul_smul, mul_assoc, pow_two]
        abel
      rw [hval]
      exact Submodule.add_mem _ (mul_mem_Jp _ (hd a)) (Submodule.smul_mem _ _ (hd a))
    · have hval : e (a, b) * e (b, a) * y -
          ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y =
          e (a, b) * (e (b, a) * y) := by
        rw [if_neg h.ne', if_neg h.not_gt]
        simp [mul_assoc]
      rw [hval]
      exact mul_mem_Jp _ (hu _ h)
  have hsum : casC τ = ∑ a, ∑ b : Fin n,
      ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) := by
    simp only [casC, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hval : Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * y - casC τ • y =
      ∑ a, ∑ b : Fin n, (e (a, b) * e (b, a) * y -
        ((if a = b then τ a ^ 2 else 0) + (if a < b then τ a - τ b else 0)) • y) := by
    rw [hsum]
    simp only [Formalism.REAL.Cas, Finset.sum_mul, Finset.sum_smul, Finset.sum_sub_distrib]
  rw [hval]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => key a b

theorem cas_mul_comm (x : U n) :
    x * Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) =
      Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * x := by
  have hz : Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) ∈ Subalgebra.center ℂ (U n) :=
    mem_center_of_commute_e fun a => by
      obtain ⟨c, d⟩ := a
      exact (Formalism.FourierDecayAlt.P.WigCas.cas_comm (glRel_e n) c d).symm
  exact (Subalgebra.mem_center_iff.1 hz) x

theorem upper_e_mem_Jp (a : Fin n × Fin n) (ha : IsUpper a) : e a ∈ Jp n :=
  vermaIdeal_le_Jp (nPlusU_le_vermaIdeal _ (Submodule.subset_span ⟨1, a, ha, one_mul _⟩))

theorem e_sub_rho_mem_Jp (u : U n) (k : Fin n) : u * e (k, k) - rhoVec n k • u ∈ Jp n := by
  have h := vermaIdeal_le_Jp (mul_e_sub_mem_vermaIdeal (rhoVec n) u k)
  have hv : u * (e (k, k) - algebraMap ℂ (U n) (rhoVec n k)) = u * e (k, k) - rhoVec n k • u := by
    rw [mul_sub, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  rwa [hv] at h

theorem casC_rho_add_eq (μ : Fin n → ℤ) (x : U n) (hw : IsAdW μ x)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n) (hx : x ∉ Jp n) :
    casC (fun k => rhoVec n k + (μ k : ℂ)) = casC (rhoVec n) := by
  have h1 := cas_mul_sub_mem_Jp (1 : U n) (rhoVec n)
    (fun k => by simpa using e_sub_rho_mem_Jp (1 : U n) k) (fun a ha => by
      rw [mul_one]; exact upper_e_mem_Jp a ha)
  have h2 := cas_mul_sub_mem_Jp x (fun k => rhoVec n k + (μ k : ℂ)) (fun k => by
    have hv : e (k, k) * x - (rhoVec n k + (μ k : ℂ)) • x = x * e (k, k) - rhoVec n k • x := by
      have := hw k
      rw [add_smul, ← this]; abel
    rw [hv]; exact e_sub_rho_mem_Jp x k) hu
  have h3 := mul_mem_Jp x h1
  have hv : x * (Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * 1 - casC (rhoVec n) • (1 : U n)) -
      (Formalism.REAL.Cas (fun a b : Fin n => e (a, b)) * x -
        casC (fun k => rhoVec n k + (μ k : ℂ)) • x) =
      (casC (fun k => rhoVec n k + (μ k : ℂ)) - casC (rhoVec n)) • x := by
    rw [mul_one, mul_sub, cas_mul_comm, mul_smul_comm, mul_one, sub_smul]; abel
  have h4 := Submodule.sub_mem _ h3 h2
  rw [hv] at h4
  by_contra hne
  apply hx
  have hc : casC (fun k => rhoVec n k + (μ k : ℂ)) - casC (rhoVec n) ≠ 0 := sub_ne_zero.2 hne
  have := Submodule.smul_mem _ (casC (fun k => rhoVec n k + (μ k : ℂ)) - casC (rhoVec n))⁻¹ h4
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

end GlobalTheory.CompanionTheory.PresRho
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentredSegmentSquareIntegrable
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.SegLink

theorem one_le_deg_of_isLSeg {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {Δ : Segment k} {y : IrrGL (k := k)} (hL : IsLSeg Δ y.rep) : 1 ≤ y.1 := by
  obtain ⟨hd, -⟩ := hL
  have hterm : ∀ a, (Δ.term a).fst = Δ.d := fun a => rfl
  rw [← hd]
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.mul_pos Δ.len_pos Δ.d_pos

theorem norm_top_eq (r A : ℝ) (d d0 l0 l1 m : ℕ) (h : d0 = d) :
    (r * (A ^ l1) ^ d) ^ l0 * (A ^ d0) ^ m = r ^ l0 * A ^ (d * (l0 * l1 + m)) := by
  subst h
  ring

theorem centredSegSqInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    Zls.CasselmanSuffSq k → GlobalTheory.Published.IrreducibleAdmissibleGL → Zc.LSegJacquet k → Zz.CentredSegSqInt k := by
  intro k _ _ _ _ hCas hIA hLJ Δ y hL hU
  have hN : 1 ≤ y.1 := one_le_deg_of_isLSeg hL
  have hmax : Zls.MaxExpStrict y.rep := by
    intro x hd hpos hjm t ht c hc
    obtain ⟨Γ, ⟨hlen, hfirst⟩, hΓ⟩ := GlobalTheory.T.segment_jacquet_two_factor_split k Δ y.1 _ y.rep hLJ hL x hd hpos hjm
    obtain ⟨hα0, hα1, hnorm⟩ := _root_.GlobalTheory.CompanionTheory.TopNilp.nabs_absPow_of_tendsto_zero k t ht
    obtain ⟨c0, hc0⟩ := _root_.GlobalTheory.CompanionTheory.SchurCentre.scalar_acts_by_scalar k Δ.first.fst _ Δ.first.rep Δ.first.snd.rep.smooth
      Δ.first.snd.rep.irr (hIA k _ _ _ Δ.first.snd.rep.smooth Δ.first.snd.rep.irr) t
    obtain ⟨cy, hcy⟩ := _root_.GlobalTheory.CompanionTheory.SchurCentre.scalar_acts_by_scalar k y.fst _ y.rep y.snd.rep.smooth y.snd.rep.irr
      (hIA k _ _ _ y.snd.rep.smooth y.snd.rep.irr) t
    have hprod := GlobalTheory.T.jacquet_two_factor_central_character_mul k y.fst _ y.rep x hd hjm t cy (c 0) (c 1) hcy (hc 0) (hc 1)
    have hcy1 : ‖cy‖ = 1 := hU t cy hcy
    have hy1 := hU t _ (GlobalTheory.T.segment_rep_central_character_formula k Δ y hL t c0 hc0)
    rw [norm_mul, norm_pow, norm_pow, hnorm, ← pow_mul] at hy1
    have hr : 0 < ‖c0‖ := by
      rcases (norm_nonneg c0).lt_or_eq with h | h
      · exact h
      · exfalso
        rw [← h, zero_pow (Nat.pos_iff_ne_zero.mp Δ.len_pos), zero_mul] at hy1
        exact zero_ne_one hy1
    have hlen2 : (Γ 0).len + (Γ 1).len = Δ.len := by rw [← hlen, Fin.sum_univ_two]
    rw [← hlen2] at hy1
    have hb0 : Zc.below Γ 0 = (Γ 1).len := by
      simp [Zc.below, Finset.sum_filter, Fin.sum_univ_two]
    have hf0 : (Γ 0).first.fst = Δ.first.fst := by rw [hfirst 0]; rfl
    have hG0 : Zl.ScalarBy (Γ 0).first t
        (c0 * ↑((GlobalTheory.SmGL.absPow k ↑(Zc.below Γ 0)) t) ^ Δ.first.fst) := by
      rw [hfirst 0]
      exact GlobalTheory.T.central_character_twist_pow_degree k Δ.first t c0 _ hc0
    have he0 := GlobalTheory.T.central_character_eq_of_scalar k (x 0) t _ _ (hc 0) (GlobalTheory.T.segment_rep_central_character_formula k (Γ 0) (x 0) (hΓ 0) t _ hG0)
    have hn0 : ‖c 0‖ = ‖c0‖ ^ (Γ 0).len * GlobalTheory.SplitWeil.nabs k t ^
        (Δ.first.fst * ((Γ 0).len * (Γ 1).len + (Γ 0).len * ((Γ 0).len - 1) / 2)) := by
      rw [he0, norm_mul, norm_pow, norm_mul, norm_pow, norm_pow, hnorm, hnorm, hb0]
      exact norm_top_eq _ _ _ _ _ _ _ hf0
    refine ⟨?_, ?_⟩
    · intro j hj
      have hj0 : j = 0 := Fin.ext (by omega)
      subst hj0
      have hp : (∏ i ∈ Finset.univ.filter (fun i : Fin 2 => i ≤ 0), ‖c i‖) = ‖c 0‖ := by
        simp [Finset.prod_filter, Fin.prod_univ_two]
      rw [hp, hn0]
      exact _root_.GlobalTheory.CompanionTheory.Segment.top_piece_exponent_lt_one _ _ _ _ _ hα0 hα1 hr Δ.d_pos (Γ 0).len_pos (Γ 1).len_pos hy1
    · rw [Fin.prod_univ_two, ← norm_mul, hprod, hcy1]
  exact @hCas y.1 _ _ _ y.rep hN y.snd.rep.smooth y.snd.rep.irr (fun t c hc => hU t c hc) hmax

end GlobalTheory.CompanionTheory.SegLink
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoFunSmooth
section
open GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory.CompanionTheory.CIndCoinv

section Abstract

variable {G M W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
  [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def coFun (s : M →* G) (χ : M →* ℂˣ) (c : W →ₗ[ℂ] W') (f : G → W) (x : M) : W' :=
  (χ x : ℂ) • c (f (s x))

theorem coFun_mem {H : Subgroup G} {Q : Subgroup M} (s : M →* G) (hQH : ∀ p ∈ Q, s p ∈ H) (χ : M →* ℂˣ)
    (σ : Representation ℂ H W) (σ' : Representation ℂ Q W') (c : W →ₗ[ℂ] W')
    (hcomp : ∀ (p : Q) (w : W), (χ p : ℂ) • c (σ ⟨s p, hQH p p.2⟩ w) = σ' p (c w)) (f : indSpace H σ) :
    coFun s χ c f.1 ∈ indSpace Q σ' := by
  intro p x
  have h1 : f.1 (s p * s x) = σ ⟨s p, hQH p p.2⟩ (f.1 (s x)) := f.2 ⟨s p, hQH p p.2⟩ (s x)
  show ((χ ((p : M) * x) : ℂˣ) : ℂ) • c (f.1 (s ((p : M) * x))) = σ' p (((χ x : ℂˣ) : ℂ) • c (f.1 (s x)))
  rw [map_mul, map_mul, h1, map_smul, ← hcomp, Units.val_mul, mul_comm, mul_smul]

theorem coFun_smooth {H : Subgroup G} {Q : Subgroup M} (s : M →* G) (hs : Continuous s) (hQH : ∀ p ∈ Q, s p ∈ H)
    (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (σ : Representation ℂ H W) (σ' : Representation ℂ Q W') (c : W →ₗ[ℂ] W')
    (hcomp : ∀ (p : Q) (w : W), (χ p : ℂ) • c (σ ⟨s p, hQH p p.2⟩ w) = σ' p (c w)) (f : smoothPart (ind H σ)) :
    (⟨coFun s χ c f.1.1, coFun_mem s hQH χ σ σ' c hcomp f.1⟩ : indSpace Q σ') ∈ smoothPart (ind Q σ') := by
  refine mem_smoothPart_of_nhds (Filter.mem_of_superset
    (((IsOpen.preimage hs f.2).inter hχ).mem_nhds ?_) ?_)
  · refine ⟨?_, one_mem _⟩
    simp
  · rintro x ⟨h1, h2⟩
    have h1' : ind H σ (s x) f.1 = f.1 := h1
    have h2' : χ x = 1 := h2
    apply Subtype.ext
    funext y
    show ((χ (y * x) : ℂˣ) : ℂ) • c (f.1.1 (s (y * x))) = ((χ y : ℂˣ) : ℂ) • c (f.1.1 (s y))
    have h3 : f.1.1 (s y * s x) = f.1.1 (s y) := congrFun (congrArg Subtype.val h1') (s y)
    rw [map_mul, map_mul, h2', mul_one, h3]

end Abstract

section Abstract2

variable {G M W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
  [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def coMap {H : Subgroup G} {Q : Subgroup M} (s : M →* G) (hs : Continuous s) (hQH : ∀ p ∈ Q, s p ∈ H)
    (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (σ : Representation ℂ H W) (σ' : Representation ℂ Q W') (c : W →ₗ[ℂ] W')
    (hcomp : ∀ (p : Q) (w : W), (χ p : ℂ) • c (σ ⟨s p, hQH p p.2⟩ w) = σ' p (c w)) :
    cIndSpace H σ →ₗ[ℂ] smoothPart (ind Q σ') where
  toFun f := ⟨⟨coFun s χ c f.1.1.1, coFun_mem s hQH χ σ σ' c hcomp f.1.1⟩, coFun_smooth s hs hQH χ hχ σ σ' c hcomp f.1⟩
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    show ((χ x : ℂˣ) : ℂ) • c (a.1.1.1 (s x) + b.1.1.1 (s x)) = _
    rw [map_add (f := _), smul_add]
    rfl
  map_smul' r a := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    show ((χ x : ℂˣ) : ℂ) • c (r • a.1.1.1 (s x)) = r • (((χ x : ℂˣ) : ℂ) • c (a.1.1.1 (s x)))
    rw [map_smul, smul_comm]

theorem coinv_equiv (H U : Subgroup G) (Q : Subgroup M) (s : M →* G) (q : G →* M)
    (hH : IsClosed (H : Set G))
    (hbasis : ∀ O : Set G, O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hs : Continuous s) (hq : Continuous q) (hqs : ∀ x, q (s x) = x) (hker : ∀ g, q g = 1 ↔ g ∈ U)
    (hUH : U ≤ H) (hHQ : ∀ g ∈ H, q g ∈ Q) (hQH : ∀ p ∈ Q, s p ∈ H)
    (C : Set M) (hC : IsCompact C) (hMC : ∀ x : M, ∃ p ∈ Q, ∃ y ∈ C, x = p * y)
    (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (σ : Representation ℂ H W) (hσ : IsSmooth σ) (σ' : Representation ℂ Q W')
    (c : W →ₗ[ℂ] W') (hc : Function.Surjective c) (hck : ∀ w, c w = 0 ↔ w ∈ twKer σ (U.subgroupOf H) 1)
    (hcomp : ∀ (p : Q) (w : W), (χ p : ℂ) • c (σ ⟨s p, hQH p p.2⟩ w) = σ' p (c w))
    (hK : ∀ f : cIndSpace H σ, (∀ g, f.1.1.1 g ∈ twKer σ (U.subgroupOf H) 1) → f ∈ twKer (cInd H σ) U 1) :
    ∃ E : (cIndSpace H σ ⧸ twKer (cInd H σ) U 1) ≃ₗ[ℂ] smoothPart (ind Q σ'),
      ∀ (f : cIndSpace H σ) (x : M), (E (Submodule.Quotient.mk f)).1.1 x = (χ x : ℂ) • c (f.1.1.1 (s x)) := by
  classical
  haveI hUn : U.Normal := by
    have : U = q.ker := by
      ext g
      rw [MonoidHom.mem_ker, hker]
    rw [this]
    infer_instance
  have hcu : ∀ (u : G) (hu : u ∈ U) (w : W), c (σ ⟨u, hUH hu⟩ w) = c w := by
    intro u hu w
    have : σ ⟨u, hUH hu⟩ w - w ∈ twKer σ (U.subgroupOf H) 1 :=
      Submodule.subset_span ⟨⟨⟨u, hUH hu⟩, hu⟩, w, by simp⟩
    have h2 := (hck _).2 this
    rwa [map_sub, sub_eq_zero] at h2
  have hdec : ∀ g : G, g * (s (q g))⁻¹ ∈ U := by
    intro g
    rw [← hker, map_mul, map_inv, hqs, mul_inv_cancel]
  set Φ := coMap s hs hQH χ hχ σ σ' c hcomp with hΦ
  have hkill : twKer (cInd H σ) U 1 ≤ LinearMap.ker Φ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, f, rfl⟩
    show Φ _ = 0
    apply Subtype.ext
    apply Subtype.ext
    funext x
    have hn : s x * u * (s x)⁻¹ ∈ U := hUn.conj_mem _ u.2 _
    have e : (cInd H σ (u : G) f).1.1.1 (s x) = σ ⟨_, hUH hn⟩ (f.1.1.1 (s x)) := by
      have := f.1.1.2 ⟨_, hUH hn⟩ (s x)
      rw [← this]
      show f.1.1.1 (s x * u) = f.1.1.1 (s x * u * (s x)⁻¹ * s x)
      congr 1
      group
    show ((χ x : ℂˣ) : ℂ) • c ((cInd H σ (u : G) f - ((1 : U →* ℂˣ) u : ℂ) • f).1.1.1 (s x)) = 0
    have e2 : (cInd H σ (u : G) f - ((1 : U →* ℂˣ) u : ℂ) • f).1.1.1 (s x)
        = (cInd H σ (u : G) f).1.1.1 (s x) - f.1.1.1 (s x) := by
      simp
    rw [e2, e, map_sub, hcu _ hn, sub_self, smul_zero]
  have hinj : ∀ f : cIndSpace H σ, Φ f = 0 → f ∈ twKer (cInd H σ) U 1 := by
    intro f hf
    refine hK f fun g => ?_
    rw [← hck]
    have h1 : ∀ x, c (f.1.1.1 (s x)) = 0 := by
      intro x
      have h2 : ((χ x : ℂˣ) : ℂ) • c (f.1.1.1 (s x)) = 0 := by
        have := congrArg (fun F : smoothPart (ind Q σ') => F.1.1 x) hf
        exact this
      exact (smul_eq_zero.1 h2).resolve_left (Units.ne_zero _)
    have h3 : f.1.1.1 g = σ ⟨_, hUH (hdec g)⟩ (f.1.1.1 (s (q g))) := by
      rw [← f.1.1.2 ⟨_, hUH (hdec g)⟩ (s (q g))]
      congr 1
      group
    rw [h3, hcu _ (hdec g), h1]
  have hmemH : ∀ g, q g ∈ Q → g ∈ H := by
    intro g hg
    have : g = (g * (s (q g))⁻¹) * s (q g) := by group
    rw [this]
    exact mul_mem (hUH (hdec g)) (hQH _ hg)
  let qH : H →* Q := (q.comp H.subtype).codRestrict Q fun h => hHQ h h.2
  let σb : Representation ℂ H W' := twist (σ'.comp qH) (χ.comp (q.comp H.subtype))⁻¹
  have hσb : ∀ (h : H) (w : W'), σb h w = (((χ (q h))⁻¹ : ℂˣ) : ℂ) • σ' (qH h) w := fun h w => rfl
  have hcb : ∀ (h : H) (w : W), c (σ h w) = σb h (c w) := by
    intro h w
    have hp : q h ∈ Q := hHQ h h.2
    have e : h = ⟨_, hUH (hdec h)⟩ * ⟨s (q h), hQH _ hp⟩ := by
      apply Subtype.ext
      show (h : G) = (h : G) * (s (q h))⁻¹ * s (q h)
      group
    have e1 : c (σ h w) = c (σ ⟨s (q h), hQH _ hp⟩ w) := by
      conv_lhs => rw [e, map_mul, Module.End.mul_apply]
      rw [hcu _ (hdec h)]
    rw [e1, hσb]
    have := hcomp ⟨q h, hp⟩ w
    show _ = (((χ (q h))⁻¹ : ℂˣ) : ℂ) • σ' ⟨q h, hp⟩ (c w)
    rw [← this, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hsurj : ∀ φ : smoothPart (ind Q σ'), ∃ f, Φ f = φ := by
    intro φ
    let b : G → W' := fun g => (((χ (q g))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q g)
    have hb : b ∈ indSpace H σb := by
      intro h g
      have h1 : φ.1.1 (q h * q g) = σ' (qH h) (φ.1.1 (q g)) := φ.1.2 (qH h) (q g)
      show (((χ (q ((h : G) * g)))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q ((h : G) * g)) = σb h ((((χ (q g))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q g))
      rw [map_mul, h1, map_smul, hσb, map_mul, mul_inv, Units.val_mul, smul_smul, mul_comm]
    have hbs : (⟨b, hb⟩ : indSpace H σb) ∈ smoothPart (ind H σb) := by
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset
        (((IsOpen.preimage hq φ.2).inter (IsOpen.preimage hq hχ)).mem_nhds ?_) ?_)
      · refine ⟨?_, ?_⟩
        · simp
        · simp
      · rintro x ⟨h1, h2⟩
        have h1' : ind Q σ' (q x) φ.1 = φ.1 := h1
        have h2' : χ (q x) = 1 := h2
        apply Subtype.ext
        funext y
        show (((χ (q (y * x)))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q (y * x)) = (((χ (q y))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q y)
        have h3 : φ.1.1 (q y * q x) = φ.1.1 (q y) := congrFun (congrArg Subtype.val h1') (q y)
        rw [map_mul, map_mul, h2', mul_one, h3]
    have hbc : (⟨⟨b, hb⟩, hbs⟩ : smoothPart (ind H σb)) ∈ cIndSpace H σb := by
      refine ⟨s '' C, hC.image hs, fun g _ => ?_⟩
      obtain ⟨p, hp, y, hy, e⟩ := hMC (q g)
      refine ⟨g * (s y)⁻¹, hmemH _ ?_, s y, ⟨y, hy, rfl⟩, by group⟩
      rw [map_mul, map_inv, hqs, e]
      simpa using hp
    obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.BZMirOnto.cInd_lift H hH hbasis σ σb c hc hcb (fun w _ => by
      let S : Subgroup H :=
        { carrier := {h | σ h w = w}
          one_mem' := by simp
          mul_mem' := fun {a b} ha hb => by
            simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
            rw [hb, ha]
          inv_mem' := fun {a} ha => by
            simp only [Set.mem_setOf_eq] at *
            conv_lhs => rw [← ha]
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
      exact ⟨S, hσ w, fun t ht _ => ht⟩) ⟨⟨⟨b, hb⟩, hbs⟩, hbc⟩
    refine ⟨F, Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
    show ((χ x : ℂˣ) : ℂ) • c (F.1.1.1 (s x)) = φ.1.1 x
    rw [hF]
    show ((χ x : ℂˣ) : ℂ) • ((((χ (q (s x)))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q (s x))) = φ.1.1 x
    rw [hqs, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  let L := (twKer (cInd H σ) U 1).liftQ Φ hkill
  have hL : Function.Bijective L := by
    constructor
    · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact (Submodule.Quotient.mk_eq_zero _).2 (hinj f hx)
    · intro φ
      obtain ⟨f, hf⟩ := hsurj φ
      exact ⟨Submodule.Quotient.mk f, hf⟩
  exact ⟨LinearEquiv.ofBijective L hL, fun f x => rfl⟩

end Abstract2

end GlobalTheory.CompanionTheory.CIndCoinv
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommuteLeviBoundaryAndLift
section
noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.PairMult.CapProdProof

open Formalism.REAL (GlRel qdet)
open CompanionTheory.D.LK (Pos)
open GlobalTheory.CompanionTheory.RgCOBlock (fa fb sz)

variable {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

theorem commute_ev (T : Module.End ℂ W) (E : Fin n → Fin n → Module.End ℂ W) (h : ∀ p q, Commute T (E p q))
    (z : FreeAlgebra ℂ (Fin n × Fin n)) : Commute T (CompanionTheory.D.LK.ev E z) := by
  induction z using FreeAlgebra.induction with
  | grade0 r => rw [AlgHom.commutes]; exact (Algebra.commutes r T).symm
  | grade1 p => simpa [CompanionTheory.D.LK.ev] using h p.1 p.2
  | mul a b ha hb => rw [map_mul]; exact ha.mul_right hb
  | add a b ha hb => rw [map_add (f := _)]; exact ha.add_right hb

end GlobalTheory.CompanionTheory.PairMult.CapProdProof
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DecompositionGroupLocalGalois
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Dict

theorem isFrob_of_unramifiedDegree_eq_one : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) [IsSepClosure (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F))], IsPlaceOver A v → ∀ (ι : Ω →ₐ[F] AlgebraicClosure (v.adicCompletion F)) (σ : G F Ω) (g : Gal(AlgebraicClosure (v.adicCompletion F)/v.adicCompletion F)), σ ∈ Dec (F := F) A → (∀ x, ι (σ x) = g (ι x)) → unramifiedDegree (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) g = Multiplicative.ofAdd 1 → IsFrob (F := F) A (normV v) σ := by
  intro F Ω _ _ _ _ _ A v _ hA ι σ g hσ hι hg
  refine (GlobalTheory.FrobTeich.isFrob_iff_teichmuller F Ω A v hA σ).2 ⟨hσ, fun z m hm hz => ?_⟩
  have hcard : Nat.card 𝓀[v.adicCompletion F] = normV v := by
    rw [GroundTheory.Global.natCard_residueField_adicCompletion, Ideal.absNorm_apply,
      Submodule.cardQuot_apply]
    rfl
  have hfrob := (unramifiedDegree_eq_ofAdd_one_iff g).1 hg
  rw [hcard] at hfrob
  have hq : 1 < normV v := hcard ▸ one_lt_card_residueField (v.adicCompletion F)
  suffices h : ι (σ z) = ι (z ^ normV v) from (RingHom.injective ι.toRingHom) h
  rw [hι, map_pow]
  have hξ : (ι z) ^ normV v ^ m = ι z := by rw [← map_pow, hz]
  by_cases h0 : ι z = 0
  · rw [h0, map_zero, zero_pow (by omega)]
  · refine hfrob _ ⟨m, hm.ne', mul_right_cancel₀ h0 ?_⟩
    have e : normV v ^ m = (normV v ^ m - 1) + 1 :=
      (Nat.sub_add_cancel (Nat.one_le_pow _ _ (by omega))).symm
    rw [hcard, ← pow_succ, ← e, hξ, one_mul]

end GlobalTheory.CompanionTheory.Dict
end
end

