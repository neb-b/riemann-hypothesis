module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0182
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0162
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0176
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0004
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.FrobeniusOrbits.RealSubfieldLeCompositum
public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.Statement
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import ReciprocityTheory.GaloisValuations.ContinuousConstSMulQuotient

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedCuspEigenformEigenvalueEqCharMulConj
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisMReal

theorem qs_smul (c : ℂ) (a : ℕ → ℂ) : qs (fun n => c * a n) = fun τ => c * qs a τ := by
  funext τ
  unfold qs
  rw [← tsum_mul_left]
  congr 1
  funext n
  ring

theorem pet_smul_right (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) (c : ℂ) :
    pet k ρ h (fun τ => c * f τ) = c * pet k ρ h f := by
  unfold pet
  rw [← integral_const_mul]
  congr 1
  funext τ
  ring

theorem pet_smul_left (k : ℕ) (ρ : ℍ → ℝ) (h f : ℍ → ℂ) (c : ℂ) :
    pet k ρ (fun τ => c * h τ) f = conj c * pet k ρ h f := by
  unfold pet
  rw [← integral_const_mul]
  congr 1
  funext τ
  simp only [map_mul]
  ring

theorem eig_conj : ∀ (k N q : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ), 1 ≤ k → 0 < N → Prim k N χ g →
    q.Prime → ¬ q ∣ N → g q = ch χ q * conj (g q) := by
  intro k N q χ g hk hN hg hq hqN
  obtain ⟨ρ, hρ⟩ := _root_.GlobalTheory.wt_exists N hN
  have hT : To k (ch χ q) q g = fun n => g q * g n := hg.eig q hq hqN
  have hadj := _root_.GlobalTheory.EisM.pet_To_adjoint k N N q χ ρ g g hk hN dvd_rfl hq hqN hρ hg.cf hg.cf.1
  have hne : g ≠ 0 := by
    intro h0
    have := hg.one
    rw [h0] at this
    simp at this
  have hP := _root_.GlobalTheory.EisM.PetPos.pet_self_ne_zero k N N χ ρ g hk hN dvd_rfl hρ hg.cf hne
  rw [hT, qs_smul, pet_smul_right, pet_smul_left] at hadj
  exact mul_right_cancel₀ hP (hadj.trans (by ring) : g q * pet k ρ (qs g) (qs g) = ch χ q * conj (g q) * pet k ρ (qs g) (qs g))

end GlobalTheory.EisMReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlmostGaloisCoordinatesStatement
section
open GlobalTheory.K5 GlobalTheory.KumDlog
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_almostGalois_coordinates : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω) (n : ℕ) (r : Ω), IsInt (p := p) r → (∀ h ∈ Hinf T, ∃ i : ℕ, h r = T.ζ n ^ i * r) →
  ∃ (ι : Type) (_ : Fintype ι) (u v : ι → Ω), (∀ k, u k ∈ FixI (Hfix T r)) ∧ (∀ k, v k ∈ FixI (Hfix T r)) ∧
  ∑ k, u k * v k = (p : Ω) ∧ ∀ h ∈ Hinf T, h r ≠ r → ∑ k, u k * h (v k) = 0 := by
  first | exact @GlobalTheory.KumDlog.almostGal_coord | exact GlobalTheory.KumDlog.almostGal_coord | (intros; apply GlobalTheory.KumDlog.almostGal_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHeckeEigenfunctionalOfDepletedEigenform
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem eigF_of_prim : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (ρ : ℍ → ℝ) (α β : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → Prim k N χ g → Wt (N * l) ρ → α + β = χ⁻¹ l * g l → α * β = χ⁻¹ l * (l : ℂ) ^ (k - 1) → ∃ (B : ℕ) (c : ℕ → ℂ), EigF k N l χ⁻¹ (fun q => χ⁻¹ q * g q) α B c ∧ ∀ a, MF k (N * l) (ch χ⁻¹) a → lam B c a = pet k ρ (qs (Vo l fun n => conj (g n))) (qs a) - β / (l : ℂ) ^ k * pet k ρ (qs fun n => conj (g n)) (qs a) := by
  intro k N l χ g ρ α β hk hN hl hlN hg hρ hab hαβ
  haveI : NeZero N := ⟨by omega⟩
  set h : ℕ → ℂ := fun n => conj (g n) with hh_def
  have hNl : 0 < N * l := Nat.mul_pos hN hl.pos
  have hdvd : N ∣ N * l := dvd_mul_right N l
  have hP : Prim k N χ⁻¹ h := (_root_.GlobalTheory.EisM.ConjForm.conj_form k N χ g).2 hg
  have hMFh : MF k N (ch χ⁻¹) h := hP.cf.1
  have lin := _root_.GlobalTheory.EisM.mf_linear k (N * l) (ch χ⁻¹)
  have hCFh : CF k (N * l) (ch χ⁻¹) h := (_root_.GlobalTheory.EisM.mf_linear k N (ch χ⁻¹)).2.2.2.2.2 (N * l) h hdvd hP.cf
  have hCFV : CF k (N * l) (ch χ⁻¹) (Vo l h) := (_root_.GlobalTheory.Vo_level k N l (ch χ⁻¹) h hl.pos).2 hP.cf
  have petlin := _root_.GlobalTheory.EisM.pet_linear k (N * l) (N * l) N χ⁻¹ ρ hk hNl hdvd hρ

  have hsc : ∀ (h' a : ℕ → ℂ) (x : ℂ), CF k (N * l) (ch χ⁻¹) h' → MF k (N * l) (ch χ⁻¹) a →
      pet k ρ (qs (x • h')) (qs a) = conj x * pet k ρ (qs h') (qs a) := by
    intro h' a x hh' ha
    have e : qs (x • h') = fun τ => x * qs h' τ + 0 * qs h' τ := by
      rw [(lin.2.2.1 x h' hh'.1).2]; funext τ; simp
    rw [e, petlin.2 h' h' a x 0 hh' hh' ha.1]; simp
  have hconj : ∀ x : ZMod N, conj (χ x) = χ⁻¹ x := fun x => MulChar.star_apply' χ x
  have hch : ∀ n : ℕ, ch χ⁻¹ (n : ℤ) = χ⁻¹ (n : ZMod N) := by intro n; simp [ch]
  set φ : (ℕ → ℂ) → ℂ := fun a => pet k ρ (qs (Vo l h)) (qs a) - β / (l : ℂ) ^ k * pet k ρ (qs h) (qs a) with hφ_def
  obtain ⟨B, hB⟩ := _root_.GlobalTheory.EisM.sturm_coef_zero k (N * l) N χ⁻¹ hNl hdvd
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.func_eq_lam {a | MF k (N * l) (ch χ⁻¹) a} B φ lin.1
    (by
      intro a ha b hb
      refine ⟨(lin.2.1 a b ha hb).1, ?_⟩
      have e1 := petlin.1 (Vo l h) a b 1 1 hCFV ha.1 hb.1
      have e2 := petlin.1 h a b 1 1 hCFh ha.1 hb.1
      simp only [one_smul, one_mul] at e1 e2
      simp only [hφ_def, e1, e2]; ring)
    (by
      intro x a ha
      refine ⟨(lin.2.2.1 x a ha).1, ?_⟩
      have e1 := petlin.1 (Vo l h) a a x 0 hCFV ha.1 ha.1
      have e2 := petlin.1 h a a x 0 hCFh ha.1 ha.1
      simp only [zero_smul, add_zero, zero_mul] at e1 e2
      simp only [hφ_def, e1, e2]; ring)
    hB
  have hφ : ∀ a, MF k (N * l) (ch χ⁻¹) a → lam B c a = φ a := fun a ha => (hc a ha).symm
  refine ⟨B, c, ⟨?_, ?_⟩, hφ⟩
  ·
    intro a ha q hq hqNl
    have hqN : ¬ q ∣ N := fun d => hqNl (dvd_mul_of_dvd_left d l)
    have hql : q ≠ l := fun e => hqNl (e ▸ dvd_mul_left q N)
    have hcop : q.Coprime l := (Nat.coprime_primes hq hl).2 hql
    have hTa := _root_.GlobalTheory.EisM.To_MF k (N * l) N q χ⁻¹ a hk hdvd hq hqNl ha
    rw [hφ _ hTa, hφ _ ha]
    have eigh : To k (ch χ⁻¹ q) q h = h q • h := by
      rw [hP.eig q hq hqN]; funext n; simp
    have eigV : To k (ch χ⁻¹ q) q (Vo l h) = h q • Vo l h := by
      rw [(_root_.GlobalTheory.EisM.formal_identities ℂ l hl.pos).2.2.2.2.1 k q _ h hcop hq.pos, eigh]
      funext n; simp only [Vo, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp
    have adj0 := _root_.GlobalTheory.EisM.pet_To_adjoint k (N * l) N q χ⁻¹ ρ h a hk hNl hdvd hq hqNl hρ hCFh ha
    have adj1 := _root_.GlobalTheory.EisM.pet_To_adjoint k (N * l) N q χ⁻¹ ρ (Vo l h) a hk hNl hdvd hq hqNl hρ hCFV ha
    rw [eigh, hsc h a _ hCFh ha] at adj0
    rw [eigV, hsc (Vo l h) a _ hCFV ha] at adj1
    have hgq : conj (h q) = g q := by simp [hh_def]
    simp only [hφ_def]
    rw [adj0, adj1]
    simp only [hgq, hch]
    ring
  ·
    intro a ha
    have hper : ∀ d : ℤ, ch χ⁻¹ (d + ((N * l : ℕ) : ℤ)) = ch χ⁻¹ d := by
      intro d; simp only [ch]; congr 1; push_cast; simp
    have hUa := (_root_.GlobalTheory.depletion_mf k (N * l) l (ch χ⁻¹) a hk hl (dvd_mul_left l N) hper ha).1
    rw [hφ _ hUa, hφ _ ha]
    have adjU0 := _root_.GlobalTheory.adjoint_U k (N * l) N l χ⁻¹ ρ h a hk hNl hdvd hl (dvd_mul_left l N) hlN hρ hCFh ha
    have adjU1 := _root_.GlobalTheory.adjoint_U k (N * l) N l χ⁻¹ ρ (Vo l h) a hk hNl hdvd hl (dvd_mul_left l N) hlN hρ hCFV ha
    have tr0 := GlobalTheory.T.sum_slash_heckeRepLowerLevel_eq_pow_mul_heckeV k N l χ⁻¹ h hk hl.pos hMFh
    have eigl : To k (ch χ⁻¹ l) l h = h l • h := by
      rw [hP.eig l hl hlN]; funext n; simp
    have tr1 := _root_.GlobalTheory.EisM.sum_slz_repL_Vo k N l χ⁻¹ h (h l) hk hN hl hlN hMFh eigl
    have f0 : (fun τ => ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs h) τ)
        = fun τ => ((l : ℂ) ^ k) * qs (Vo l h) τ + 0 * qs (Vo l h) τ := by
      funext τ; rw [tr0]; ring
    have f1 : (fun τ => ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ)
        = fun τ => (ch χ⁻¹⁻¹ l * h l) * qs (Vo l h) τ + (-(ch χ⁻¹⁻¹ l * (l : ℂ)⁻¹)) * qs h τ := by
      funext τ; rw [tr1]; ring
    rw [f0, petlin.2 (Vo l h) (Vo l h) a _ 0 hCFV hCFV ha.1] at adjU0
    rw [f1, petlin.2 (Vo l h) h a _ _ hCFV hCFh ha.1] at adjU1
    have e1 : conj (ch χ⁻¹⁻¹ (l : ℤ)) = χ⁻¹ (l : ZMod N) := by
      rw [inv_inv]; simp only [ch, Int.cast_natCast]; exact hconj _
    have hgl : conj (h l) = g l := by simp [hh_def]
    have hl0 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne_zero
    have key : (l : ℂ) ^ (k - 1) / (l : ℂ) ^ k = (l : ℂ)⁻¹ := by
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel, pow_succ]; field_simp
    simp only [map_mul, map_neg, map_inv₀, map_pow, Complex.conj_natCast, map_zero, e1, hgl, zero_mul, add_zero] at adjU0 adjU1
    simp only [hφ_def, adjU0, adjU1]
    set P0 := pet k ρ (qs h) (qs a)
    set P1 := pet k ρ (qs (Vo l h)) (qs a)
    have hcan : (l : ℂ) ^ k / (l : ℂ) ^ k = 1 := div_self (pow_ne_zero _ hl0)
    linear_combination (-P1) * hab + (P0 / (l : ℂ) ^ k) * hαβ + (χ⁻¹ (l : ZMod N) * P0) * key + (-β * P1) * hcan

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsCrisPOfIsCrisDR
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.FundSeq

def OntoAt (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ ι : Per.Bcris l →+* Per.BdR l, Per.IsCrisDR l ι →
    (∀ u : Per.Bcris l, ∃ x : Per.Bcris l, ι x ∈ Per.FilD l 0 ∧ x - Per.φB l x = u) ∧
    (∀ w : Per.BdR l, ∃ b : Per.Bcris l, Per.φB l b = b ∧ ι b - w ∈ Per.FilD l 0)

theorem pair_onto {B D : Type} [AddCommGroup B] [AddCommGroup D] (φ : B →+ B) (ι : B →+ D) (F : Set D)
    (h1 : ∀ u, ∃ x, x - φ x = u) (h2 : ∀ w, ∃ b, φ b = b ∧ ι b - w ∈ F) (u : B) (w : D) :
    ∃ x y, y ∈ F ∧ x - φ x = u ∧ ι x - y = w := by
  obtain ⟨x0, hx0⟩ := h1 u
  obtain ⟨b, hb, hF⟩ := h2 (w - ι x0)
  refine ⟨x0 + b, _, hF, ?_, ?_⟩
  · rw [map_add (f := _), hb, ← hx0]; abel
  · rw [map_add (f := _)]; abel

variable {l : ℕ} [Fact l.Prime]

theorem exists_restrict_aCris_bdRPlus {ι : Per.Bcris l →+* Per.BdR l} (h : Per.IsCrisDR l ι) :
    ∃ j : Per.Acris l →+* Per.BdRp l, IsCrisP j ∧ ∀ x : Per.Acris l,
      ι (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.BdRp l) (Per.BdR l) (j x) := by
  obtain ⟨j, h1, h2, h3⟩ := GlobalTheory.CrisIncl.exists_restrict l ι h
  exact ⟨j, ⟨h2, h3⟩, h1⟩

theorem eq_core_of_isCrisDR {ι : Per.Bcris l →+* Per.BdR l} (h : Per.IsCrisDR l ι) (C : Core l) :
    ι = C.ι := by
  obtain ⟨j, hj, hι⟩ := exists_restrict_aCris_bdRPlus h
  have e : j = C.j := (crisP_unique_equivariant l C.j C.j_cris).1 j hj
  refine GlobalTheory.RingIface.bcris_ext l fun x => ?_
  rw [hι, C.ι_j, e]

theorem ontoAt_of_core (C : Core l) (h1 : C.OneSubPhiOnto) (h2 : C.FundOnto) : OntoAt l := by
  intro ι hι
  rw [eq_core_of_isCrisDR hι C]
  refine ⟨fun u => ?_, h2⟩
  obtain ⟨x, y, hy, hx, hxy⟩ := pair_onto (Per.φB l).toAddMonoidHom C.ι.toAddMonoidHom
    (Per.FilD l 0 : Set (Per.BdR l)) h1 h2 u 0
  exact ⟨x, (sub_eq_zero.1 hxy : C.ι x = y) ▸ hy, hx⟩

theorem pair_onto_of_tied {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (h : OntoAt l)
    (K : FinExt l) (u : P.R.B) (w : P.R.BdR) :
    ∃ (x : P.R.B) (y : P.R.BdR), y ∈ (P.PD K).Fil 0 ∧ x - (P.PD K).φ x = u ∧ (P.PD K).ι x - y = w := by
  obtain ⟨h1, h2⟩ := h _ T.incl
  have H := pair_onto (P.φB : P.R.B →+* P.R.B).toAddMonoidHom
    (P.ιB : P.R.B →+* P.R.BdR).toAddMonoidHom ((P.PD K).Fil 0 : Set P.R.BdR) (fun u => ?_) (fun w => ?_) u w
  · obtain ⟨x, y, hy, hx, hxy⟩ := H
    exact ⟨x, y, hy, by rw [P.PD_φ]; exact hx, by rw [P.PD_ι]; exact hxy⟩
  · obtain ⟨x, -, hx⟩ := h1 (T.eB u)
    obtain ⟨x, rfl⟩ := T.eB.surjective x
    refine ⟨x, T.eB.injective ?_⟩
    rw [← hx, map_sub, ← T.frob]
    rfl
  · obtain ⟨b, hb, hF⟩ := h2 (T.eD w)
    obtain ⟨b, rfl⟩ := T.eB.surjective b
    refine ⟨b, T.eB.injective ((T.frob b).trans hb), (T.fil K 0 _).2 ?_⟩
    have e : T.eB.symm.toRingHom (T.eB b) = b := T.eB.symm_apply_apply b
    rw [RingHom.comp_apply, e] at hF
    rw [map_sub]
    exact hF

theorem surjective_half_of_onto (h : ∀ (l : ℕ) [Fact l.Prime], OntoAt l) (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.LocalSituation.adm1 D :=
  fun l _ K u w => pair_onto_of_tied (D.locT l) (h l) K u w

end GlobalTheory.FundSeq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsUnitReprOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction
open scoped ENNReal nonZeroDivisors

namespace GlobalTheory.SelBaseChange

section Coord

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [Algebra R R']

end Coord

section Coh

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
  {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R' M'] [Module R M'] [IsScalarTower R R' M']
  (ρ : Representation R G M) (ρ' : Representation R' G M') (u : M' →ₗ[R] M) (hu : Continuous u)
  (he : ∀ g m, u (ρ' g m) = ρ g (u m))

def cZ : Z1 ρ' →ₗ[R] Z1 ρ where
  toFun f := ⟨u ∘ f.1, hu.comp f.2.1, fun g h => by
    simp only [Function.comp_apply, f.2.2 g h, map_add (f := _), he]⟩
  map_add' f f' := Subtype.ext (funext fun g => map_add u _ _)
  map_smul' r f := Subtype.ext (funext fun g => map_smul u _ _)

def cH : H1 ρ' →ₗ[R] H1 ρ :=
  Submodule.mapQ (((B1 ρ').comap (Z1 ρ').subtype).restrictScalars R) _ (cZ ρ ρ' u hu he)
    (fun f hf => by
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ' _).1 hf
      refine (mem_coboundaries1 _ _).2 ⟨u m, fun g => ?_⟩
      have e := hm g
      simp only [Submodule.coe_subtype] at e
      change u (f.1 g) = _
      rw [e, map_sub, he]) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv R ((B1 ρ').comap (Z1 ρ').subtype)).symm.toLinearMap

theorem cH_mk (z : Z1 ρ') :
    cH ρ ρ' u hu he (Submodule.Quotient.mk z) = Submodule.Quotient.mk (cZ ρ ρ' u hu he z) := rfl

theorem res_cH {H : Type} [Group H] [TopologicalSpace H] (φ : H →* G) (hφ : Continuous φ)
    (x : H1 ρ') :
    resH1 ρ φ hφ (cH ρ ρ' u hu he x) =
      cH (ρ.comp φ) (ρ'.comp φ) u hu (fun _ _ => he _ _) (resH1 ρ' φ hφ x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem cH_mem_H1ur (J : Subgroup G) (x : H1 ρ') (hx : x ∈ H1ur ρ' J) :
    cH ρ ρ' u hu he x ∈ H1ur ρ J := by
  unfold H1ur at hx ⊢
  rw [LinearMap.mem_ker] at hx ⊢
  exact (res_cH ρ ρ' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ hx).trans (map_zero _))

theorem cH_mem_Sel {I : Type} {Dc : I → Type} [∀ v, Group (Dc v)] [∀ v, TopologicalSpace (Dc v)]
    (φ : ∀ v, Dc v →* G) (hφ : ∀ v, Continuous (φ v)) (L : LocCond ρ φ) (L' : LocCond ρ' φ)
    (h : ∀ v, ∀ x ∈ L' v, cH (ρ.comp (φ v)) (ρ'.comp (φ v)) u hu (fun _ _ => he _ _) x ∈ L v)
    (x : H1 ρ') (hx : x ∈ Sel ρ' φ hφ L') : cH ρ ρ' u hu he x ∈ Sel ρ φ hφ L := by
  rw [mem_Sel] at hx ⊢
  intro v
  rw [res_cH]
  exact h v _ (hx v)

theorem eq_zero_of_cH {ι : Type} (u : ι → (M' →ₗ[R] M)) (hu : ∀ i, Continuous (u i))
    (he : ∀ i g m, u i (ρ' g m) = ρ g (u i m))
    (hb : Function.Bijective fun (m : M') (i : ι) => u i m) (x : H1 ρ')
    (hx : ∀ i, cH ρ ρ' (u i) (hu i) (he i) x = 0) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [cH_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1] at hx ⊢
  choose m hm using hx
  obtain ⟨m', hm'⟩ := hb.2 m
  refine ⟨m', fun g => hb.1 (funext fun i => ?_)⟩
  have := hm i g
  rw [← congrFun hm' i] at this
  show u i _ = u i _
  rw [map_sub, he]
  exact this

end Coh

section Main

open Formalism.MainNotions.BlochKatoReduction.Gen

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
  (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (k k' : ℕ)

theorem trep_one_apply (g : Gen.GE N) (m : Fin D.R.r → KmodO (X.Ok i k)) (a : Fin D.R.r) :
    Trep i s k 1 g m a = ∑ j, phiK X i k (Tmat i s g a j) • m j := by
  simp [Trep, twRep, matAct, Tmat, Finset.smul_sum, smul_smul]

variable [Algebra (X.Ok i k) (X.Ok i k')] [IsScalarTower (X.O i) (X.Ok i k) (X.Ok i k')]

theorem phiK_eq (a : X.O0 i) :
    phiK X i k' a = algebraMap (X.Ok i k) (X.Ok i k') (phiK X i k a) :=
  IsScalarTower.algebraMap_apply (X.O i) (X.Ok i k) (X.Ok i k') _

variable (p : KmodO (X.Ok i k') →ₗ[X.Ok i k] KmodO (X.Ok i k))

theorem equivariant (g : Gen.GE N) (m : Fin D.R.r → KmodO (X.Ok i k')) :
    p.compLeft (Fin D.R.r) (Trep i s k' 1 g m) = Trep i s k 1 g (p.compLeft (Fin D.R.r) m) := by
  funext a
  show p (Trep i s k' 1 g m a) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [trep_one_apply, trep_one_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [phiK_eq i k k', algebraMap_smul, map_smul]
  rfl

end Main

end GlobalTheory.SelBaseChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FockQWordRowActAdj
section
open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.FockAdj

theorem fockQ_applyWord : Formalism.GradedWeylDivisibility.FockQWordAdj := by
  intro r n w
  induction w with
  | nil => intro F G; rfl
  | cons x w ih =>
    intro F G
    have h1 : applyWord ℚ (x :: w) F = rowDiv ℚ x.1 x.2.1 x.2.2 (applyWord ℚ w F) := rfl
    have h2 : applyWord ℚ (transposeWord (x :: w)) G =
        applyWord ℚ (transposeWord w) (rowDiv ℚ x.2.1 x.1 x.2.2 G) := by
      simp [applyWord, transposeWord, List.foldr_append]
    rw [h1, h2, fockQRowDivAdj, ih]

theorem map_rowAct {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℚ) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    map (Rat.castHom ℂ) (rowAct ℚ g f) =
      rowAct ℂ (g.map (Rat.castHom ℂ)) (map (Rat.castHom ℂ) f) := by
  have : (map (Rat.castHom ℂ)).comp (rowAct ℚ (n := n) g).toRingHom =
      (rowAct ℂ (n := n) (g.map (Rat.castHom ℂ))).toRingHom.comp (map (Rat.castHom ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowAct]
    · intro v
      simp [rowAct]
  exact congrArg (fun φ => φ f) this

theorem fockQ_rowAct : Formalism.GradedWeylDivisibility.FockQRowAct := by
  intro r n g P Q
  have ht : (g.map (Rat.castHom ℂ)).conjTranspose = g.transpose.map (Rat.castHom ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have h : ((fockQ (rowAct ℚ g P) Q : ℚ) : ℂ) = ((fockQ P (rowAct ℚ g.transpose Q) : ℚ) : ℂ) := by
    rw [lfockq_cast, lfockq_cast, map_rowAct, map_rowAct, fockRowAdj, ht]
  exact_mod_cast h

theorem fockQ_word_rowAct_adj : Formalism.GradedWeylDivisibility.FockQWordAdj ∧ Formalism.GradedWeylDivisibility.FockQRowAct :=
  ⟨fockQ_applyWord, fockQ_rowAct⟩

end GlobalTheory.FockAdj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisEmbeddingCount
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction

namespace GlobalTheory.Proof.GaloisEmbeddingCount

theorem card_ringHom_of_isGalois (E F : Type) [Field E] [NumberField E] [IsGalois ℚ E] [Field F]
    (φ : E →+* F) : Nat.card (E →+* F) = Module.finrank ℚ E := by
  haveI : CharZero F := (RingHom.charZero_iff φ.injective).1 inferInstance
  letI : Algebra E F := φ.toAlgebra
  haveI : IsScalarTower ℚ E F := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  rw [Nat.card_congr (RingHom.equivRatAlgHom E F), Nat.card_congr (Normal.algHomEquivAut ℚ F E),
    IsGalois.card_aut_eq_finrank]

end GlobalTheory.Proof.GaloisEmbeddingCount
end

