module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0368
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0473
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinModuleBasisOfFCrystal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0454
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0481
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRTwO
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Classical

noncomputable section

namespace GlobalTheory.TwistPotCrys

section

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem loc_rTwO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    Br.loc D.nbr i w hw (rTwO D.nd i r x) =
      twistM (Br.loc D.nbr i w hw (rO D.nd i r x)) (Br.locChi D.nbr i w hw (D.nd.chi i 1))⁻¹ := by
  refine MonoidHom.ext fun g => Matrix.ext fun a b => ?_
  show (D.nbr i w hw).toLL ((((chiU D.nd i 1)⁻¹ (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i) *
      rO D.nd i r x (decS D.nd w (Br.iota D.nbr i w hw g)) a b) = _
  rw [map_mul]
  rfl

theorem matRep_loc_rO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    matRep (Br.loc D.nbr i w hw (rO D.nd i r x)) = (D.nbr i w hw).rep ((r x).comp (decS D.nd w)) := rfl

theorem isTwistRep_loc (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) :
    IsTwistRep (Br.locChi D.nbr i w hw (D.nd.chi i 1))⁻¹ (matRep (Br.loc D.nbr i w hw (rO D.nd i r x)))
      (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) := by
  refine ⟨LinearEquiv.refl _ _, fun g v => ?_⟩
  rw [loc_rTwO]
  change ((((Br.locChi D.nbr i w hw (D.nd.chi i 1))⁻¹ g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) •
      Br.loc D.nbr i w hw (rO D.nd i r x) g).mulVec v = _
  exact Matrix.smul_mulVec _ _ _

theorem continuous_rTwO (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i)
    (hc : Continuous (fun g => ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)))) :
    Continuous fun g => rTwO D.nd i r x g := by
  have h1 : Continuous fun g : GE D.nd => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) :=
    (D.nd.chi_cont i 1).comp continuous_inv
  refine (h1.smul hc).congr fun g => ?_
  simp [rTwO, twistM, rO]

end


set_option maxHeartbeats 1600000 in
theorem twist_potCrys : ∀ (D : D7), PcrisTensorL D.loc → ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x : D.nd.X i) (K' : FinExt (D.nd.l i))
    (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c')
    (Sig0 : Finset ((pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ))
    (c : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ),
    Continuous (fun g => ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i))) →
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) →
    (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep ((r x).comp (decS D.nd w))) Sig0 →
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys (WeaklyAdmissibleFiltrations.charRep (Br.locChi D.nbr i w hw (D.nd.chi i 1))) →
    (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough (WeaklyAdmissibleFiltrations.charRep (Br.locChi D.nbr i w hw (D.nd.chi i 1))) {c} →
    (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x))) ∧
      (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough (matRep (Br.loc D.nbr i w hw (rTwO D.nd i r x)))
        (Sig0.image (fun a => a * c⁻¹)) := by
  intro D hT i w hw r x K' h hN hF hS Sig0 c hcont hpot hit hχpot hχit
  have hcO : Continuous fun g => rO D.nd i r x g := hcont
  have hcT := continuous_rTwO D i r x hcont
  rw [← matRep_loc_rO] at hpot hit
  exact (hT (D.nd.l i) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS
      (GlobalTheory.PotDual.bundle _ _ (Br.loc D.nbr i w hw (rO D.nd i r x)) (GlobalTheory.PotDual.continuous_loc D i w hw _ hcO))
      (GlobalTheory.PotDual.bundle _ _ (Br.loc D.nbr i w hw (rTwO D.nd i r x)) (GlobalTheory.PotDual.continuous_loc D i w hw _ hcT))
      Sig0 (Sig0.image (fun a => a * c⁻¹)) hpot hit).1 _ c (isTwistRep_loc D i w hw r x) hχpot hχit
      (fun b => by
        rw [Finset.mem_image]
        exact ⟨fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩, fun ⟨a, ha, e⟩ => ⟨a, ha, e.symm⟩⟩)

end GlobalTheory.TwistPotCrys

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoverExists
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.TraceConjugationCover

theorem cover_exists : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (L₀ : FinExt l) (r : Γ →* GL (Fin a) (Om l)), Continuous r → Formalism.MainNotions.N.IsSSRep r → ∀ Cl : Set (Γ →* GL (Fin a) (Om l)), (∀ ρ ∈ Cl, Continuous ρ) → LinApprox r Cl → Nonempty (Cover L₀ r Cl) := by
  intro l _ Γ _ _ _ _ a L₀ r hr hss Cl hCl hap
  classical
  obtain ⟨d, ρ, b, e, hρ, hreads, hind, hbr⟩ := _root_.GlobalTheory.BKLim.exists_zl_span_lattice_reads l Γ a r hr
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.smallTrace_dvd_span l Γ a r hr hss
  obtain ⟨K, hK⟩ := traceL l a d b
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith

  have hch : ∀ ρ' : Γ →* GL (Fin a) (Om l), ∃ (L : FinExt l) (t : Finset (Matrix (Fin a) (Fin a) (Om l))), Continuous ρ' →
      (L₀.1 ≤ L.1 ∧ (∀ g i j, ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L.1) ∧ (∀ x ∈ t, ∀ i j, x i j ∈ L.1) ∧
        (∀ x : Matrix (Fin a) (Fin a) (Om l), (∀ i j, x i j ∈ L.1) → x ∈ Submodule.span ℚ_[l] (t : Set (Matrix (Fin a) (Fin a) (Om l)))) ∧
        (∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ∑ y ∈ t, zOm l (c' y) • y = 1) ∧
        ∀ g, ∀ x ∈ t, ∃ c' : Matrix (Fin a) (Fin a) (Om l) → ℤ_[l], ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) * x = ∑ y ∈ t, zOm l (c' y) • y) := by
    intro ρ'
    by_cases h : Continuous ρ'
    · obtain ⟨L, hLf, hL⟩ := _root_.GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem_of_continuous l Γ a ρ' h
      haveI := hLf
      haveI := L₀.2
      let L' : FinExt l := ⟨L ⊔ L₀.1, inferInstance⟩
      have hL' : ∀ g i j, ((ρ' g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j ∈ L'.1 := fun g i j =>
        (le_sup_left : L ≤ L ⊔ L₀.1) (hL g i j)
      obtain ⟨t, h1, h2, h3, h4⟩ := _root_.GlobalTheory.exists_stable_spanning_finset l Γ a ρ' L' h hL'
      exact ⟨L', t, fun _ => ⟨le_sup_right, hL', h1, h2, h3, h4⟩⟩
    · exact ⟨L₀, ∅, fun h' => absurd h' h⟩
  choose Lf tf htf using hch

  have hap' : ∀ n : ℕ, ∃ (s : Finset (Γ →* GL (Fin a) (Om l))) (cc : (Γ →* GL (Fin a) (Om l)) → Om l),
      (s : Set (Γ →* GL (Fin a) (Om l))) ⊆ Cl ∧ ∀ g, ‖trc r g - ∑ ρ' ∈ s, cc ρ' * trc ρ' g‖ ≤ ((l : ℝ)⁻¹) ^ (n + K + c) :=
    fun n => hap _ (by positivity)
  choose s cc hsCl hscc using hap'
  let U : ℕ → Finset (Γ →* GL (Fin a) (Om l)) := fun n => (Finset.range (n + 1)).biUnion s
  have hUmono : ∀ n, U n ⊆ U (n + 1) := fun n =>
    Finset.biUnion_subset_biUnion_of_subset_left _ (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
  have hsU : ∀ n, s n ⊆ U n := fun n => Finset.subset_biUnion_of_mem s (Finset.mem_range.2 (Nat.lt_succ_self n))
  have hUCl : ∀ n, ∀ ρ' ∈ U n, ρ' ∈ Cl := by
    intro n ρ' h
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 h
    exact hsCl j hj
  let m : ℕ → ℕ := fun n => (U n).card
  let ρs : ∀ n, Fin (m n) → (Γ →* GL (Fin a) (Om l)) := fun n k => ((U n).equivFin.symm k).1
  have hρsU : ∀ n k, ρs n k ∈ U n := fun n k => ((U n).equivFin.symm k).2
  have hρsC : ∀ n k, Continuous (ρs n k) := fun n k => hCl _ (hUCl n _ (hρsU n k))
  let cs : ∀ n, Fin (m n) → Om l := fun n k => if ρs n k ∈ s n then cc n (ρs n k) else 0
  have hcs : ∀ n g, ∑ k, cs n k * trc (ρs n k) g = ∑ ρ' ∈ s n, cc n ρ' * trc ρ' g := by
    intro n g
    have e1 : ∑ k, cs n k * trc (ρs n k) g = ∑ x : (U n), (if x.1 ∈ s n then cc n x.1 else 0) * trc x.1 g :=
      Fintype.sum_equiv (U n).equivFin.symm _ _ (fun k => rfl)
    rw [e1, Finset.sum_coe_sort (U n) (fun x => (if x ∈ s n then cc n x else 0) * trc x g)]
    simp only [ite_mul, zero_mul]
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (hsU n)]
  have hK' : ∀ n, ∀ w : Fin d → ℤ_[l], ‖((l : Om l) ^ (n + K) • ∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    intro n w
    rw [Matrix.trace_smul, smul_eq_mul, norm_mul, norm_pow, norm_l]
    calc ((l : ℝ)⁻¹) ^ (n + K) * ‖(∑ i, zOm l (w i) • b i).trace‖ ≤ ((l : ℝ)⁻¹) ^ (n + K) * (l : ℝ) ^ K :=
          mul_le_mul_of_nonneg_left (hK w) (by positivity)
      _ = ((l : ℝ) ^ n)⁻¹ := by
          rw [pow_add, inv_pow, inv_pow, mul_assoc, inv_mul_cancel₀ (by positivity), mul_one]
  have hlay : ∀ n, ∃ M₀ : ℕ, ∀ M, M₀ ≤ M → ∃ (d' : ℕ) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (bb : Fin d' → Fin (m n) → Matrix (Fin a) (Fin a) (Om l)) (e' : Fin d' → ℤ_[l]) (P : Matrix (Fin d) (Fin d') ℤ_[l]), Continuous ρ' ∧ (∀ s k i j, bb s k i j ∈ (Lf (ρs n k)).1) ∧ LinearIndependent ℚ_[l] bb ∧ (∀ x : Fin (m n) → Matrix (Fin a) (Fin a) (Om l), (∀ k i j, x k i j ∈ (Lf (ρs n k)).1) → x ∈ Submodule.span ℚ_[l] (Set.range bb)) ∧ (∀ k, Reads ρ' (ρs n k) (fun s => bb s k) e') ∧ (∀ s, bb s ∈ latT (ρs n) (fun k => tf (ρs n k)) M) ∧ (∀ x ∈ latT (ρs n) (fun k => tf (ρs n k)) M, ∃ z : Fin d' → ℤ_[l], x = ∑ s, zOm l (z s) • bb s) ∧ Carries r b (ρs n) (fun k => tf (ρs n k)) M bb P (n + K) ∧ Onto (fun g => ((ρ g : GL (Fin d) ℤ_[l]) : Matrix (Fin d) (Fin d) ℤ_[l])) (fun g => ((ρ' g : GL (Fin d') ℤ_[l]) : Matrix (Fin d') (Fin d') ℤ_[l])) P n ∧ (∀ i, (l : ℤ_[l]) ^ n ∣ (P *ᵥ e' - e) i) ∧ ∀ s, ‖(∑ i, zOm l (P i s) • b i).trace - ∑ k, cs n k * (bb s k).trace‖ ≤ ((l : ℝ) ^ n)⁻¹ := by
    intro n
    exact GlobalTheory.T.exists_lattice_layer_cover_basis_mod_pow l Γ a r d ρ b e hreads hind hbr c hc n (n + K) (by omega) (hK' n) (m n) (ρs n)
      (fun k => Lf (ρs n k)) (fun k => tf (ρs n k)) (hρsC n) (fun k => (htf _ (hρsC n k)).2.1)
      (fun k => (htf _ (hρsC n k)).2.2.1) (fun k => (htf _ (hρsC n k)).2.2.2.1)
      (fun k => (htf _ (hρsC n k)).2.2.2.2.1) (fun k => (htf _ (hρsC n k)).2.2.2.2.2) (cs n)
      (fun g => by rw [hcs n g]; exact hscc n g)
  choose M₀ hM₀ using hlay
  let M : ℕ → ℕ := fun n => ∑ j ∈ Finset.range (n + 1), M₀ j
  have hMle : ∀ n, M₀ n ≤ M n := fun n =>
    Finset.single_le_sum (f := M₀) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_self n))
  have hMmono : ∀ n, M n ≤ M (n + 1) := fun n => by
    simp only [M]
    rw [Finset.sum_range_succ _ (n + 1)]
    exact Nat.le_add_right _ _
  have hL := fun n => hM₀ n (M n) (hMle n)
  choose d' ρ' bb e' P hcont hbbL hind' hspan' hreads' hmem hcoord hcar honto hunit htr using hL
  let ι : ∀ n, Fin (m n) → Fin (m (n + 1)) := fun n k =>
    (U (n + 1)).equivFin ⟨((U n).equivFin.symm k).1, hUmono n ((U n).equivFin.symm k).2⟩
  have hι : ∀ n k, ρs (n + 1) (ι n k) = ρs n k := by
    intro n k
    simp [ρs, ι]
  have htrans : ∀ n, ∃ f : Matrix (Fin (d' n)) (Fin (d' (n + 1))) ℤ_[l], (∀ g, f * ((ρ' (n + 1) g : GL (Fin (d' (n + 1))) ℤ_[l]) : Matrix (Fin (d' (n + 1))) (Fin (d' (n + 1))) ℤ_[l]) = ((ρ' n g : GL (Fin (d' n)) ℤ_[l]) : Matrix (Fin (d' n)) (Fin (d' n)) ℤ_[l]) * f) ∧ ∀ i j, (l : ℤ_[l]) ^ n ∣ (P n * f - P (n + 1)) i j := by
    intro n
    exact GlobalTheory.T.exists_equivariant_transition_matrix_cover l Γ a r d b hind (m n) (m (n + 1)) (ρs n) (ρs (n + 1)) (ι n) (hι n)
      (fun k => tf (ρs n k)) (fun k => tf (ρs (n + 1) k)) (fun k => by rw [hι n k]) (M n) (M (n + 1)) (hMmono n)
      (d' n) (d' (n + 1)) (ρ' n) (ρ' (n + 1)) (bb n) (bb (n + 1)) (e' n) (e' (n + 1)) (hind' n) (hreads' n)
      (hreads' (n + 1)) (hmem (n + 1)) (hcoord n) (P n) (P (n + 1)) n (n + K) (n + 1 + K) (by omega) (by omega)
      (hcar n) (hcar (n + 1))
  choose f hfe hfP using htrans
  let tw : Tower ρ :=
    { d' := d', ρ' := ρ', Pi := P, onto := honto, f := f, f_equi := hfe, f_Pi := hfP }
  let lay : ∀ n, Layer L₀ Cl (tw.ρ' n) := fun n =>
    { m := m n, rep := ρs n, mem := fun k => hUCl n _ (hρsU n k), L := fun k => Lf (ρs n k),
      le := fun k => (htf _ (hρsC n k)).1, rep_mem := fun k => (htf _ (hρsC n k)).2.1, b := bb n,
      b_mem := hbbL n, indep := hind' n, span := hspan' n, e := e' n, reads := hreads' n, c := cs n }
  exact ⟨{ d := d, ρ := ρ, cont := hρ, b := b, e := e, reads := hreads, tw := tw, cont' := hcont, lay := lay,
            unit := hunit, trace := htr }⟩

end GlobalTheory.TraceConjugationCover

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalBasisTransportFreeOverPrismStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystal_basis_transport_free_over_prism : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → (∀ i, (oE 1).u (ϖ.prism a) (b i) = b i) ∧ ∀ (P' : Obj l ↥(OL (ϖ.field a))) (f : GlobalTheory.Prism.Hom (ϖ.prism a) P') (Q Q' : Type) [Fintype Q] [Fintype Q'] (c : ι → Q → O) (y : ι → Q → P'.A) (c' : ι → Q' → O) (y' : ι → Q' → P'.A), ∑ i, ∑ q, y i q • (oE (c i q)).u P' (E.tr f (b i)) = ∑ i, ∑ q, y' i q • (oE (c' i q)).u P' (E.tr f (b i)) → ∀ (R : Type) [CommRing R] [Algebra O R] (ψ : P'.A →+* R), (∀ z : ℤ_[l], ψ (f.f (algebraMap ℤ_[l] (Wq l a)⟦X⟧ z)) = algebraMap O R (algebraMap ℤ_[l] O z)) → ∀ i, ∑ q, c i q • ψ (y i q) = ∑ q, c' i q • ψ (y' i q) := by
  first | exact @GlobalTheory.CrysIndep.main | exact GlobalTheory.CrysIndep.main | (intros; apply GlobalTheory.CrysIndep.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalChangeOfBasisFrobeniusCompat
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysEpsFrob


set_option maxHeartbeats 1000000 in
theorem eps_frob_compat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : Lat a O K ϖ) (I : Ident t ϖ P T), letI := zlLat T; ∀ (E : FCrys l ↥(OL (ϖ.field a))) (jA : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)), Realises (ϖ.field a) E (ainfObj _) (ainfId _) ↥T.L.T (actZ T) jA → (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (jA (E.tr (ϖ.toAinf a) x))) ↔ ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) → ∀ (oE : O → FHom E E), (∀ (c : O) (x : E.M (ainfObj (ϖ.field a))), jA ((oE c).u (ainfObj (ϖ.field a)) x) = (OfCrystal.mulZ T c).lTensor (WCb l) (jA x)) → ∀ (b : ι → E.M (ϖ.prism a)), (∀ j, ∃ hm : (bas j : Vec K a ι) ∈ P.M, kappa T (jA (E.tr (ϖ.toAinf a) (b j))) = I.j (toW t ϖ P ⟨bas j, mem_ME_of_mem_M hm⟩)) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → (∀ f : K⟦X⟧, φ₂ (PowerSeries.C f) = PowerSeries.C (frob K l f)) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (κ : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), PP.I = Ideal.span {(l : PP.A)} → (∀ τ (x : (Wq l a)⟦X⟧), κ τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ κ τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → (∀ τ y, κ τ (PP.D.φ y) = φ₂ (κ (τ - 1) y)) → ∀ (Q : Type) [Fintype Q] (c : ι → ι → Q → O) (y : ι → ι → Q → PP.A), (∀ j, E.tr p₁ (b j) = ∑ i, ∑ q, y i j q • (oE (c i j q)).u PP (E.tr p₀ (b i))) → ∀ τ, (Matrix.of fun i j => ∑ q, c i j q • κ τ (y i j q)) * ((P.mx (τ - 1)).map (frob K l)).map sh = ((P.mx (τ - 1)).map (frob K l)).map PowerSeries.C * (Matrix.of fun i j => ∑ q, c i j q • κ (τ - 1) (y i j q)).map φ₂ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I
  intro EE jA hR him oE hoE b hb sh φ₂ hsh hφC PP p₀ p₁ κ hI hκ hκφ Q _ c y hy τ
  letI := zlLat T
  haveI hK : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective

  obtain ⟨J, hJ⟩ : ∃ J : EE.M (ϖ.prism a) →+ TW (OW l O) T,
      ∀ x, J x = kappa T (jA (EE.tr (ϖ.toAinf a) x)) :=
    ⟨(kappa T).comp (jA.toAddMonoidHom.comp (EE.tr (ϖ.toAinf a)).toAddMonoidHom), fun _ => rfl⟩
  have h1 : ∀ z : TW (OW l O) T, (∃ x, z = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), z = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := fun z => by
    simp only [hJ]
    exact him z
  obtain ⟨cc, hcM, hcJ, hsurj⟩ := GlobalTheory.BKCoord.exists_coord I J h1
  have hJi : Function.Injective J := by
    have := EE.proj (ainfObj (ϖ.field a))
    have := EE.proj (ϖ.prism a)
    intro u v huv
    rw [hJ, hJ] at huv
    exact GlobalTheory.BKCoord.semiBC_injective (EE.tr_bc (ϖ.toAinf a)) (GlobalTheory.BKCoord.ev_injective ϖ)
      (GlobalTheory.BKCoord.semiBC_injective hR.bc inclW_injective ((kappa_bijective T).1 huv))
  have hinj : Function.Injective cc := fun x x' h => hJi (by rw [hcJ, hcJ]; simp only [h])
  have hw : ∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)),
      cc (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * cc x τ i := by
    intro w x
    refine GlobalTheory.BKCoord.eq_of_j_eq_toAc I w ⟨_, mem_ME_of_mem_M (hcM x)⟩ ⟨_, mem_ME_of_mem_M (hcM _)⟩ ?_
    have h3 := congrArg jA ((EE.tr (ϖ.toAinf a)).map_smulₛₗ w x)
    have h4 := congrArg (kappa T) (h3.trans (jA.map_smulₛₗ _ _))
    have h5 := h4.trans (GlobalTheory.BKCoord.kappa_smul T _ _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h5
  have hU : ∀ (o : O) x, cc ((oE o).u (ϖ.prism a) x) =
      fun τ i => PowerSeries.C (algebraMap O K o) * cc x τ i := by
    intro o x
    refine GlobalTheory.BKCoord.eq_of_j_eq_const I o ⟨_, mem_ME_of_mem_M (hcM x)⟩ ⟨_, mem_ME_of_mem_M (hcM _)⟩ ?_
    have h3 := (congrArg jA ((oE o).u_tr (ϖ.toAinf a) x)).symm.trans (hoE o _)
    have h4 := (congrArg (kappa T) h3).trans (GlobalTheory.BKCoord.kappa_mulZ T o _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h4
  have hΦ : ∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e)
      (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k →
      cc m = fun τ i => E K l e ^ k * P.phi (cc x) τ i := by
    intro x m k h
    refine GlobalTheory.BKCoord.eq_of_j_eq_phi I k (hcM x) ⟨_, mem_ME_of_mem_M (hcM _)⟩ ?_
    have h3 := (congrArg (kappa T) (GlobalTheory.BKCoord.j_frob hR x m k h)).trans (GlobalTheory.BKCoord.kappa_smul T _ _)
    have h4 := GlobalTheory.BKCoord.kappa_frob T (jA (EE.tr (ϖ.toAinf a) x))
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h3.trans (congrArg _ h4)
  have hcb : ∀ j, cc (b j) = bas j := by
    intro j
    obtain ⟨hm, hbj⟩ := hb j
    have h2 := (hcJ (b j)).symm.trans ((hJ (b j)).trans hbj)
    exact congrArg Subtype.val (toW_injective t ϖ P (I.j.injective h2))

  obtain ⟨lam₀, hl₀, ht₀⟩ := GlobalTheory.CrysExt.exists_coord l a e O K t ϖ ι EE cc hw PP p₀ κ PowerSeries.C
    (fun τ w => (hκ τ w).1)
  obtain ⟨lam₁, hl₁, ht₁⟩ := GlobalTheory.CrysExt.exists_coord l a e O K t ϖ ι EE cc hw PP p₁ κ sh
    (fun τ w => (hκ τ w).2)
  obtain ⟨ε', hε'⟩ := GlobalTheory.BKGal.CrysEps.exists_eps l a e O K t ϖ ι P EE cc hinj hcM hsurj hw
    (fun o => ⟨oE o, hU o⟩) sh hsh PP p₀ p₁ κ hκ lam₀ lam₁ hl₀ hl₁ ht₀ ht₁
  have hsh1 : ∀ f, PowerSeries.constantCoeff (sh f) = f := fun f => by simpa using hsh f 0
  have hshinj : Function.Injective sh := fun f g h => by rw [← hsh1 f, ← hsh1 g, h]
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl1 : (l : K⟦X⟧) ≠ 0 := fun h => hl0 (by simpa using congrArg PowerSeries.constantCoeff h)
  have hl2 : (l : K⟦X⟧⟦X⟧) ≠ 0 := fun h => hl1 (by simpa using congrArg PowerSeries.constantCoeff h)
  have hE : E K l e ≠ 0 := fun h => hl0 (by
    simpa [E, NeZero.ne e] using congrArg PowerSeries.constantCoeff h)
  have hshE : sh (frob K l (E K l e)) ≠ 0 := by
    rw [map_ne_zero_iff _ hshinj, map_ne_zero_iff _ (frob_injective l)]; exact hE
  have hl : (l : PP.A) ∈ PP.I := hI ▸ Ideal.mem_span_singleton_self _
  have hfb : ∀ (j : ι) (σ : ZMod a) (i : ι), frob K l (bas j σ i) = bas j σ i := by
    intro j σ i
    rcases eq_or_ne i j with rfl | h
    · simp [bas]
    · simp [bas, Pi.single_eq_of_ne h]

  have hl1b : ∀ j σ, lam₁ (EE.tr p₁ (b j)) σ = Pi.single j 1 := by
    intro j σ; funext i
    rw [ht₁, hcb, hfb]
    rcases eq_or_ne i j with rfl | h
    · simp [bas]
    · simp [bas, Pi.single_eq_of_ne h]

  have hε'col : ∀ σ i j, ε' σ i j = lam₀ (EE.tr p₁ (b j)) σ i := by
    intro σ i j
    rw [hε' _ σ, hl1b, Matrix.mulVec_single_one]; rfl

  have hEps : ∀ σ i j, lam₀ (EE.tr p₁ (b j)) σ i = ∑ q, c i j q • κ σ (y i j q) := by
    intro σ i j
    have hU0 : ∀ (o : O) (i' : ι), lam₀ ((oE o).u PP (EE.tr p₀ (b i'))) σ i =
        if i = i' then PowerSeries.C (PowerSeries.C (algebraMap O K o)) else 0 := by
      intro o i'
      rw [(oE o).u_tr, ht₀, hU, hcb]
      rcases eq_or_ne i i' with rfl | h
      · simp [bas]
      · simp [bas, Pi.single_eq_of_ne h, h]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy j, map_sum, Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single i]
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_sum, Finset.sum_apply, Finset.sum_apply]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hl₀, hU0, if_pos rfl, Algebra.smul_def, PowerSeries.algebraMap_apply,
          PowerSeries.algebraMap_apply, mul_comm]
    · intro i' _ h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [hl₀, hU0, if_neg (Ne.symm h), mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h
  refine Matrix.ext fun i j => ?_
  obtain ⟨n, k, hn⟩ := exists_isFrac (l : PP.A) (EE.Φ PP ⟨l, hl⟩ (EE.tr p₁ (b j)))

  have hA := GlobalTheory.CrysFrobCoord.frob_in_coordinates l a e O K t ϖ ι P EE cc hw hΦ PP hl p₀ κ
    PowerSeries.C φ₂ (fun τ w => (hκ τ w).1) hκφ hφC PowerSeries.C_injective lam₀ hl₀ ht₀ _ n k hn τ i

  obtain ⟨m', k', hm'⟩ := exists_isFrac (A := (ϖ.prism a).A) (eis l a e)
    (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ (b j))
  obtain ⟨r, hr⟩ := EE.Φ_nat p₁ ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ ⟨l, hl⟩ (b j) m' k' n k hm' hn
  have hκE : κ τ (p₁.f (eis l a e)) = sh (frob K l (E K l e)) := by
    rw [(hκ τ _).2, ← GlobalTheory.CrysFrobCoord.frob_toAc, GlobalTheory.CrysFrobCoord.coe_toAc_eis]
  have hJl : κ τ (l : PP.A) = l := map_natCast _ _
  have hB : ∀ i', lam₁ n τ i' = (l : K⟦X⟧⟦X⟧) ^ k * sh (frob K l (P.mx (τ - 1) i' j)) := by
    intro i'
    have h1 := congrArg (fun z => lam₁ z τ i') hr
    simp only [hl₁, map_sub, Pi.sub_apply, map_zero, Pi.zero_apply, map_pow, map_mul, hJl, hκE] at h1
    have h2 := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ (mul_ne_zero hshE hl2)))
    have hm'c : cc m' (τ - 1) i' = E K l e ^ k' * P.mx (τ - 1) i' j := by
      rw [hΦ _ _ _ hm', hcb]
      simp only [PhiMod.phi_apply]
      congr 1
      have : frobV l (bas j (τ - 1 - 1) : ι → K⟦X⟧) = Pi.single j 1 := funext fun i'' => by
        rw [frobV_apply, hfb]; rfl
      rw [this, Matrix.mulVec_single_one]; rfl
    rw [ht₁, hm'c, map_mul, map_mul, map_pow, map_pow] at h2
    refine mul_left_cancel₀ (pow_ne_zero k' hshE) ?_
    rw [← h2]; ring
  have hlk : ((l : K⟦X⟧⟦X⟧) ^ k) ≠ 0 := pow_ne_zero k hl2
  refine mul_left_cancel₀ hlk ?_
  have hC := congrFun (hε' n τ) i
  rw [hA] at hC
  simp only [Matrix.mulVec, dotProduct, hB, hε'col, hEps, Matrix.map_apply, Matrix.of_apply] at hC
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply]
  rw [hC, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.CrysEpsFrob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeHodgeTateJumpsFiniteStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_hodgeTateJumps_finite : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (Jumps (PD := (D.loc l).PD K) T).Finite := by
  first | exact @GlobalTheory.NL.JumpsFinite.jumps_finite | exact GlobalTheory.NL.JumpsFinite.jumps_finite | (intros; apply GlobalTheory.NL.JumpsFinite.jumps_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePhiModuleMapExistsStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_phi_module_map_exists : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c → (∀ x, c x ∈ P.M) → (∀ m ∈ P.M, ∃ x, c x = m) → (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative (R := K))^[i] f) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∃ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, ∀ y τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ := by
  first | exact @GlobalTheory.BKGal.CrysEps.exists_eps | exact GlobalTheory.BKGal.CrysEps.exists_eps | (intros; apply GlobalTheory.BKGal.CrysEps.exists_eps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupDivisibleImageCoboundaryIffFiniteLevelStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_divisible_image_coboundary_iff_finite_level : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (d : ↥(latticeCocycles LA)) (c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), CobO (P.PD K) L1 (cupLD LA' m (d : ↥(GK K) → A.V) (fun g => GlobalTheory.BKFinLevel.ioL LA' ϖ r (c' g))) ↔ CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r (redT LA _ d) c') := by
  first | exact @GlobalTheory.BKFinLevel.cobO_cupLD_ioL_iff | exact GlobalTheory.BKFinLevel.cobO_cupLD_ioL_iff | (intros; apply GlobalTheory.BKFinLevel.cobO_cupLD_ioL_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisExactStrictElementwiseCrystalline
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem dcris_exact_strict_elementwise : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D := by
  intro D l _ K LL
  have hA := (_root_.GlobalTheory.Per.DcrisExact.fontaine_dcris D l K LL).1
  intro hbij V₀ V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ₀ ρ₁ ρ₂ ι π _ _ _ _ _ _ _ _ _ hιe hπe hinj hsurj
    hker c₀ c₁ c₂
  obtain ⟨h1, h2, h3, h4⟩ :=
    hA hbij V₀ ρ₀ V₁ ρ₁ V₂ ρ₂ ι π hιe hπe hinj hsurj hker.symm c₀ c₁ c₂
  refine ⟨h1, ?_, h3, fun a => (h4 a).1, ?_⟩
  · intro x hx hπx
    exact Submodule.mem_map.mp (h2.ge ⟨hx, hπx⟩)
  · intro a y hy hyF
    exact (h4 a).2.ge ⟨hy, hyF⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOrthogonalIdempotentsHeckeSpanRepStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_idempotents_heckeSpan_rep : ∀ (l : ℕ) [Fact l.Prime] {Γ X A : Type} [Group Γ] [Finite X] [CommRing A] [IsDomain A] [Algebra ℤ_[l] A] [Module.Finite ℤ_[l] A] {n r t : ℕ} (T : Subalgebra A (X → A)) (rep : X → (Γ →* GL (Fin n) A)) (ρ : Γ →* GL (Fin r) A) (χ : ℕ → (Γ →* Aˣ)) (π : X) (e : (Fin n → FractionRing A) ≃ₗ[FractionRing A] ((Fin r → FractionRing A) × (Fin t → FractionRing A))), 2 ≤ r → Submodule.span A (Set.range (mat ρ)) = ⊤ → IsDecomp (t := t) (rep π) ρ χ e → ∃ eB e1 : X → Matrix (Fin n) (Fin n) A, (InRing T rep eB ∧ InRing T rep e1 ∧ eB * eB = eB ∧ e1 * e1 = e1 ∧ eB * e1 = 0 ∧ e1 * eB = 0) ∧ (∀ u, e (((eB π).map (toFr A)).mulVec u) = (0, (e u).2)) ∧ ∃ ε : Matrix (Fin r) (Fin r) (FractionRing A), ε.rank = 1 ∧ ∀ u, e (((e1 π).map (toFr A)).mulVec u) = (ε.mulVec (e u).1, 0) := by
  first | exact @GlobalTheory.SpanIdem.exists_orthogonal_idempotents | exact GlobalTheory.SpanIdem.exists_orthogonal_idempotents | (intros; apply GlobalTheory.SpanIdem.exists_orthogonal_idempotents <;> assumption)
end

