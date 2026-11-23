module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0282
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0560
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLubinTateCharacterUnramifiedPeriod
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

theorem GlobalTheory.LTChar.main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (s : ℕ), 0 < s → ∃ (K' : FinExt l) (_ : K.1 ≤ K'.1) (x : P.R.Bˣ) (χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ), (∀ c : ↥(MaximalUnramifiedExtension l), fr l s c = c → (c : Om l) ∈ K'.1) ∧ (∀ g, fr l s (χ g : ↥(MaximalUnramifiedExtension l)) = χ g) ∧ (Continuous fun g => (((χ g : (↥(MaximalUnramifiedExtension l))ˣ) : ↥(MaximalUnramifiedExtension l)) : Om l)) ∧ (∀ g : ↥(GK K'), P.actQ (g : GQ l) (x : P.R.B) = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (χ g : ↥(MaximalUnramifiedExtension l)) * x) ∧ P.ιB x ∈ Fil P 1 ∧ P.ιB x ∉ Fil P 2 ∧ ∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1 := by
  intro l _ P AI T K s hs
  obtain ⟨E, ω, -, -, hE, -⟩ := _root_.GlobalTheory.PMon.UnrDeg.fixed_field_deg l s hs
  obtain ⟨x, hu, hφ, h1, h2, hj⟩ := GlobalTheory.LTPeriod.main l P AI T K s hs
  have h1' : P.ιB x ∈ Fil P 1 := (mem_Fil_iff P K).2 h1
  have h2' : P.ιB x ∉ Fil P 2 := fun h => h2 ((mem_Fil_iff P K).1 h)
  have hj' : ∀ j, 0 < j → j < s → ev P j x ∈ Fil P 0 ∧ ev P j x ∉ Fil P 1 := fun j h0 hjs =>
    ⟨(mem_Fil_iff P K).2 (hj j h0 hjs).1, fun h => (hj j h0 hjs).2 ((mem_Fil_iff P K).1 h)⟩
  let K' : FinExt l := supExt K E
  have hKK' : K.1 ≤ K'.1 := le_sup_left
  have hEK' : E.1 ≤ K'.1 := le_sup_right
  choose a ha hax using fun g : GQ l => _root_.GlobalTheory.PMon.lt_period_conj_ratio l P AI T s hs x hu hφ h1' h2' hj' g
  have hx0 : x ≠ 0 := by
    intro h0
    apply h2'
    rw [h0, map_zero]
    exact Fil_zero_mem 2
  haveI : Nontrivial P.R.B := ⟨⟨x, 0, hx0⟩⟩
  have hcancel : ∀ c c' : ↥(MaximalUnramifiedExtension l), algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c * x = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c' * x → c = c' :=
    fun c c' h => (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B).injective (hu.mul_right_cancel h)
  have hfix : ∀ (g : ↥(GK K')) (h : GQ l), P.actQ (g : GQ l) (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a h)) =
      algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a h) := fun g h => act_kur P g (hEK' ((hE (a h)).1 (ha h)))
  have hmul : ∀ g h : ↥(GK K'), a ((g : GQ l) * (h : GQ l)) = a g * a h := by
    intro g h
    apply hcancel
    calc algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a ((g : GQ l) * (h : GQ l))) * x = P.actQ ((g : GQ l) * (h : GQ l)) x := (hax _).symm
      _ = P.actQ (g : GQ l) (P.actQ (h : GQ l) x) := by rw [map_mul, AlgEquiv.mul_apply]
      _ = P.actQ (g : GQ l) (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a h) * x) := by rw [hax]
      _ = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a h) * (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a g) * x) := by rw [map_mul, hfix, hax]
      _ = algebraMap ↥(MaximalUnramifiedExtension l) P.R.B (a g * a h) * x := by rw [map_mul]; ring
  have hone : a 1 = 1 := by
    apply hcancel
    rw [← hax, map_one, AlgEquiv.one_apply, map_one, one_mul]
  have hne : ∀ g, a g ≠ 0 := by
    intro g h0
    have h := hax g
    rw [h0, map_zero, zero_mul] at h
    exact hx0 ((P.actQ g).injective (h.trans (map_zero _).symm))
  let χ : ↥(GK K') →* (↥(MaximalUnramifiedExtension l))ˣ :=
    { toFun := fun g => Units.mk0 (a g) (hne g)
      map_one' := Units.ext hone
      map_mul' := fun g h => Units.ext (hmul g h) }
  refine ⟨K', hKK', hu.unit, χ, fun c hc => hEK' ((hE c).1 hc), fun g => ha _, ?_, fun g => ?_, ?_, ?_,
    fun j h0 hjs => ?_⟩
  · exact _root_.GlobalTheory.LTChar.char_cont l P AI T K' x h1' h2' (fun g => a g) (fun g => hax g)
  · rw [IsUnit.unit_spec]
    exact hax g
  · rw [IsUnit.unit_spec]
    exact h1'
  · rw [IsUnit.unit_spec]
    exact h2'
  · rw [IsUnit.unit_spec]
    exact hj' j h0 hjs

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNumericalGaloisDataLocalSituation
section
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.TopWindow

theorem exists_topData_galData : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) (K LL : FinExt l)
    (hA : CaseA K LL) (lam : ↥(OL LL)), Irreducible lam → 5 ≤ (P.PD K).p →
    ∀ (t : ℕ) (h w η : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) (typ : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Bool)
      (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
      (χ : ℕ → ↥(GK K) →* (↥(OL LL))ˣ), tableLineDegreeTwo.TopHyp (P.PD K) (H.W K 1 LL hA.2.2).emb t h w η typ U T.ρ χ →
      (∀ i, Multiset.card (U i) = Module.finrank ↥LL.1 T.V) →
      ∃ (r : ℕ) (D : TopData (Module.finrank ℚ_[l] ↥(K0 K)) r) (ε : ↥(GK K) →* (↥(OL LL))ˣ),
        GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Hyp P K LL (H.W K 1 LL hA.2.2).emb D
          (GalData.mk lam T (χ 1) ε) ∧ D.t = t ∧
        (∀ i a, ((D.Ut i).count a : ℤ) = tableLineDegreeTwo.jTil U w t i a) ∧
        ∀ c ∈ Finset.Icc 1 t,
          (GalData.mk lam T (χ 1) ε : GalData ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)).chi c = χ c := by
  intro l _ P H K LL hA lam hlam h5 t h w η typ U T χ hyp hc
  have hp : (P.PD K).p = l := P.PD_p K
  have hS : Standing P K LL (H.W K 1 LL hA.2.2).emb lam :=
    (GlobalTheory.SenCompare.standing_iff P H lam).2 ⟨hp ▸ h5, hA, hlam⟩
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.letters_ne_zero hS⟩
  obtain ⟨ht, hposition, -, hcrys, hmult, hchi⟩ := hyp
  rw [hp] at hposition
  obtain ⟨D, hDt, hD, t1, t2, t3⟩ := GlobalTheory.TopWindow.exists_topData_of_positionHyps l _ t _ h w η typ U
    (Fact.out : l.Prime).two_le ht hc hposition
  obtain ⟨-, hcont1, hcrys1, hjump1⟩ := hchi 1 (Finset.mem_Icc.2 ⟨le_rfl, ht⟩)
  have hcyc : ∀ g, tableLineDegreeTwo.charL (LL := ↥LL.1) (GlobalTheory.AdmLoc.CycWitness.cycO P K LL) g =
      Formalism.MainNotions.N.cycLL (P.PD K) ↥LL.1 g := fun g => Units.ext (GlobalTheory.AdmLoc.CycWitness.cycO_val P K LL g)
  refine ⟨_, D, GlobalTheory.AdmLoc.CycWitness.cycO P K LL,
    ⟨hS, ⟨rfl, ⟨hcrys, fun i τ hτ a => ?_⟩, ⟨hcont1, hcrys1, fun i τ hτ a => ?_⟩,
      GlobalTheory.AdmLoc.CycWitness.cycO_val P K LL⟩, t1, t2, t3⟩, hDt, fun i a => (hD i).2.2 a, fun c hc' => ?_⟩
  · rw [(hD i).2.1]
    exact hmult i τ (AlgHom.ext fun x => hτ x) a
  · refine (hjump1 i τ (AlgHom.ext fun x => hτ x) a).trans ?_
    show _ = ((Multiset.count a {D.w i} : ℕ) : ℤ)
    rw [(hD i).1, Multiset.count_singleton]
    push_cast
    simp only [add_sub_cancel_right]
  · obtain ⟨hχc, -⟩ := hchi c hc'
    refine MonoidHom.ext fun g => ?_
    apply Units.map_injective (f := (algebraMap ↥(OL LL) ↥LL.1).toMonoidHom) Subtype.val_injective
    change tableLineDegreeTwo.charL (LL := ↥LL.1) (χ 1 * GlobalTheory.AdmLoc.CycWitness.cycO P K LL ^ (-((c : ℤ) - 1))) g =
      tableLineDegreeTwo.charL (LL := ↥LL.1) (χ c) g
    rw [hχc g, ← hcyc g]
    simp [tableLineDegreeTwo.charL, map_zpow]

end GlobalTheory.TopWindow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepsLatticeQuotientConjugateHalfOrthogonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DownLift.GenQuot

open GlobalTheory.PlaceModel

variable {D : D7} {S T : HSp D}

theorem symplO_nsmul_swap (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  induction k with
  | zero => simp only [zero_smul, symplO_zero_left, symplO_zero_right]
  | succ n ih => rw [succ_nsmul, succ_nsmul, symplO_add_left, symplO_add_right, ih]

theorem reps_orth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a : AE D, a * a = a → infPart D a = 0 → ∀ k : ℕ, 0 < k → ∃ Y : Finset (WO S T), Y.Nonempty ∧ (∀ y ∈ Y, IsHalf (cA D a) y ∧ k • y ∈ latH S T ΛS ΛT) ∧ (∀ y', IsHalf (cA D a) y' → k • y' ∈ latH S T ΛS ΛT → ∃! y, y ∈ Y ∧ ∃ u ∈ latH S T ΛS ΛT, IsHalf (cA D a) u ∧ y' - y = k • u) ∧ ∀ x, IsHalf a x → k • x ∈ latH S T ΛS ΛT → ((∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) → ∀ y ∈ Y, ψ (symplO S T x y) = 1) ∧ ((¬ ∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ x = k • u) → ∑ y ∈ Y, ψ (symplO S T x y) = 0) := by
  intro D ψ S T hψ ΛS ΛT hS hT a ha hinf k hk
  classical
  have hdual : ∀ u : WO S T, u.map (infPart D) = 0 →
      (u ∈ latH S T ΛS ΛT ↔ ∀ u' ∈ latH S T ΛS ΛT, ψ (symplO S T u u') = 1) :=
    (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T _ _ hψ hS hT).1
  have hfin : ∀ m : ℕ, 0 < m → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ latH S T ΛS ΛT, ∃ r ∈ R, ∃ u ∈ latH S T ΛS ΛT, t = r + m • u :=
    GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg fun _ => True
  have hsm : ∀ {b : AE D}, b * b = b → ∀ u ∈ latH S T ΛS ΛT, b • u ∈ latH S T ΛS ΛT ⊓ half S T b :=
    fun {b} hb u hu =>
    ⟨GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ b
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, hb])) u hu,
      (mem_half S T).2 (by rw [smul_smul, hb])⟩
  generalize latH S T ΛS ΛT = Λ at *
  have hc : cA D a * cA D a = cA D a := by rw [← RingHom.map_mul, ha]
  generalize hcdef : cA D a = c at *
  have tf : Function.Injective fun t : WO S T => k • t := fun x y hxy => by
    rw [← inv_smul_nsmul S T hk x, ← inv_smul_nsmul S T hk y]
    exact congrArg _ hxy

  let M : AddSubgroup (WO S T) := half S T c ⊓ Λ.comap (nsmulAddMonoidHom k)
  let N : AddSubgroup (WO S T) := (Λ ⊓ half S T c).map (nsmulAddMonoidHom k)
  have hM : ∀ y, y ∈ M ↔ IsHalf c y ∧ k • y ∈ Λ := fun y => by
    rw [isHalf_iff]; rfl
  have hN : ∀ n, n ∈ N ↔ ∃ u ∈ Λ, IsHalf c u ∧ n = k • u := fun n => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu.1, (isHalf_iff S T).2 hu.2, rfl⟩
    · rintro ⟨u, hu, hu', rfl⟩
      exact ⟨u, ⟨hu, (isHalf_iff S T).1 hu'⟩, rfl⟩
  let N' : AddSubgroup M := N.addSubgroupOf M
  have hq : ∀ y₁ y₂ : M, ((y₁ : M ⧸ N') = y₂ ↔ (y₂ : WO S T) - y₁ ∈ N) := fun y₁ y₂ => by
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [neg_add_eq_sub]

  obtain ⟨R2, hR2, hR2'⟩ := hfin (k * k) (Nat.mul_pos hk hk)
  have hP : ((fun t : WO S T => k • t) ⁻¹' ((fun r => c • r) '' R2)).Finite :=
    (hR2.image _).preimage tf.injOn
  have hcover : ∀ y : M, ∃ z : M, (z : WO S T) ∈ (fun t : WO S T => k • t) ⁻¹' ((fun r => c • r) '' R2) ∧
      (z : M ⧸ N') = y := by
    rintro ⟨y, hy⟩
    obtain ⟨hyc, hyk⟩ := (hM y).1 hy
    obtain ⟨r, hr, u, hu, hru⟩ := hR2' _ hyk
    have hcu := hsm hc u hu
    have hky : c • (k • y) = k • y := by
      rw [smul_comm]; exact congrArg (k • ·) ((mem_half S T).1 ((isHalf_iff S T).1 hyc))
    have hz : k • (y - k • (c • u)) = c • r := by
      rw [smul_sub, ← hky, hru, smul_add, mul_smul, smul_comm c k (k • u), smul_comm c k u]
      abel
    have hzM : y - k • (c • u) ∈ M := by
      refine (hM _).2 ⟨(isHalf_iff S T).2 ?_, ?_⟩
      · exact sub_mem ((isHalf_iff S T).1 hyc) (nsmul_mem hcu.2 k)
      · rw [smul_sub]
        exact sub_mem hyk (nsmul_mem (nsmul_mem hcu.1 k) k)
    refine ⟨⟨_, hzM⟩, ⟨r, hr, hz.symm⟩, (hq _ _).2 ?_⟩
    show y - (y - k • (c • u)) ∈ N
    rw [sub_sub_cancel]
    exact ⟨c • u, hcu, rfl⟩
  haveI hfinQ : Finite (M ⧸ N') := by
    let P' : Set M := {z | (z : WO S T) ∈ (fun t : WO S T => k • t) ⁻¹' ((fun r => c • r) '' R2)}
    have hP' : P'.Finite := hP.preimage Subtype.val_injective.injOn
    haveI := hP'.to_subtype
    refine Finite.of_surjective (fun z : P' => ((z : M) : M ⧸ N')) fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      obtain ⟨z, hz, hzy⟩ := hcover y
      exact ⟨⟨z, hz⟩, hzy⟩
  letI := Fintype.ofFinite (M ⧸ N')
  let rep : M ⧸ N' → WO S T := fun q => ((Quotient.out q : M) : WO S T)
  have hrepM : ∀ q, rep q ∈ M := fun q => (Quotient.out q : M).2
  have hrep : ∀ q, ((⟨rep q, hrepM q⟩ : M) : M ⧸ N') = q := fun q => QuotientAddGroup.out_eq' q
  have hrepinj : Function.Injective rep := fun q₁ q₂ h => by
    rw [← hrep q₁, ← hrep q₂]
    simp only [h]
  refine ⟨Finset.univ.image rep, ⟨rep 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    exact (hM _).1 (hrepM q)
  · intro y' hy'c hy'k
    have hy'M : y' ∈ M := (hM y').2 ⟨hy'c, hy'k⟩
    refine ⟨rep (⟨y', hy'M⟩ : M), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (hN _).1 ?_⟩, ?_⟩
    · exact (hq _ _).1 (hrep _)
    · rintro y ⟨hyY, hyN⟩
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hyY
      have := (hq ⟨rep q, hrepM q⟩ ⟨y', hy'M⟩).2 ((hN _).2 hyN)
      rw [hrep] at this
      rw [this]
  intro x hx hkx
  have hxfin : ∀ {u : WO S T}, IsHalf a u → u.map (infPart D) = 0 := fun hu =>
    GlobalTheory.PlaceVec.half_infPart hinf ((isHalf_iff S T).1 hu)
  have hkxh : IsHalf a (k • x) := (isHalf_iff S T).2 (nsmul_mem ((isHalf_iff S T).1 hx) k)
  refine ⟨?_, fun hnot => ?_⟩
  · rintro ⟨u, hu, hua, rfl⟩ y hy
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hy
    rw [symplO_nsmul_swap]
    exact (hdual u (hxfin hua)).1 hu _ ((hM _).1 (hrepM q)).2
  ·
    have hconst : ∀ y₁ y₂ : M, (y₁ : M ⧸ N') = y₂ →
        ψ (symplO S T x (y₂ : WO S T)) = ψ (symplO S T x (y₁ : WO S T)) := fun y₁ y₂ h => by
      obtain ⟨u, hu, -, hu'⟩ := (hN _).1 ((hq _ _).1 h)
      have e : (y₂ : WO S T) = y₁ + k • u := by rw [← hu']; abel
      rw [e, symplO_add_right, AddChar.map_add_eq_mul, ← symplO_nsmul_swap,
        (hdual _ (hxfin hkxh)).1 hkx u hu, mul_one]

    obtain ⟨x', hx'h, hx'⟩ := half_div S T a k hk x ((isHalf_iff S T).1 hx)
    have hx'Λ : x' ∉ Λ := fun h => hnot ⟨x', h, (isHalf_iff S T).2 hx'h, hx'.symm⟩
    have hx'fin := hxfin ((isHalf_iff S T).2 hx'h)
    obtain ⟨l, hl, hψl⟩ : ∃ l ∈ Λ, ψ (symplO S T x' l) ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hx'Λ ((hdual x' hx'fin).2 hcon)
    have hl' := hsm hc l hl
    obtain ⟨y₀, hy₀h, hy₀⟩ := half_div S T c k hk _ hl'.2
    have hy₀M : y₀ ∈ M := (hM _).2 ⟨(isHalf_iff S T).2 hy₀h, hy₀ ▸ hl'.1⟩
    have hψ0 : ψ (symplO S T x y₀) ≠ 1 := by
      rw [← hx', symplO_nsmul_swap, hy₀, ← hcdef, ← symplO_smul, (mem_half S T).1 hx'h]
      exact hψl

    have hsum : ∑ y ∈ Finset.univ.image rep, ψ (symplO S T x y) = ∑ q : M ⧸ N', ψ (symplO S T x (rep q)) :=
      Finset.sum_image fun q₁ _ q₂ _ h => hrepinj h
    rw [hsum]
    have hshift : ∑ q : M ⧸ N', ψ (symplO S T x (rep q)) =
        (∑ q : M ⧸ N', ψ (symplO S T x (rep q))) * ψ (symplO S T x y₀) := by
      rw [Finset.sum_mul]
      refine (Fintype.sum_equiv (Equiv.addRight ((⟨y₀, hy₀M⟩ : M) : M ⧸ N')) _ _ fun q => ?_).symm
      rw [← AddChar.map_add_eq_mul, ← symplO_add_right]
      have := hconst (⟨rep q, hrepM q⟩ + ⟨y₀, hy₀M⟩) ⟨rep (q + ((⟨y₀, hy₀M⟩ : M) : M ⧸ N')), hrepM _⟩
        (by rw [hrep, QuotientAddGroup.mk_add, hrep])
      simpa using this.symm
    have h0 : (∑ q : M ⧸ N', ψ (symplO S T x (rep q))) * (ψ (symplO S T x y₀) - 1) = 0 := by
      rw [mul_sub, mul_one, ← hshift, sub_self]
    exact (mul_eq_zero.1 h0).resolve_right (sub_ne_zero.2 hψ0)

end GlobalTheory.DownLift.GenQuot

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitarySupportedAtSplitPlaceLift
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

namespace GlobalTheory.DownLift.SplitCoef

open GlobalTheory.ParahoricLift GlobalTheory.LevSplit Formalism.L2.NTheta

theorem lift_map_eq_of_smul {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (φ : A →+* B) (p : A) (hp : φ p = 1)
    (M M' : Matrix (Fin m) (Fin n) A) (h : p • M = p • M') : M.map φ = M'.map φ := by
  ext i j
  have := congrArg φ (congrFun (congrFun h i) j)
  simpa only [Matrix.smul_apply, smul_eq_mul, map_mul, hp, one_mul, Matrix.map_apply] using this

theorem lift_smul_eq_of_map {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (φ : A →+* B) (p : A)
    (hker : ∀ z, φ z = 0 ↔ p * z = 0) (M M' : Matrix (Fin m) (Fin n) A) (h : M.map φ = M'.map φ) : p • M = p • M' := by
  ext i j
  have h2 := congrFun (congrFun h i) j
  simp only [Matrix.map_apply] at h2
  have h3 : φ (M i j - M' i j) = 0 := by rw [map_sub, h2, sub_self]
  rw [hker, mul_sub, sub_eq_zero] at h3
  simpa only [Matrix.smul_apply, smul_eq_mul] using h3

theorem lift_smul_conj {A : Type} [CommRing A] {n : ℕ} (β : GL (Fin n) A) (p : A) (M : Matrix (Fin n) (Fin n) A) :
    p • (β.1 * M * (β⁻¹).1) = β.1 * (p • M) * (β⁻¹).1 := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem lift_smul_conj_inv {A : Type} [CommRing A] {n : ℕ} (β : GL (Fin n) A) (p : A) (M : Matrix (Fin n) (Fin n) A) :
    p • ((β⁻¹).1 * M * β.1) = (β⁻¹).1 * (p • M) * β.1 := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem lift_conj_mul_smul {A : Type} [CommRing A] {n : ℕ} (β : GL (Fin n) A) (p : A) (M M' : Matrix (Fin n) (Fin n) A)
    (h : p • (M * M') = p • (1 : Matrix (Fin n) (Fin n) A)) :
    p • ((β.1 * M * (β⁻¹).1) * (β.1 * M' * (β⁻¹).1)) = p • (1 : Matrix (Fin n) (Fin n) A) := by
  have e3 : (β.1 * M * (β⁻¹).1) * (β.1 * M' * (β⁻¹).1) = β.1 * (M * M') * (β⁻¹).1 := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (β⁻¹).1 β.1, Units.inv_mul, Matrix.one_mul]
  rw [e3, lift_smul_conj, h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Units.mul_inv]

theorem lift_conj_part {A : Type} [CommRing A] {n : ℕ} (β : GL (Fin n) A) (p : A) (g M : Matrix (Fin n) (Fin n) A)
    (h : p • g = p • (β.1 * M * (β⁻¹).1)) : p • ((β⁻¹).1 * g * β.1) = p • M := by
  rw [lift_smul_conj_inv, h, lift_smul_conj]
  simp only [Matrix.mul_assoc]
  rw [Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]

theorem lift_chart_idem {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v}
    (hker : ∀ z, φ z = 0 ↔ toEAf D e * z = 0) (he : toEAf D e * toEAf D e = toEAf D e) : φ (toEAf D e) = 1 := by
  have h0 : φ (1 - toEAf D e) = 0 := by
    rw [hker, mul_sub, mul_one, he, sub_self]
  rw [map_sub, map_one, sub_eq_zero] at h0
  exact h0.symm

theorem lift_chart_int {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v}
    (hsurj : Function.Surjective φ) (h1 : φ (toEAf D e) = 1)
    (hint : ∀ z, toEAf D e * z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ φ z ∈ v.adicCompletionIntegers D.host.F)
    (o : GlobalTheory.SplitHecke.Ov D v) : ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, φ (s : Formalism.IndefR.Lev.EAf D) = (o : Fv D.host.F v) := by
  obtain ⟨z, hz⟩ := hsurj (o : Fv D.host.F v)
  refine ⟨⟨toEAf D e * z, (hint z).2 (hz ▸ o.2)⟩, ?_⟩
  show φ (toEAf D e * z) = _
  rw [map_mul, h1, one_mul, hz]

theorem lift_frG_one {D : D7} (T : HSp D) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) :
    Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG T βT 1 = 1 := by
  unfold Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG
  rw [map_one, mul_one, inv_mul_cancel]

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_St_of_part_inv (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hβ : IsFrame β Λ) (hΛ : HatSelfDual σ J Λ)
    (p : Formalism.L2.Herm.intAf F E) (hq : Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) p ∈ Formalism.L2.Herm.intAf F E)
    (Y Y' : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E))
    (hmm : (p : E ⊗[F] Formalism.L2.Herm.Af F) • ((β.1 * Y.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1) *
      (β.1 * Y'.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1)) = (p : E ⊗[F] Formalism.L2.Herm.Af F) • 1)
    (g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hg : g ∈ Formalism.UG.UPts σ J (Formalism.L2.Herm.Af F))
    (f : E ⊗[F] Formalism.L2.Herm.Af F) (hf : f = p + Formalism.UG.sigR σ (Formalism.L2.Herm.Af F) p) (hs : f • (g.1 - 1) = g.1 - 1)
    (hY : (p : E ⊗[F] Formalism.L2.Herm.Af F) • g.1 =
      (p : E ⊗[F] Formalism.L2.Herm.Af F) • (β.1 * Y.map (Formalism.L2.Herm.intAf F E).subtype * (β⁻¹).1)) : g ∈ St β := by
  subst hf
  exact (mem_St_iff β Λ hβ g).2 (stab_of_part _ _ _ hΛ p.2 hq g hg hs _ _ (frame_mulVec β Λ hβ Y)
    (frame_mulVec β Λ hβ Y') hmm hY)

end Gen


set_option maxHeartbeats 1000000 in
theorem exists_supp_lift_adj : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N : ℕ), IsBaseFrame S βS Λ N → ∀ h : GL (Fin S.rank) (GlobalTheory.SplitHecke.Ov D v), ∃ κ : GA D S, SuppAt e S κ ∧ κ ∈ GfC S ∧ finE S κ ∈ St βS ∧ (redFn βS PP (finE S κ)).val.map ι = h.val.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) ∧ (∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn βS PP' (finE S κ) = 1) ∧ ∀ x : WO S T, rdAdj S T βS βT φ (actO S T κ 1 x) = h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) * rdAdj S T βS βT φ x := by
  intro D S T βS βT e PP v φ ι he hL Λ N hB h
  obtain ⟨hsurj, hker, hint, hres⟩ := hL
  have := PP.isPrime
  obtain ⟨p, hp, hpp, hres1⟩ := exists_idem_int he
  have hpe : toEAf D e = (p : Formalism.IndefR.Lev.EAf D) := hp.symm
  have hpp' : toEAf D e * toEAf D e = toEAf D e := by rw [hpe]; exact congrArg Subtype.val hpp
  have hp1 : φ (p : Formalism.IndefR.Lev.EAf D) = 1 := hpe ▸ lift_chart_idem hker hpp'
  have hker' : ∀ z, φ z = 0 ↔ (p : Formalism.IndefR.Lev.EAf D) * z = 0 := fun z => hpe ▸ hker z
  choose lf hlf using lift_chart_int hsurj (hpe ▸ hp1) hint
  set Y : Matrix (Fin S.rank) (Fin S.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := h.val.map lf with hYdef
  set Y' : Matrix (Fin S.rank) (Fin S.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E) := (h⁻¹).val.map lf with hY'def
  have hY : (Y.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).map φ =
      h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := Matrix.ext fun i j => hlf _
  have hY' : (Y'.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).map φ =
      (h⁻¹).val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := Matrix.ext fun i j => hlf _
  have hYY : (p : Formalism.IndefR.Lev.EAf D) • (Y.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype *
      Y'.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) = (p : Formalism.IndefR.Lev.EAf D) • 1 := by
    refine lift_smul_eq_of_map φ _ hker' _ _ ?_
    rw [Matrix.map_mul, hY, hY', ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hmm := lift_conj_mul_smul βS _ _ _ hYY
  have hmm' := hmm
  rw [hp] at hmm'
  obtain ⟨κ, hs, hκ⟩ := split_lift_fin S he.1 _ _ hmm'
  have hP : IsPrimeIdem PP e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents S
  have hsf := supp_fin S (f := e + cA D e) hs
  have hκ' : (p : Formalism.IndefR.Lev.EAf D) • (finE S κ).1 =
      (p : Formalism.IndefR.Lev.EAf D) • (βS.1 * Y.map (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype * (βS⁻¹).1) := by
    rw [hp]; exact hκ
  have hf : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add (f := _), finSw_cA, hp]
  have hSt : finE S κ ∈ St βS :=
    mem_St_of_part_inv D.sp.cm.sig S.gram Λ βS hB.1 (hatL_selfDual hB) p (sigR_int p.2) Y Y' hmm (finE S κ)
      (finE_mem_UA S κ) _ hf hsf hκ'
  refine ⟨κ, hs, (T3 PP e _ hP).2.2.1 κ hs, hSt, ?_, fun P' h1 h2 => ?_, fun x => ?_⟩
  · rw [redFn_of_smul_eq βS PP _ hSt p hres1 Y hκ']
    ext i j
    simp only [Matrix.map_apply]
    exact hres (lf (h.val i j)) (h.val i j) (hlf _).symm
  · obtain ⟨y, y', hy, hyy, a1, a2⟩ := exists_sep h1 fun h => h2 (isConjPl_symm h)
    obtain ⟨w, hw⟩ := idem_div_int hP y y' hyy a1 a2
    refine redFn_eq_one βS P' _ hSt (w * oToS D.host.F D.host.E y) ?_ ?_
    · rw [RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hy, mul_zero]
    · have e1 : ((w * oToS D.host.F D.host.E y : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Lev.EAf D) =
          finSw D (e + cA D e) := hw
      rw [e1]
      exact hsf
  · have hG : (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG S βS κ).val.map φ =
        h.val.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := by
      rw [← hY]
      refine lift_map_eq_of_smul φ _ hp1 _ _ ?_
      unfold Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frG
      rw [Units.val_mul, Units.val_mul]
      exact lift_conj_part βS _ _ _ hκ'
    unfold rdAdj
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_actO, lift_frG_one, inv_one, Units.val_one, Matrix.mul_one, Matrix.map_mul, hG]

end GlobalTheory.DownLift.SplitCoef
end

