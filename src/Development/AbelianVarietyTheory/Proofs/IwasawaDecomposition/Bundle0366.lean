module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Formalism.LocalToGlobal.Columns.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
public import Formalism.LocalToGlobal.Columns.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesStdMatched
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsForgetsFrames

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteColumnConfigurationsWitnesses
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.HFld

open Formalism.L2.DIV

theorem norm_piG_le {P : Pre} (px : PreX P) (i : Fin 2) (φ : P.host.E →+* ℂ) :
    ‖φ (px.piG i : P.host.E)‖ ≤ (P.host.g i : ℝ) + 1 := by
  have h := congrArg φ (px.piG_norm i)
  have hc : φ (P.host.conj (px.piG i : P.host.E)) = starRingEnd ℂ (φ (px.piG i : P.host.E)) := Formalism.HC.HostAx.conjE_apply _ _ _
  rw [map_mul, hc, map_natCast, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  have h2 : ‖φ (px.piG i : P.host.E)‖ ^ 2 = (P.host.g i : ℝ) := by exact_mod_cast h
  nlinarith [sq_nonneg (‖φ (px.piG i : P.host.E)‖ - 1), norm_nonneg (φ (px.piG i : P.host.E))]

theorem finite_piG (P : Pre) :
    {g : Fin 2 → 𝓞 P.host.E | ∀ i (φ : P.host.E →+* ℂ), ‖φ (g i : P.host.E)‖ ≤ (P.host.g i : ℝ) + 1}.Finite := by
  refine (Set.Finite.pi (t := fun i => ((↑) : 𝓞 P.host.E → P.host.E) ⁻¹'
    {x | IsIntegral ℤ x ∧ ∀ φ : P.host.E →+* ℂ, ‖φ x‖ ≤ (P.host.g i : ℝ) + 1}) fun i =>
      (NumberField.Embeddings.finite_of_norm_le P.host.E ℂ _).preimage
        RingOfIntegers.coe_injective.injOn).subset ?_
  intro g hg i _
  exact ⟨RingOfIntegers.isIntegral_coe _, hg i⟩


open Classical in
def chiOf {P : Pre} (f : Top.Fr P) : Fin P.R.m → HeightOneSpectrum (𝓞 P.host.E) → 𝓞 P.host.E → ℂ :=
  fun j w y => if h : (f.P.Div 0 w ∨ f.P.Div 1 w) ∧ (y : P.host.E) ≠ 0 ∧ IsUnit (Ideal.Quotient.mk w.asIdeal y) then
    ((((f.mu0 j).locK w (Units.mk0 (y : P.host.E) h.2.1))⁻¹ : ℂˣ) : ℂ) else 0

theorem chiC_eq {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) (h : I.Ok) : chiC I = chiOf I.C := by
  classical
  funext j w y
  have hv : w ∈ (B.primes px).vGs ↔ (I.C.P.Div 0 w ∨ I.C.P.Div 1 w) := by
    rw [← h.pibar 0 w, ← h.pibar 1 w]
    simp [Formalism.L2.Col.Primes.vGs]
  unfold chiC chiOf
  by_cases hw : w ∈ (B.primes px).vGs
  · by_cases hu : IsUnit (Ideal.Quotient.mk w.asIdeal y)
    · have hy : (y : B.host.E) ≠ 0 := by
        intro h0
        have hy0 : y = 0 := RingOfIntegers.coe_injective (by simpa using h0)
        subst hy0
        haveI : w.asIdeal.IsPrime := w.isPrime
        exact hu.ne_zero (map_zero _)
      rw [dite_eq_left hw, dite_eq_left hu, dite_eq_left ⟨hv.1 hw, hy, hu⟩]
      have ht := (h.ch_tied.mu0 j).atg ⟨w, hw⟩ (Units.mk0 _ hy) y hu.unit rfl (by simp)
      rw [Units.val_inv_eq_inv_val, ht, Units.val_inv_eq_inv_val, map_inv₀, inv_inv]
    · rw [dite_eq_left hw, dite_eq_right hu, dite_eq_right (fun h' => hu h'.2.2)]
  · rw [dite_eq_right hw, dite_eq_right (fun h' => hw (hv.2 h'.1))]

def ramPl {P : Pre} (ξ : Formalism.L2.Host.HChar P.host.E) : Set (HeightOneSpectrum (𝓞 P.host.F)) :=
  {v | ∃ a : Neutral.B1.Ideles P.host.E, Col2.finAf P.host.F P.host.E a ∈ inertAt P.host.E v ∧ ξ.1 a ≠ 1}

theorem qprime_eq_of_reads {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [Field K]
    {σ : K →+* ℂ} {μ : Chr F E K} {ξ : Formalism.L2.Host.HChar E} (h : Col2.Reads σ μ ξ) :
    Qprime μ = {v | ∃ a : Neutral.B1.Ideles E, Col2.finAf F E a ∈ inertAt E v ∧ ξ.1 a ≠ 1} := by
  ext v
  simp only [Qprime, Set.mem_setOf_eq, SetLike.not_le_iff_exists, MonoidHom.mem_ker]
  constructor
  · rintro ⟨y, hy, hne⟩
    obtain ⟨a, rfl⟩ := Col2.finAf_surjective F E y
    refine ⟨a, hy, fun h1 => hne (Units.ext (σ.injective ?_))⟩
    rw [← h a, h1]
    simp
  · rintro ⟨a, ha, hne⟩
    refine ⟨_, ha, fun h1 => hne (Units.ext ?_)⟩
    rw [h a, h1]
    simp


open Classical in
def qBound {P : Pre} (ξ : Formalism.L2.Host.HChar P.host.E) : Set (HeightOneSpectrum (𝓞 P.host.E)) :=
  if (ramPl ξ).Finite then {Q | ∃ v ∈ ramPl ξ, Ideal.under (𝓞 P.host.F) Q.asIdeal = v.asIdeal} else ∅

theorem finite_qBound {P : Pre} (ξ : Formalism.L2.Host.HChar P.host.E) : (qBound ξ).Finite := by
  classical
  unfold qBound
  split_ifs with hf
  · refine (hf.biUnion fun v _ => Ideal.finite_factors
      (I := Ideal.map (algebraMap (𝓞 P.host.F) (𝓞 P.host.E)) v.asIdeal) ?_).subset ?_
    · rw [Ideal.zero_eq_bot, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
      exact v.ne_bot
    · rintro Q ⟨v, hv, hQ⟩
      refine Set.mem_biUnion hv ?_
      show Q.asIdeal ∣ _
      rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
      exact hQ.ge
  · exact Set.finite_empty

theorem qC_subset {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) (h : I.Ok) (ξ : Formalism.L2.Host.HChar B.host.E) :
    (↑(qC I ξ) : Set (HeightOneSpectrum (𝓞 B.host.E))) ⊆ qBound (P := B.toPre) ξ := by
  classical
  unfold qC
  split_ifs with hx
  · have hr : Qprime (I.tup hx.choose : Chr B.fields.F B.fields.E B.fields.K) = ramPl (P := B.toPre) ξ := by
      have := qprime_eq_of_reads (h.xi_reads hx.choose)
      rw [hx.choose_spec] at this
      exact this
    intro Q hQ
    have hQ' : Q ∈ Formalism.L2.Col.QE I.sel (I.tup hx.choose : Chr B.fields.F B.fields.E B.fields.K) := hQ
    unfold Formalism.L2.Col.QE at hQ'
    split_ifs at hQ' with hfin
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hQ'
      rw [Set.Finite.mem_toFinset] at hv
      unfold qBound
      rw [if_pos (hr ▸ hfin)]
      exact ⟨v, hr ▸ hv, h.sel_ok v⟩
    · simp at hQ'
  · simp

theorem qC_of_not_mem {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) {ξ : Formalism.L2.Host.HChar B.host.E}
    (hξ : ξ ∉ Set.range I.xi) : qC I ξ = ∅ := by
  classical
  unfold qC
  rw [dite_eq_right fun ⟨a, ha⟩ => hξ ⟨a, ha⟩]

theorem finite_qFns {P : Pre} {Ξ : Set (Formalism.L2.Host.HChar P.host.E)} (hΞ : Ξ.Finite) :
    {q : Formalism.L2.Host.HChar P.host.E → Finset (HeightOneSpectrum (𝓞 P.host.E)) |
      (∀ ξ, (↑(q ξ) : Set (HeightOneSpectrum (𝓞 P.host.E))) ⊆ qBound ξ) ∧ ∀ ξ ∉ Ξ, q ξ = ∅}.Finite := by
  classical
  haveI := hΞ.to_subtype
  refine Set.Finite.of_finite_image (f := fun q (ξ : Ξ) => q ξ) ?_ ?_
  · refine (Set.Finite.pi (t := fun ξ : Ξ => {s : Finset (HeightOneSpectrum (𝓞 P.host.E)) |
      (↑s : Set (HeightOneSpectrum (𝓞 P.host.E))) ⊆ qBound (ξ : Formalism.L2.Host.HChar P.host.E)}) fun ξ =>
        (finite_qBound (ξ : Formalism.L2.Host.HChar P.host.E)).finite_subsets.preimage Finset.coe_injective.injOn).subset ?_
    rintro _ ⟨q, hq, rfl⟩ ξ _
    exact hq.1 ξ
  · intro q hq q' hq' he
    funext ξ
    by_cases hξ : ξ ∈ Ξ
    · exact congrFun he ⟨ξ, hξ⟩
    · rw [hq.2 ξ hξ, hq'.2 ξ hξ]

theorem exists_finite_cfg : ∀ (P : Pre) (f : Top.Fr P) (F F₀ : IntermediateField ℚ ℂ) (Ξ : Set (Formalism.L2.Host.HChar P.host.E)),
  ∃ (n : ℕ) (Wt : Fin n → Σ B0 : Base, Σ px0 : PreX B0.toPre, Col2.ColIn B0 px0),
    (∀ i, (Wt i).1.fields.Ok ∧ (Wt i).2.2.Ok) ∧
    ∀ (B : Base) (px : PreX B.toPre) (I : Col2.ColIn B px), B.fields.Ok → I.Ok → B.toPre = P → HEq I.C f → B.KsC = F →
      B.fixedCoefficientFieldInComplex = F₀ → HEq (Set.range I.xi) Ξ → ∃ i, GlobalTheory.Mem.HFld.SameCfg B px I (Wt i).1 (Wt i).2.1 (Wt i).2.2 := by
  intro P f F F₀ Ξ
  classical
  let admitted : (Σ B0 : Base, Σ px0 : PreX B0.toPre, Col2.ColIn B0 px0) → Prop := fun x =>
    x.1.fields.Ok ∧ x.2.2.Ok ∧ x.1.toPre = P ∧ HEq x.2.2.C f ∧ x.1.KsC = F ∧ x.1.fixedCoefficientFieldInComplex = F₀ ∧ HEq (Set.range x.2.2.xi) Ξ
  let Tr : Type := (Fin 2 → 𝓞 P.host.E) × (Fin P.R.m → HeightOneSpectrum (𝓞 P.host.E) → 𝓞 P.host.E → ℂ) ×
    (Formalism.L2.Host.HChar P.host.E → Finset (HeightOneSpectrum (𝓞 P.host.E)))
  let T : Set Tr := {t | ∃ x, admitted x ∧ HEq x.2.1.piG t.1 ∧ HEq (chiC x.2.2) t.2.1 ∧ HEq (qC x.2.2) t.2.2}
  have hT : T.Finite := by
    by_cases hΞ : Ξ.Finite
    · refine ((finite_piG P).prod ((Set.finite_singleton (chiOf f)).prod (finite_qFns hΞ))).subset ?_
      rintro ⟨t1, t2, t3⟩ ⟨⟨B, px, I⟩, ⟨-, hI, hP, hC, -, -, hX⟩, h1, h2, h3⟩
      dsimp only at hI hP hC hX h1 h2 h3
      subst hP
      cases eq_of_heq hC
      cases eq_of_heq hX
      cases eq_of_heq h1
      cases eq_of_heq h2
      cases eq_of_heq h3
      refine ⟨fun i φ => norm_piG_le px i φ, chiC_eq I hI, fun ξ => qC_subset I hI ξ, fun ξ hξ => qC_of_not_mem I hξ⟩
    · convert Set.finite_empty
      ext ⟨t1, t2, t3⟩
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨B, px, I⟩, ⟨-, -, hP, -, -, -, hX⟩, -⟩
      dsimp only at hP hX
      subst hP
      exact hΞ (eq_of_heq hX ▸ Set.finite_range I.xi)
  have hch : ∀ t : T, ∃ x, admitted x ∧ HEq x.2.1.piG t.1.1 ∧ HEq (chiC x.2.2) t.1.2.1 ∧ HEq (qC x.2.2) t.1.2.2 := fun t => t.2
  choose w hwA hwR using hch
  haveI := hT.fintype
  let e := Fintype.equivFin T
  refine ⟨Fintype.card T, fun i => w (e.symm i), fun i => ⟨(hwA _).1, (hwA _).2.1⟩, ?_⟩
  intro B px I hBo hIo hP hC hK hL hX
  have hx : admitted ⟨B, px, I⟩ := ⟨hBo, hIo, hP, hC, hK, hL, hX⟩
  subst hP
  have ht : ((px.piG, chiC I, qC I) : Tr) ∈ T := ⟨⟨B, px, I⟩, hx, HEq.rfl, HEq.rfl, HEq.rfl⟩
  refine ⟨e ⟨_, ht⟩, ?_⟩
  have key : ∀ s : T, s = ⟨_, ht⟩ → GlobalTheory.Mem.HFld.SameCfg B px I (w s).1 (w s).2.1 (w s).2.2 := by
    rintro s rfl
    obtain ⟨-, -, h3, h4, -, -, h6⟩ := hwA ⟨_, ht⟩
    obtain ⟨r1, r2, r3⟩ := hwR ⟨_, ht⟩
    exact ⟨h3.symm, hC.trans h4.symm, hX.trans h6.symm, r1.symm, r2.symm, r3.symm⟩
  exact key _ (e.symm_apply_apply _)

end GlobalTheory.Mem.HFld

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalComponentConjSplitPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutQuot

theorem conjLoc_exists_split (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host) (h : IsConjPl D.host w s.w) :
    ∃ s' : SplitPlace D.host.E, s'.w = w := by
  have hc : ∀ x : D.host.E, D.host.conj x = IsCMField.complexConj D.host.E x := fun x => by
    apply D.host.φ₀.injective
    rw [NumberField.IsCMField.complexEmbedding_complexConj]
    exact Formalism.HC.HostAx.conjE_apply _ _ _
  refine ⟨⟨s.v, s.i.comp (IsCMField.complexConj D.host.E).toAlgHom⟩, ?_⟩
  apply HeightOneSpectrum.ext
  ext x
  have hy : ((IsCMField.ringOfIntegersComplexConj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [hc]; rfl
  rw [h x _ hy]
  exact Iff.rfl

theorem conjLoc (D : D7) (π : NG.AutRep D.host.E D.R.nV) (s : SplitPlace D.host.E) (w : PlE D.host)
    (h : IsConjPl D.host w s.w) : ∃ x, GlobalTheory.AutQuot.LocAt π w x := by
  obtain ⟨s', rfl⟩ := conjLoc_exists_split D s w h
  obtain ⟨σ, hσ, -⟩ := _root_.GlobalTheory.LocCompSplit.main D.host.E D.R.nV π s'
  exact ⟨_, s', σ, rfl, hσ, HEq.rfl⟩

end GlobalTheory.AutQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNotMemConjMem
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MoveUpLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem localization_le_localization_of_le {M N : Submodule (𝓞 E) (Sp E n)} (P : HeightOneSpectrum (𝓞 E))
    (h : M ≤ N) : Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N :=
  localization_le_of_smul_mem (one_notMem P) fun y hy => by rw [one_smul]; exact h hy

theorem exists_notMem_conj_mem (P : ST) (hP : MoveHyp ST SG P) :
    ∃ a : 𝓞 E, a ∉ P.1.asIdeal ∧ ∀ Q : ST, cO E a ∈ Q.1.asIdeal := by
  classical
  have hex : ∀ Q : ST, ∃ b ∈ Q.1.asIdeal, b ∉ (conjPrime₂ P.1).asIdeal := fun Q =>
    exists_mem_notMem (hP.st Q)
  choose b hb hb' using hex
  refine ⟨cO E (∏ Q : ST, b Q), ?_, fun Q => ?_⟩
  · intro h
    have h' : ∏ Q : ST, b Q ∈ (conjPrime₂ P.1).asIdeal := (mem_conjP _ _).2 h
    obtain ⟨Q, -, hQ⟩ := (Ideal.IsPrime.prod_mem_iff (hp := (conjPrime₂ P.1).isPrime)).1 h'
    exact hb' Q hQ
  · rw [cO_cO]
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem b (Finset.mem_univ Q)) (hb Q)

theorem localization_dual_L_eq_localization_N {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) :
    Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) d.L) = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.N := by
  obtain ⟨a, ha, haQ⟩ := exists_notMem_conj_mem P hP
  exact le_antisymm (localization_le_of_smul_mem ha fun y hy => hd.smul_Lsh_mem_N haQ hy)
    (localization_le_localization_of_le P.1 hd.N_le_Lsh)

theorem localization_L_eq_localization_kerAt {d : Deco E n ST SG} (hd : d.Ok) (P : ST) :
    Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.L = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.kerAt P) := by
  ext y
  rw [hd.mem_locP_L]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨s, hs, hsy⟩ := (mem_locP _ _ _).1 h1
    refine (mem_locP _ _ _).2 ⟨s, hs, (hd.mem_kerAt P _).2 ⟨hsy, ?_⟩⟩
    rw [hd.f_smul P s y h1, h2, mul_zero]
  · intro h
    obtain ⟨s, hs, hsy⟩ := (mem_locP _ _ _).1 h
    obtain ⟨h1, h2⟩ := (hd.mem_kerAt P _).1 hsy
    have hy : y ∈ d.at P.1 := (mem_locP _ _ _).2 ⟨s, hs, h1⟩
    refine ⟨hy, ?_⟩
    rw [hd.f_smul P s y hy] at h2
    exact (mul_eq_zero.1 h2).resolve_left (mk_ne_zero hs)

theorem localization_up_L_eq_localization_N {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) {x : Sp E n} (hx : x ∈ d.N)
    (hfx : d.f P x = 1) :
    Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.up P q x).L = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.N := by
  have hd' := hd.up P hP hq hq2 hx hfx
  rw [localization_L_eq_localization_kerAt hd' P, ← (hd'.dnN_spec P hP.ne).2.2.2, hd.dnN_up P hP hq hq2 hx hfx]

theorem localization_dual_up_L {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) {x : Sp E n} (hx : x ∈ d.N)
    (hfx : d.f P x = 1) :
    Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) (d.up P q x).L) =
      Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) d.L ⊔
        Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x}) := by
  have hd' := hd.up P hP hq hq2 hx hfx
  obtain ⟨-, -, -, h4, h5⟩ := upN_spec hd.lat hd.uni P.1 hP.ne hx
  rw [localization_dual_L_eq_localization_N hd' P hP]
  change Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (upN P.1.asIdeal d.N x) = _
  have hq0' : q ≠ 0 := fun h => hq2 (h ▸ Submodule.zero_mem _)
  have hq0 : algebraMap (𝓞 E) E q ≠ 0 := by rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  obtain ⟨a, ha, haQ⟩ := exists_notMem_conj_mem P hP
  obtain ⟨b, hb, hbP⟩ := exists_mem_notMem hP.ne
  obtain ⟨c, hc, r, hr, hcr⟩ := exists_inv_unif P.1 hq hq2
  have hAS : upA P.1.asIdeal d.N x ≤
      d.N ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x} := by
    refine sup_le le_sup_left ?_
    rw [Submodule.span_le]
    rintro z ⟨e, he, rfl⟩
    obtain ⟨β, hβ⟩ := Formalism.HermitianLatticesTheory.neighbourConstruct_mem_inv.1 he q hq
    have e1 : e • x = β • ((algebraMap (𝓞 E) E q)⁻¹ • x) := by
      rw [← algebraMap_smul E β, smul_smul, hβ, mul_comm (algebraMap (𝓞 E) E q) e, mul_assoc,
        mul_inv_cancel₀ hq0, mul_one]
    rw [SetLike.mem_coe, e1]
    exact (le_sup_right : _ ≤ d.N ⊔ _)
      (Submodule.smul_mem _ β (Submodule.subset_span rfl))
  have hSA : ∀ z ∈ d.N ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x},
      r • z ∈ upA P.1.asIdeal d.N x := by
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hz
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
    have e2 : r • (t • ((algebraMap (𝓞 E) E q)⁻¹ • x)) = t • (c • x) := by
      rw [smul_comm r t, ← algebraMap_smul E r, smul_smul, ← hcr, mul_comm (algebraMap (𝓞 E) E q) c,
        mul_assoc, mul_inv_cancel₀ hq0, mul_one]
    rw [smul_add, e2]
    exact Submodule.add_mem_sup (d.N.smul_mem r hu)
      (Submodule.smul_mem _ t (Submodule.subset_span ⟨c, hc, rfl⟩))
  have hupN : Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (upN P.1.asIdeal d.N x) =
      Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (upA P.1.asIdeal d.N x) :=
    le_antisymm (localization_le_localization_of_le P.1 h4)
      (localization_le_of_smul_mem hbP fun y hy => h5 (Submodule.smul_mem_smul hb hy))
  have hA : Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (upA P.1.asIdeal d.N x) =
      Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.N ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x}) :=
    le_antisymm (localization_le_localization_of_le P.1 hAS) (localization_le_of_smul_mem hr hSA)
  have hL : Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) d.L ⊔
        Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x}) =
      Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.N ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x}) := by
    refine le_antisymm (localization_le_of_smul_mem ha fun z hz => ?_)
      (localization_le_localization_of_le P.1 (sup_le_sup_right hd.N_le_Lsh _))
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hz
    rw [smul_add]
    exact Submodule.add_mem_sup (hd.smul_Lsh_mem_N haQ hu) (Submodule.smul_mem _ a hv)
  rw [hupN, hA, hL]

theorem lattices_at_up : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (d : Deco E n ST SG), d.Ok → ∀ (P : ST), MoveHyp ST SG P → ∀ (q : 𝓞 E), q ∈ P.1.asIdeal → q ∉ P.1.asIdeal ^ 2 → ∀ (x : Sp E n), x ∈ d.N → d.f P x = 1 → d.N ≤ Formalism.HermitianLatticesTheory.dual (hStd E n) d.L ∧ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) d.L) = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.N ∧ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.up P q x).L = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal d.N ∧ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) (d.up P q x).L) = Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (Formalism.HermitianLatticesTheory.dual (hStd E n) d.L ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x}) ∧ ∀ y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (d.up P q x).N, (d.up P q x).f P y = d.f P (q • y) := by
  intro E _ _ _ n ST SG d hd P hP q hq hq2 x hx hfx
  exact ⟨hd.N_le_Lsh, localization_dual_L_eq_localization_N hd P hP, localization_up_L_eq_localization_N hd P hP hq hq2 hx hfx,
    localization_dual_up_L hd P hP hq hq2 hx hfx, fun y hy => by
      rw [Deco.up_f, if_pos (show y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal (upN P.1.asIdeal d.N x) from hy)]⟩

end GlobalTheory.MoveUpLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitIdempotentAtConjugatePrime
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
open GlobalTheory.Mem.R3.LiftBrg

namespace GlobalTheory.SplitEtaIdem

theorem exists_isIdemAt_conjP : ∀ {D : D7} (Pb : Formalism.L2.DIV.Pl D.host.E) (Ut : Formalism.L2.Col.MhlUnif Pb),
    ∃ e : Formalism.L2.Theta.AE D, Formalism.L2.NTheta.IsIdemAt e (Formalism.L2.Col.conjPrime₂ Pb) := by
  intro D Pb Ut
  apply GlobalTheory.MovedIdem.exists_isIdemAt
  rw [Formalism.L2.Col.conjIdeal_asIdeal, Formalism.L2.Col.conjPrime_conjPrime]
  intro h
  exact Ut.hπP (h ▸ Ut.hπ)

end GlobalTheory.SplitEtaIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitPlaceOfIsSplitPlaceCmField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.SplitPlaceOf

theorem exists_splitPlace : ∀ (D : D7) (P : PlE D.host), IsSplitPl D.host P →
    ∃ s : SplitPlace D.host.E, s.w = P :=
  fun D P hP => GlobalTheory.RowUnitProof.exists_splitPlace_eq D P hP

end GlobalTheory.HeightCounting.SplitPlaceOf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitFrame
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.MtIn
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MtIn

theorem isOrthF_one {D : D7} (V : HSp D) (h : V.gram = 1) : GlobalTheory.StdFrameExist.IsOrthF V 1 := by
  unfold GlobalTheory.StdFrameExist.IsOrthF GlobalTheory.StdFrameExist.gA
  rw [h, Matrix.map_one _ (map_zero _) (map_one _), Units.val_one, Formalism.UG.cT_one, Matrix.mul_one, Matrix.mul_one]

theorem intM_one {D : D7} (n : ℕ) : GlobalTheory.StdFrameExist.IntM (GlobalTheory.StdFrameExist.SI D) (1 : GL (Fin n) (Lev.EAf D)).1 := by
  intro i j
  rw [Units.val_one, Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem exists_unit_frame : ∀ (D : D7) (V : HSp D) (hF : D.host.F = maximalRealSubfield D.host.E), V.gram = 1 → Seed.FrmC.StdLat V → ∃ P : principalLevelFrame.RowPsi V V.rank, StdFrame hF P ∧ UnitFr P := by
  intro D V hF hg hV
  have h := isOrthF_one V hg
  refine ⟨GlobalTheory.StdFrameExist.rowPsi V 1 h, GlobalTheory.StdFrameExist.stdFrame_rowPsi hF hV h (intM_one _) ?_, fun κ => ?_⟩
  · rw [inv_one]; exact intM_one _
  · show finE V (GlobalTheory.StdFrameExist.psiF V 1 h κ) = _
    rw [GlobalTheory.StdFrameExist.finE_psiF, one_mul, inv_one, mul_one]
    rfl

end GlobalTheory.MtIn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedSpaceLeSupEigenspaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

end GlobalTheory.HeightCounting.FormsStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvMapMulMapMulCancelComplexEmbedding
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.Col2.TC.inv_map_mul_map_mul_cancel_complex_embedding {n : ℕ} {E : Type} [Field E] (f : E →+* ℂ) (γ : GL (Fin n) E) (M : Matrix (Fin n) (Fin n) ℂ) :
    ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).map f * ((γ : Matrix (Fin n) (Fin n) E).map f * M) = M := by
  rw [← Matrix.mul_assoc, ← Matrix.map_mul]
  simp

theorem GlobalTheory.Mem.Col2.TC.tr_eq_of_isTr : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∀ (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi), I.IdY l Z u a i hi eY → ∀ (b : (I.stp u a i).β) (g : (I.stp u a i).G b) (h : (I.chain l u a).Y i → ℂ) (s s' : (I.chain l u a).Y i), IsTr (atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) ((I.stp u a i).gam b g : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E)) (eY s') (eY s) → (I.stp u a i).tr B.fields.emb B.embLL b g h s = B.embLL (((I.stp u a i).chr b g : B.LLˣ) : B.LL) * h s' := by
  intro B X I _ _ l Z u a i hi eY hId b g h s s' hT
  have key : s' = frMul B.fields.emb B.embLL ((I.stp u a i).gam b g)⁻¹ s := by
    apply Subtype.ext
    funext τ
    have h1 : s.1 τ = Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (I.rec7 l Z))
        (((I.stp u a i).gam b g : GL (Fin (B.R.N i)) B.fields.E) : Matrix (Fin (B.R.N i)) (Fin (B.R.N i)) B.host.E) τ * s'.1 τ := by
      have := hT τ
      rw [hId, hId] at this
      exact this
    have hf : embAt B.embLL B.fields.emb τ = Formalism.L2.Forms.embT (I.rec7 l Z) τ := B.fields_embC τ
    show s'.1 τ = ((((I.stp u a i).gam b g)⁻¹ : GL _ _) : Matrix _ _ _).map (embAt B.embLL B.fields.emb τ) * s.1 τ
    rw [h1, hf]
    exact (GlobalTheory.Mem.Col2.TC.inv_map_mul_map_mul_cancel_complex_embedding _ _ _).symm
  show B.embLL _ * h (frMul B.fields.emb B.embLL ((I.stp u a i).gam b g)⁻¹ s) = _
  rw [← key]
end

