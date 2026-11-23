module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1100
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Formalism.LocalToGlobal.HermitianColumns.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1124
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFlagStabilizerNotLowerWeight
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact
open Formalism.UG (cT cT_mul cT_one)

namespace GlobalTheory.UAut.NoLower

theorem abstract_no_lower {A : Type} [CommRing A] {n r : ℕ} (st : Matrix (Fin n) (Fin n) A →+ Matrix (Fin n) (Fin n) A)
    (u : Fin r → Matrix (Fin n) (Fin n) A) (X Y : Matrix (Fin n) (Fin r) A) (L T : Matrix (Fin r) (Fin n) A)
    (hu : ∀ j, u j = X * single j j (1 : A) * L) (hs : ∀ j, st (u j) = Y * single j j (1 : A) * T)
    (hLX : L * X = 1) (hTX : T * X = 0) (hTY : T * Y = 1) (d : Fin r → ℕ) (M : ℕ) (hd : ∀ j, d j < M)
    (x : Matrix (Fin n) (Fin n) A) (B C : Matrix (Fin r) (Fin r) A) (hB : ∀ i j, d j < d i → B i j = 0)
    (hC : ∀ i j, d i < d j → C i j = 0) (eB : x * X = X * B) (eC : T * x = C * T) :
    ∀ a b, wt d M a < wt d M b → fam st u a * x * fam st u b = 0 := by
  have e0 : fam st u none = 1 - (X * L + Y * T) := by
    simp only [fam, Option.elim, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hs]
    simp only [hu, ← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
  have e1 : ∀ j, fam st u (some (.inl j)) = X * single j j (1 : A) * L := hu
  have e2 : ∀ j, fam st u (some (.inr j)) = Y * single j j (1 : A) * T := hs
  have k0 : fam st u none * X = 0 := by
    rw [e0, Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hLX, hTX]; simp
  have k1 : T * fam st u none = 0 := by
    rw [e0, Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hTY, hTX]; simp
  have l1 : ∀ (e : Matrix (Fin n) (Fin n) A) (j : Fin r), e * x * (X * single j j (1 : A) * L) =
      e * X * B * single j j (1 : A) * L := fun e j => by
    rw [Matrix.mul_assoc e X, ← eB]; simp only [Matrix.mul_assoc]
  have l2 : ∀ (e : Matrix (Fin n) (Fin n) A) (j : Fin r), (Y * single j j (1 : A) * T) * x * e =
      Y * single j j (1 : A) * C * (T * e) := fun e j => by
    rw [Matrix.mul_assoc _ T, eC]; simp only [Matrix.mul_assoc]
  have sm : ∀ (D : Matrix (Fin r) (Fin r) A) (i j : Fin r), D i j = 0 →
      single i i (1 : A) * D * single j j (1 : A) = 0 := fun D i j h => by
    rw [Matrix.single_mul_mul_single, h]; simp
  rintro (_ | i | i) (_ | j | j) hab
  · simp at hab
  · rw [e1, l1, k0]; simp
  · have := hd j; simp [wt] at hab; omega
  · have := hd i; simp [wt] at hab; omega
  · have h := sm B i j (hB i j (by simp [wt] at hab; omega))
    rw [e1, e1, l1, Matrix.mul_assoc _ L, hLX, Matrix.mul_one, Matrix.mul_assoc X, Matrix.mul_assoc X, h]; simp
  · have := hd i; have := hd j; simp [wt] at hab; omega
  · rw [e2, l2, k1]; simp
  · rw [e1, e2, l1, Matrix.mul_assoc _ T, hTX]; simp
  · have h := sm C i j (hC i j (by simp [wt] at hab; omega))
    rw [e2, e2, l2, ← Matrix.mul_assoc T, ← Matrix.mul_assoc T, hTY, Matrix.one_mul, ← Matrix.mul_assoc,
      Matrix.mul_assoc Y, Matrix.mul_assoc Y, h]; simp

theorem parFlag_no_lower : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ p ∈ parFlag σ J X d, ∀ a b, wt d M a < wt d M b → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J p).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0 := by
  intro F E _ _ _ _ _ σ hcm n J hJ r X Y d M hd hXX _ hXY p hp
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hcm
  have cc : ∀ {m q : Type} (A : Matrix m q E), cT (σ : E →+* E) (cT (σ : E →+* E) A) = A := fun A =>
    Matrix.ext fun i j => hσ _
  obtain ⟨⟨B, hB, eB⟩, B', hB', eB'⟩ := hp
  have eC := form_mul_of_mul_cols eB'
  rw [inv_inv] at eC
  have hLX : cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (cT (σ : E →+* E)) hXY
    rwa [cT_mul, cT_mul, cc, cT_form hJ, cT_one, ← Matrix.mul_assoc] at this
  refine abstract_no_lower _ _ (adMat F X) (adMat F Y) (adMat F (cT (σ : E →+* E) Y * J))
    (adMat F (cT (σ : E →+* E) X * J)) (fun j => idemA_eq _ _ j) (fun j => ?_) ?_ ?_ ?_ d M hd _ B _
    (fun i j h => hB h) (fun i j h => ?_) eB eC
  · have s : cT (σ : E →+* E) (single j j (1 : E) : Matrix (Fin r) (Fin r) E) = single j j 1 := by
      rw [cT, Matrix.map_single, Matrix.transpose_single, map_one]
    have e : J⁻¹ * cT (σ : E →+* E) (X * single j j (1 : E) * (cT (σ : E →+* E) Y * J)) * J =
        Y * single j j (1 : E) * (cT (σ : E →+* E) X * J) := by
      rw [cT_mul, cT_mul, cT_mul, cc, cT_form hJ, s, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_left _ _ (det_isUnit hJ)]
      simp only [Matrix.mul_assoc]
    rw [idemA, adjA_map, e]
    exact idemA_eq Y _ j
  · rw [adMat, adMat, ← Matrix.map_mul, hLX, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [adMat, adMat, ← Matrix.map_mul, hXX, Matrix.map_zero _ (map_zero _)]
  · rw [adMat, adMat, ← Matrix.map_mul, hXY, Matrix.map_one _ (map_zero _) (map_one _)]
  · show sigR (AF F) σ (B' j i) = 0
    rw [hB' h, map_zero]

end GlobalTheory.UAut.NoLower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KudlaSplittingSplitUnitary
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem kudlaSplittingSplitUnitary : GlobalTheory.Published.KudlaSplittingSplitUnitary := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α ν _ _ _ _ Q hQ ψ hψ hψ1 hψne χ hχ hres
  letI : MeasurableSpace (Matrix α ν E) := borel _
  haveI : BorelSpace (Matrix α ν E) := ⟨rfl⟩
  obtain ⟨-, -, -, -, -, -, -, hmat⟩ := _root_.GlobalTheory.quadExt_topology F E c δ hE
  obtain ⟨-, hG⟩ := hmat α ν
  haveI := hG.grp
  haveI := hG.t2
  haveI := hG.lc
  haveI := hG.sc
  obtain ⟨κ, ω, hKW⟩ := GlobalTheory.T.exists_weil_representation_split_unitary_schwartzBruhat F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres (Measure.addHaar)
  refine ⟨ω, GlobalTheory.T.splitUnitaryWeilRepresentation_isSmooth F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres _ κ ω hKW, ?_,
    GlobalTheory.T.weilRepresentation_intertwines_heisenberg F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres _ κ ω hKW, ?_⟩
  · intro μ' hμ' g φ
    exact GlobalTheory.T.weil_representation_preserves_L2_space F E c δ hE α ν Q hQ ψ hψ hψ1 hψne χ hχ hres _ κ ω hKW μ' g φ
  · intro a φ x
    have hp : levi c hE.invol a ∈ sieg c ν := by
      rw [mem_sieg, mat, levi_val, toBlocks_fromBlocks₂₁]
    rw [hKW.par _ hp φ]
    have h0 : ∀ y : Matrix α ν E, pr c Q y 0 = 0 := fun y => by
      simp [pr, form, GlobalTheory.WeilM.hTens]
    obtain ⟨-, -, hsc, -⟩ := GlobalTheory.T.unitaryCharacterAbsScalar_basic_properties F E c δ hE (Fintype.card α) χ hres
    have hd := hsc (Matrix.GeneralLinearGroup.det a)
    rw [Matrix.GeneralLinearGroup.val_det_apply] at hd
    simp only [parFun, mat, levi_val, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.mul_zero, h0,
      mul_zero, AddChar.map_zero_eq_one, one_mul, hd]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeArithVolumeOfFrequentlySmallSectionsLower
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr

theorem le_arVol_of_frequently_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (a : ℝ), (∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop, (L.pow N).smallSec.Finite ∧ (a / (D + 1).factorial - ε) * (N : ℝ) ^ (D + 1) ≤ Real.log ((L.pow N).smallSec.ncard : ℝ)) → (a : EReal) ≤ arVol L D := by
  intro k _ X _ p D L a h
  have hc : (0 : ℝ) < ((D + 1).factorial : ℝ) := by positivity
  have key : ∀ δ : ℝ, 0 < δ → ((a - δ : ℝ) : EReal) ≤ arVol L D := by
    intro δ hδ
    refine Filter.le_limsup_of_frequently_le ?_
    have hε : 0 < δ / ((D + 1).factorial : ℝ) := div_pos hδ hc
    refine ((h _ hε).and_eventually (eventually_gt_atTop 0)).mono ?_
    rintro N ⟨⟨hfin, hle⟩, hN⟩
    have h0 : 0 < (L.pow N).smallSec.ncard := (Set.ncard_pos hfin).2 ⟨_, (L.pow N).zero_mem_smallSec⟩
    rw [← hfin.cast_ncard_eq, ENat.toENNReal_coe, ← ENNReal.ofReal_natCast,
      ENNReal.log_ofReal_of_pos (by exact_mod_cast h0), ← EReal.coe_mul, EReal.coe_le_coe_iff]
    have hNp : (0 : ℝ) < (N : ℝ) ^ (D + 1) := by positivity
    rw [mul_div_assoc', le_div_iff₀ hNp]
    have e : (a / ((D + 1).factorial : ℝ) - δ / ((D + 1).factorial : ℝ)) * ((D + 1).factorial : ℝ) = a - δ := by
      field_simp
    calc (a - δ) * (N : ℝ) ^ (D + 1)
        = ((a / ((D + 1).factorial : ℝ) - δ / ((D + 1).factorial : ℝ)) * (N : ℝ) ^ (D + 1)) * ((D + 1).factorial : ℝ) := by
          rw [← e]; ring
      _ ≤ Real.log ((L.pow N).smallSec.ncard : ℝ) * ((D + 1).factorial : ℝ) :=
          mul_le_mul_of_nonneg_right hle hc.le
  refine le_of_forall_lt_imp_le_of_dense fun z hz => ?_
  induction z using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hz (not_lt.2 le_top)
  | coe r =>
    have hr : r < a := EReal.coe_lt_coe_iff.1 hz
    have := key (a - r) (by linarith)
    rwa [sub_sub_cancel] at this

end GlobalTheory.VolBr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupLiftExists
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

theorem isBaseFrame_of_isLatBasis {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (h : IsLatBasis V rfl β) :
    IsBaseFrame V β (GlobalTheory.Member.latC V) 1 := by
  refine ⟨fun x => ?_, Formalism.L2.Herm.coordinate_lattice_self_dual D.sp.cm V, Nat.one_pos, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨z, rfl⟩ := GlobalTheory.LiftLevel.swap_surj x
    refine Iff.trans ?_ (h z)
    rw [(GlobalTheory.Member.latHat_eq_hat_and_gram D V).1]
    exact (GlobalTheory.LevSplit.latHat_iff _ z).symm
  · rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq] at hx
    simpa using hx
  · rw [← GlobalTheory.Member.coe_selfDualLatticeInFrameCoordinates_eq]
    simpa using hx

theorem not_isConjPl_of_le {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : Level H)
    {w w' : Formalism.L2.DIV.Pl D.host.E} (hw : l.Mb ≤ w.asIdeal) (hw' : l.Mb ≤ w'.asIdeal) : ¬ IsConjPl w w' := by
  intro h
  apply w'.isPrime.ne_top
  rw [eq_top_iff, ← l.coprime]
  refine sup_le hw' (Ideal.map_le_iff_le_comap.2 fun a ha => ?_)
  obtain ⟨c', hc', e⟩ := h a (hw ha)
  have : H.bar a = c' := by
    apply RingOfIntegers.coe_injective
    exact (H.bar_eq a).trans e.symm
  show H.bar a ∈ w'.asIdeal
  rw [this]; exact hc'

theorem finR_rfl {D : D7} (V : HSp D) (κ : GA D V) : finR V rfl κ = finE V κ := by
  apply Units.ext
  ext i j
  rfl

end GlobalTheory.GeoLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviProjectionMaximalCompact
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviFubini

theorem levH_fst_entry {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ} (h : a + b = n) (w : Pl E)
    (p : parB h w) (i j : Fin a) :
    ((levH h w p).1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (GlobalTheory.SmGL.stdSum h (Sum.inl i)) (GlobalTheory.SmGL.stdSum h (Sum.inl j)) := rfl

theorem levH_snd_entry {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ} (h : a + b = n) (w : Pl E)
    (p : parB h w) (i j : Fin b) :
    ((levH h w p).2 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j =
      ((p : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E))
        (GlobalTheory.SmGL.stdSum h (Sum.inr i)) (GlobalTheory.SmGL.stdSum h (Sum.inr j)) := rfl

theorem levH_mem_KGL_of_mem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (p : GlobalTheory.LeviFubini.parB h w), (p : GLw n w) ∈ GlobalTheory.LFun.KGL w (n := n) →
      (GlobalTheory.LeviFubini.levH h w p).1 ∈ GlobalTheory.LFun.KGL w (n := a) ∧ (GlobalTheory.LeviFubini.levH h w p).2 ∈ GlobalTheory.LFun.KGL w (n := b) := by
  intro E _ _ _ a b n h w p hp
  have hp' := GlobalTheory.AdelicU.mem_GLint_iff.1 hp
  have hinv1 : ((levH h w p).1)⁻¹ = (levH h w p⁻¹).1 := by rw [map_inv, Prod.fst_inv]
  have hinv2 : ((levH h w p).2)⁻¹ = (levH h w p⁻¹).2 := by rw [map_inv, Prod.snd_inv]
  refine ⟨GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩,
    GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · rw [levH_fst_entry]; exact hp'.1 _ _
  · rw [hinv1, levH_fst_entry]; exact hp'.2 _ _
  · rw [levH_snd_entry]; exact hp'.1 _ _
  · rw [hinv2, levH_snd_entry]; exact hp'.2 _ _

end GlobalTheory.LeviFubini
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeL2InnerProduct
section
open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.ExpDeriv

open Filter Topology GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def expGL (X : Lie E a) (t : ℝ) : GL (Fin a) (Cinf E) :=
  (Matrix.isUnit_exp (t • Matrix.of X)).unit

theorem expGL_val (X : Lie E a) (t : ℝ) :
    ((expGL X t : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = NormedSpace.exp (t • Matrix.of X) := rfl

theorem expGL_zero (X : Lie E a) : expGL X 0 = 1 :=
  Units.ext (by rw [expGL_val, zero_smul, NormedSpace.exp_zero]; rfl)

theorem expGL_add (X : Lie E a) (s t : ℝ) : expGL X (s + t) = expGL X s * expGL X t := by
  apply Units.ext
  rw [Units.val_mul, expGL_val, expGL_val, expGL_val, add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl (Matrix.of X)).smul_left s).smul_right t)

theorem hasDerivAt_expGL (X : Lie E a) : HasDerivAt (fun t => toL (expGL X t).val) X 0 := by
  letI : NormedRing (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (LinearMap.id : Lie E a →ₗ[ℝ] Lie E a)
  have h := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (Matrix.of X) (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, mul_one] at h
  exact T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_along (X : Lie E a) (ψ : Sm E a) (g : GA E a) (t : ℝ) :
    HasDerivAt (fun s => ψ.1 (g * infGL E a (expGL X s)))
      ((lie E a X ψ).1 (g * infGL E a (expGL X t))) t := by
  have h := hasDerivAt_curve ψ (g * infGL E a (expGL X t)) (expGL X) X (expGL_zero X) (hasDerivAt_expGL X)
  have h2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h)
  have e : (fun s => ψ.1 (g * infGL E a (expGL X s))) =
      fun x => ψ.1 (g * infGL E a (expGL X t) * infGL E a (expGL X (x - t))) := by
    funext s
    rw [mul_assoc, ← map_mul, ← expGL_add, add_sub_cancel]
  rw [e]
  exact h2

end GlobalTheory.ExpDeriv

namespace GlobalTheory.ExpDeriv

open Filter Topology GlobalTheory.CuspRep

end GlobalTheory.ExpDeriv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLocalUnitsAlongNilpotentThickening
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

namespace GlobalTheory.FormalAlg

theorem lift_localUnits_of_thickening :
    ∀ (R : Type) [CommRing R] (J : Ideal R) (X X₀ : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (γ : X₀ ⟶ X) (q : X₀ ⟶ Spec (CommRingCat.of (R ⧸ J))), IsPullback γ q f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) → Surjective γ → ∀ (L : LB X), L.IsLB → ∀ D : X.Opens, IsAffineOpen D → ∀ u : ∀ m : L.ι, Γ(X₀, γ ⁻¹ᵁ (D ⊓ L.U m))ˣ, (∀ z m m', γ z ∈ D ⊓ L.U m → γ z ∈ D ⊓ L.U m' → gm (𝟙 X₀) z _ (u m) = gm γ z _ (L.g m m') * gm (𝟙 X₀) z _ (u m')) → ∃ τ : ∀ m : L.ι, Γ(X, D ⊓ L.U m)ˣ, (∀ m, (γ.app (D ⊓ L.U m)).hom (τ m).val = (u m).val) ∧ ∀ x m m', x ∈ D ⊓ L.U m → x ∈ D ⊓ L.U m' → gm (𝟙 X) x _ (τ m) = gm (𝟙 X) x _ (L.g m m') * gm (𝟙 X) x _ (τ m') := by
  intro R _ J X X₀ f γ q hpb hsurj L hL D hD u hu
  have hLp := LB.isLB_pull hL γ
  let O : L.ι → X₀.Opens := fun m => γ ⁻¹ᵁ (D ⊓ L.U m)
  have hO : ∀ m, O m ≤ γ ⁻¹ᵁ D := fun m => γ.preimage_mono inf_le_left
  have hc : γ ⁻¹ᵁ D ≤ ⨆ m, O m := by
    intro z hz
    obtain ⟨m, hm⟩ := exists_chart hL (γ z)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨m, show γ z ∈ D ⊓ L.U m from ⟨hz, hm⟩⟩
  have hU : ∀ m, O m ≤ (L.pull γ).U (fun _ => m) := fun m z hz => mem_pull.2 hz.2

  have hg : ∀ z a b, γ z ∈ L.U a → γ z ∈ L.U b →
      gm (𝟙 X₀) z ((L.pull γ).U (fun _ => a) ⊓ (L.pull γ).U (fun _ => b))
        ((L.pull γ).g (fun _ => a) (fun _ => b)) = gm γ z _ (L.g a b) := by
    intro z a b ha hb
    have hp : (𝟙 X₀) z ∈ (L.pull γ).U (fun _ => a) ⊓ (L.pull γ).U (fun _ => b) :=
      ⟨mem_pull.2 ha, mem_pull.2 hb⟩
    show gm (𝟙 X₀) z _ (∏ _k : PUnit, (res _ (pullU γ _ (L.g a b))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    refine (gm_res (𝟙 X₀) z _ hp _).trans ((gm_pull (𝟙 X₀) γ z (L.U a ⊓ L.U b) ⟨ha, hb⟩ _).trans ?_)
    rw [Category.id_comp]
  have hcomp : ∀ a b, rs X₀ (inf_le_left : O a ⊓ O b ≤ O a) (u a).val =
      rs X₀ (inf_le_inf (hU a) (hU b)) ((L.pull γ).g (fun _ => a) (fun _ => b)).val *
        rs X₀ (inf_le_right : O a ⊓ O b ≤ O b) (u b).val := by
    intro a b
    have e : res (inf_le_left : O a ⊓ O b ≤ O a) (u a) =
        res (inf_le_inf (hU a) (hU b)) ((L.pull γ).g (fun _ => a) (fun _ => b)) *
          res (inf_le_right : O a ⊓ O b ≤ O b) (u b) := by
      apply unit_ext
      intro z hz
      have hz' : (𝟙 X₀) z ∈ O a ⊓ O b := hz
      rw [map_mul, gm_res _ z _ hz', gm_res _ z _ hz', gm_res _ z _ hz',
        hg z a b hz.1.2 hz.2.2]
      exact hu z a b hz.1 hz.2
    have e' := congrArg Units.val e
    simp only [Units.val_mul, GlobalTheory.LB.val_res] at e'
    exact e'
  obtain ⟨t, ht, -⟩ := SecOn.existsUnique_of_local hLp O hO hc (fun m _ => m) hU
    (fun m => (u m).val) hcomp
  obtain ⟨s, hs⟩ := secOn_pull_surjective_of_surjective R (R ⧸ J) (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective X X₀ f q γ hpb L hL D hD t
  have hcoord : ∀ m, (γ.app (D ⊓ L.U m)).hom (GlobalTheory.LB.coord s m) = (u m).val := by
    intro m
    have e := ht m
    rw [← hs] at e
    erw [SecOn.coord_pull γ s (fun _ => m), GlobalTheory.LB.resG_appLE] at e
    rw [Scheme.Hom.app_eq_appLE]
    exact e
  have hunit : ∀ m, IsUnit (GlobalTheory.LB.coord s m) := by
    intro m
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hx
    obtain ⟨z, rfl⟩ := γ.surjective x
    apply isUnit_of_map_unit (γ.stalkMap z).hom
    erw [Scheme.Hom.germ_stalkMap_apply γ (D ⊓ L.U m) z hx, hcoord m]
    exact (u m).isUnit.map _
  refine ⟨fun m => (hunit m).unit, fun m => hcoord m, ?_⟩
  intro x m m' hx hx'
  have hi : D ⊓ L.U m ⊓ L.U m' ≤ D ⊓ L.U m := inf_le_left
  have hj : D ⊓ L.U m ⊓ L.U m' ≤ D ⊓ L.U m' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hij : D ⊓ L.U m ⊓ L.U m' ≤ L.U m ⊓ L.U m' :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have e : res hi (hunit m).unit = res hij (L.g m m') * res hj (hunit m').unit := by
    apply Units.ext
    simp only [Units.val_mul, GlobalTheory.LB.val_res, IsUnit.unit_spec]
    exact SecOn.compat s m m' hi hj hij
  have hxx : (𝟙 X) x ∈ D ⊓ L.U m ⊓ L.U m' := ⟨hx, hx'.2⟩
  have e' := congrArg (gm (𝟙 X) x _) e
  rw [map_mul, gm_res _ x _ hxx, gm_res _ x _ hxx, gm_res _ x _ hxx] at e'
  exact e'

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIntersectionNumberAmpleConsNefNonneg
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem interNum_cons_ample_nef_nonneg :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → (∀ (E : X.Modules) [IsFiniteQC E], suppDim E ≤ (d : ℕ) → ∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k E P) → ∀ A : LB X, IsAmpleLB A → (∀ P : Fin d → LB X, (∀ i, IsNef k (P i)) → 0 ≤ interNum k (GlobalTheory.structureModule X) (Fin.cons A P : Fin (d + 1) → LB X)) := by
  intro k _ _ X _ hp d hd H A hA P hP
  have hf := algebraMap_eq_strHom k X
  have := isNoetherian_of_isProjOver hp
  have hPb : ∀ i, (P i).IsLB := fun i => (hP i).isLB
  have hsd : suppDim (GlobalTheory.structureModule X) ≤ (d + 1 : ℕ) := by
    rw [suppDim_structureModule]; exact hd
  have hfin := finiteCohTwists_of_isProjOver hf (GlobalTheory.structureModule X) hp
  have hv := diffVanish_chiPic_of_isProjOver hf (GlobalTheory.structureModule X) hp hsd
  obtain ⟨a, ha, s, hs, -⟩ := hA.exists_mono_cutHom (GlobalTheory.structureModule X)
  have hLa := isLB_lbPow hA.isLB a
  have h0 := H _ (suppDim_cut_le _ hLa s hsd) P hP
  rw [← interNum_cons_eq_interNum_cut hLa s hPb hfin] at h0
  have h := hv.interNum_update_of_cls_eq_zsmul (by simp) (isLB_cons hA.isLB hPb) (0 : Fin (d + 1))
    hLa hA.isLB (a : ℤ) (cls_lbZPow hA.isLB a _)
  simp only [Fin.update_cons_zero] at h
  rw [h] at h0
  exact nonneg_of_mul_nonneg_right h0 (by exact_mod_cast ha)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTestFactorNeZeroOfGlobalProductNeZeroStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localTestFactor_ne_zero_of_globalProduct_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ), IsTest (KL n) K' f → ∀ y : finU (E := E) (n := n), (∀ᶠ w in cofinite, cLoc w y.1 ∈ GlobalTheory.LFun.KGL w (n := n)) → globFn S f y ≠ 0 → ∀ w ∈ S, f w (toSub _ (cLoc w y.1)) ≠ 0 := by
  first | exact @GlobalTheory.BCT.SuppFin.factor_ne_zero_of_globFn_ne_zero | exact GlobalTheory.BCT.SuppFin.factor_ne_zero_of_globFn_ne_zero | (intros; apply GlobalTheory.BCT.SuppFin.factor_ne_zero_of_globFn_ne_zero <;> assumption)
end

