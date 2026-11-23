module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitQuotientTopology.IsClosedRStab
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0236
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0245
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0241
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinates
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentMiddleRowMemHomLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LiftRowMiddleSpaceIntegralPoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeMiddleLatticeHomLatticeIdeal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0242
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLimitOfChart
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0154
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0303
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0302

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralUnipotentRadicalRealPoints
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

theorem cM_one (k r : ℕ) (β : Bk r) : cM k r β (Matrix.of.symm 1) = 0 := by
  rcases β with p | a | p | a
  · show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r p.1.1) (eI k r p.1.2) = 0
    exact Matrix.one_apply_ne (fun h => p.2.ne (by simpa [eI, Fin.ext_iff] using h))
  · funext j
    show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r a) (wI k r j) = 0
    refine Matrix.one_apply_ne (fun h => ?_)
    have h' := congrArg Fin.val h
    simp only [eI, wI] at h'
    have := a.isLt
    omega
  · show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r p.1.1) (esI k r p.1.2) = 0
    refine Matrix.one_apply_ne (fun h => ?_)
    have h' := congrArg Fin.val h
    simp only [eI, esI] at h'
    have := p.1.1.isLt
    have := p.1.2.isLt
    omega
  · show ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (eI k r a) (esI k r a)).im = 0
    rw [Matrix.one_apply]
    split_ifs <;> simp

theorem pos_le (k r : ℕ) (i : Fin (2 * r + k + 1)) : pos k r i ≤ 2 * r := by
  have := i.isLt
  unfold pos
  split_ifs <;> omega

theorem eq_one_of_dep {k r : ℕ} {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (h : Dep k r (2 * r + 1) (x - 1)) : x = 1 := by
  refine sub_eq_zero.1 (Matrix.ext fun i j => ?_)
  exact h i j (by have := pos_le k r j; omega)

theorem countable_units (E : Type) [Field E] [NumberField E] (n : ℕ) :
    Countable (Matrix (Fin n) (Fin n) E)ˣ := by
  haveI : Countable E :=
    Function.Injective.countable (Module.finBasis ℚ E).equivFun.injective
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Function.Injective.countable (f := fun u : (Matrix (Fin n) (Fin n) E)ˣ => (u : Matrix (Fin n) (Fin n) E))
    Units.val_injective

theorem ofReal_five (t u h c g : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) (hh : 0 ≤ h) (hc : 0 ≤ c) (hg : 0 ≤ g) :
    ENNReal.ofReal (t * (u * h * c * g)) =
      ENNReal.ofReal t * (ENNReal.ofReal u * ENNReal.ofReal h * ENNReal.ofReal c * ENNReal.ofReal g) := by
  rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul hu]

abbrev MM (k r : ℕ) (E : Type) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E

theorem covolume_N : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → IsHermND σ J → GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ → IsFrame (σ : E →+* E) J (algebraMap F E T) P → IsDual (σ : E →+* E) J P f → tupLat (id1 E r) (sideM P f) ≤ Λ → IsModelAt J A → (∀ a, 0 < s a) → Adapted A P f s → AllSome (IsDomN (σ : E →+* E) J Λ P A) fun 𝓓 => Measure.pi (fun _ : InfinitePlace E => haarLie (Nset k r) 1) 𝓓 = ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (-(((k : ℝ) + 1) * (r : ℝ) ^ 2) - 4 * ((r : ℝ) ^ 3 - r) / 3 - 3 * (r : ℝ) / 2) * (∏ a : Fin r, s a ^ (4 * (r - (a : ℕ)) + 2 * k)) ^ Fintype.card (InfinitePlace E)) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hV : IsVolData σ J Λ P f T A s := ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  obtain ⟨⟨G, hG⟩, hGu⟩ := _root_.GlobalTheory.SnMass.VolN.gN_subgroup F E σ k r J Λ P f T A s hV
  obtain ⟨ha1, ha2, ha3⟩ := _root_.GlobalTheory.SnMass.VolN.actLaws F E σ k r J Λ P f T A s hV
  have hmem := _root_.GlobalTheory.SnMass.VolN.gM_mem_Nset F E σ k r J Λ P f T A s hV
  choose DU hDUm hDUf hDUv using fun p : UTr r =>
    _root_.GlobalTheory.SnMass.VolN.hasDom_ideLat_dInv_div F E σ h1 h2 (r - p.1.1.val) (r - p.1.2.val) (s p.1.1 / s p.1.2) (div_pos (h9 _) (h9 _))
  choose DC hDCm hDCf hDCv using fun p : UTr r =>
    _root_.GlobalTheory.SnMass.VolN.CovMul.hasDom_ideLat_dInv_mul F E σ h1 h2 (r - p.1.1.val) (r - p.1.2.val) (s p.1.1 * s p.1.2) (mul_pos (h9 _) (h9 _))
  choose DH hDHm hDHf hDHv using _root_.GlobalTheory.SnMass.VolN.CovH.covolume_homLat F E σ k r J Λ P f T A s hV
  choose DG hDGm hDGf hDGv using fun a : Fin r =>
    _root_.GlobalTheory.SnMass.SkewVol.skew_covol_dInv F E σ h1 h2 (r - a.val) (s a ^ 2) (pow_pos (h9 _) 2)
  let LB := blkSet (InfinitePlace E) k r
    (fun p => (ideLat (dInv E (r - p.1.1.val) * (dInv E (r - p.1.2.val))⁻¹) (s p.1.1 / s p.1.2) : Set _))
    (fun a => homLat (σ : E →+* E) J Λ P f A (dInv E (r - a.val)) (s a))
    (fun p => (ideLat (dInv E (r - p.1.1.val) * dInv E (r - p.1.2.val)) (s p.1.1 * s p.1.2) : Set _))
    (fun a => (skewLat (σ : E →+* E) (dInv E (2 * (r - a.val))) (s a ^ 2) : Set _))
  let DB := blkSet (InfinitePlace E) k r DU DH DC DG
  let NN : Set (InfinitePlace E → Mt k r) := {x | ∀ w, Matrix.of (x w) ∈ Nset k r}
  let ρ : G → (InfinitePlace E → Mt k r) → (InfinitePlace E → Mt k r) :=
    fun g => actM A ((g : (MM k r E)ˣ) : MM k r E)
  let o : InfinitePlace E → Mt k r := fun _ => Matrix.of.symm 1
  let gm : G → InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    fun g => gM A ((g : (MM k r E)ˣ) : MM k r E)
  have hρo : ∀ g w, ρ g o w = Matrix.of.symm (gm g w) := fun g w => by
    show Matrix.of.symm (gm g w * 1) = Matrix.of.symm (gm g w)
    rw [mul_one]
  have hgm : ∀ g w, gm g w ∈ Nset k r := fun g => hmem _ ((hG _).1 g.2)
  have hρ1 : ∀ x, ρ 1 x = x := fun x => by
    have e : (((1 : G) : (MM k r E)ˣ) : MM k r E) = 1 := rfl
    show actM A (((1 : G) : (MM k r E)ˣ) : MM k r E) x = x
    rw [e]; exact ha1 x
  have hρm : ∀ g h x, ρ (g * h) x = ρ g (ρ h x) := fun g h x => by
    have e : (((g * h : G) : (MM k r E)ˣ) : MM k r E) = ((g : (MM k r E)ˣ) : MM k r E) * ((h : (MM k r E)ˣ) : MM k r E) := rfl
    show actM A (((g * h : G) : (MM k r E)ˣ) : MM k r E) x = _
    rw [e]; exact ha2 _ _ x
  have hρN : ∀ g, ∀ x ∈ NN, ρ g x ∈ NN := fun g x hx w =>
    PI.AmpOrbQuot.nset_mul (hgm g w) (hx w)
  have hdep : ∀ (g : G) (d : ℕ), (∀ β : Bk r, degB r β < d →
      (fun w => cM k r β (ρ g o w)) = 0) → ∀ w, Dep k r d (gm g w - 1) := fun g d hg w =>
    GlobalTheory.T.hasFlagDepthAtLeast_of_free_entries_vanish k r _ d (hgm g w) fun β hβ => by
      have := congrFun (hg β hβ) w
      rwa [hρo] at this
  have tw := _root_.GlobalTheory.SnMass.VolN.existsUnique_layered_fundamentalDomain (V := fun β : Bk r => InfinitePlace E → VM k r β) ρ NN o (degB r)
    (fun β x w => cM k r β (x w)) LB DB (fun w => by
      change Matrix.of (Matrix.of.symm 1) ∈ Nset k r
      rw [Equiv.apply_symm_apply]
      exact PI.AmpOrbQuot.nset_one) hρ1 hρm hρN
    (by
      rintro (p | a | p | a)
      · exact (ideLat _ _).zero_mem
      · exact ⟨0, ⟨fun a => by simp [form], fun c _ => by simp⟩, fun w l => by
          have e : (fun i => w.embedding ((0 : Fin (2 * r + k + 1) → E) i)) = 0 := by ext; simp
          rw [e, Matrix.mulVec_zero]
          simp [herm]
          rfl⟩
      · exact (ideLat _ _).zero_mem
      · exact (skewLat _ _ _).zero_mem)
    (by
      rintro (p | a | p | a) v
      · exact hDUf p v
      · exact hDHf a v
      · exact hDCf p v
      · exact hDGf a v)
    (fun β => funext fun w => cM_one k r β)
    (fun d g hg x hx β hβ => funext fun w => by
      have := _root_.GlobalTheory.SnMass.VolN.cM_mul_of_dep k r (gm g w) (Matrix.of (x w)) d (hdep g d hg w) (_root_.GlobalTheory.SnMass.VolN.DepOne.dep_one k r _ (hx w)) β hβ
      show cM k r β (ρ g x w) = cM k r β (x w) + cM k r β (ρ g o w)
      rw [hρo]
      exact this)
    (by
      intro g β hβ
      have hgN := (hG _).1 g.2
      have e : (fun w => cM k r β (ρ g o w)) = fun w => cM k r β (Matrix.of.symm (gm g w)) :=
        funext fun w => by rw [hρo]
      show (fun w => cM k r β (ρ g o w)) ∈ LB β
      rw [e]
      rcases β with p | a | p | a
      · exact _root_.GlobalTheory.SnMass.VolN.gM_entry_mem_ideLat F E σ k r J Λ P f T A s hV _ hgN p
      · exact _root_.GlobalTheory.SnMass.VolN.row_mem_homLat F E σ k r J Λ P f T A s hV _ hgN a
      · exact _root_.GlobalTheory.SnMass.VolN.corner_entry_mem_ideLat F E σ k r J Λ P f T A s hV _ hgN p
      · exact GlobalTheory.T.integralUnipotent_antidiagonal_mem_skewLattice F E σ k r J Λ P f T A s hV _ hgN a fun w =>
          GlobalTheory.T.re_antidiagonal_entry_eq_zero_of_flagDepth k r _ a (hgm g w) (hdep g _ hβ w))
    (by
      have lift : ∀ (β : Bk r) (l : InfinitePlace E → VM k r β),
          (∃ γ ∈ GN (σ : E →+* E) J Λ P, (∀ w, cM k r β (Matrix.of.symm (gM A γ w)) = l w) ∧
            ∀ β' : Bk r, β' ≠ β → degB r β' ≤ degB r β → ∀ w, cM k r β' (Matrix.of.symm (gM A γ w)) = 0) →
          ∃ g : G, (fun w => cM k r β (ρ g o w)) = l ∧ ∀ β', β' ≠ β → degB r β' ≤ degB r β →
            (fun w => cM k r β' (ρ g o w)) = 0 := by
        rintro β l ⟨γ, hγ, hl, h0⟩
        obtain ⟨u, rfl⟩ := hGu γ hγ
        refine ⟨⟨u, (hG u).2 hγ⟩, funext fun w => ?_, fun β' h h' => funext fun w => ?_⟩
        · rw [hρo]; exact hl w
        · rw [hρo]; exact h0 β' h h' w
      rintro (p | a | p | a) l hl
      · exact lift _ _ (_root_.GlobalTheory.SnMass.VolN.LiftEntry.lift_entry F E σ k r J Λ P f T A s hV p l hl)
      · exact lift _ _ (_root_.GlobalTheory.SnMass.VolN.RowLift.lift_row F E σ k r J Λ P f T A s hV a l hl)
      · exact lift _ _ (_root_.GlobalTheory.SnMass.VolN.LiftCorner.lift_corner F E σ k r J Λ P f T A s hV p l hl)
      · exact lift _ _ (_root_.GlobalTheory.SnMass.VolN.exists_lift_antidiag F E σ k r J Λ P f T A s hV a l hl))
    (fun g hg => by
      have h1' : ∀ w, gm g w = 1 := fun w => eq_one_of_dep (hdep g _ (fun β _ => hg β) w)
      exact Subtype.ext (Units.ext (ha3 _ h1')))
  obtain ⟨hNm, hN0⟩ := _root_.GlobalTheory.SnMass.VolN.pi_nset_full (InfinitePlace E) k r
  obtain ⟨hDm, hDv⟩ := _root_.GlobalTheory.SnMass.VolN.BlockMeas.measure_blocks (InfinitePlace E) k r DU DH DC DG hDUm hDHm hDCm hDGm
  set Dset : Set (InfinitePlace E → Mt k r) := {x | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧
    ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet (InfinitePlace E) k r DU DH DC DG β} with hDset
  have hstrict : ∀ x ∈ NN, ∃! g : G, ρ g x ∈ Dset := fun x hx => by
    obtain ⟨g, hg, hu⟩ := tw x hx
    exact ⟨g, ⟨hρN g x hx, hg⟩, fun g' hg' => hu g' hg'.2⟩
  have conv : ∀ S : Set (InfinitePlace E → Mt k r), (∀ x ∈ NN, ∃! g : G, ρ g x ∈ S) ↔
      ∀ x ∈ NN, ∃! γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E,
        (InN (σ : E →+* E) J P γ ∧ latMap γ Λ = Λ) ∧ actM A γ x ∈ S := fun S => by
    refine forall₂_congr fun x hx => ?_
    constructor
    · rintro ⟨g, hg, hu⟩
      refine ⟨_, ⟨(hG _).1 g.2, hg⟩, fun γ hγ => ?_⟩
      obtain ⟨u, rfl⟩ := hGu γ hγ.1
      exact congrArg (fun g : G => ((g : (MM k r E)ˣ) : MM k r E)) (hu ⟨u, (hG u).2 hγ.1⟩ hγ.2)
    · rintro ⟨γ, hγ, hu⟩
      obtain ⟨u, rfl⟩ := hGu γ hγ.1
      refine ⟨⟨u, (hG u).2 hγ.1⟩, hγ.2, fun g hg => ?_⟩
      exact Subtype.ext (Units.ext (hu _ ⟨(hG _).1 g.2, hg⟩))
  haveI : Countable G := by
    haveI := countable_units E (2 * r + k + 1)
    infer_instance
  refine ⟨⟨Dset, hDm, (conv Dset).1 hstrict⟩, fun 𝓓 h𝓓 => ?_⟩
  have hEq := GlobalTheory.T.strictFundamentalDomain_measure_eq (G := G) _ ρ NN 𝓓 Dset hNm hN0 h𝓓.1 hDm hρ1 hρm hρN
    (fun g => GlobalTheory.T.unipotentModelProductAction_measurePreserving E k r A _ (hgm g)) ((conv 𝓓).2 h𝓓.2) hstrict
  beta_reduce
  rw [hEq, hDv]
  simp only [hDUv, hDHv, hDCv, hDGv]
  have hd : 0 < |(NumberField.discr F : ℝ)| := abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero F)
  rw [← _root_.GlobalTheory.SnMass.VolN.covol_blocks_prod _ (Fintype.card (InfinitePlace E)) k r s hd h9]
  have nnU : ∀ p : UTr r, 0 ≤ (2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) + 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 / s p.1.2) ^ (2 * Fintype.card (InfinitePlace E)) := fun p => by
    have := h9 p.1.1; have := h9 p.1.2; positivity
  have nnC : ∀ p : UTr r, 0 ≤ (2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - p.1.1.val : ℕ) : ℝ) - 2 * ((r - p.1.2.val : ℕ) : ℝ)) * (s p.1.1 * s p.1.2) ^ (2 * Fintype.card (InfinitePlace E)) := fun p => by
    have := h9 p.1.1; have := h9 p.1.2; positivity
  have nnH : ∀ a : Fin r, 0 ≤ ((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) * s a ^ (2 * Fintype.card (InfinitePlace E))) ^ (k + 1) := fun a => by
    have := h9 a; positivity
  have nnG : ∀ a : Fin r, 0 ≤ |(NumberField.discr F : ℝ)| ^ (1 / 2 - 2 * ((r - a.val : ℕ) : ℝ)) * (s a ^ 2) ^ Fintype.card (InfinitePlace E) := fun a => by
    have := h9 a; positivity
  rw [← ENNReal.ofReal_prod_of_nonneg fun p _ => nnU p, ← ENNReal.ofReal_prod_of_nonneg fun a _ => nnH a,
    ← ENNReal.ofReal_prod_of_nonneg fun p _ => nnC p, ← ENNReal.ofReal_prod_of_nonneg fun a _ => nnG a,
    ofReal_five _ _ _ _ _ (by positivity) (Finset.prod_nonneg fun p _ => nnU p) (Finset.prod_nonneg fun a _ => nnH a)
      (Finset.prod_nonneg fun p _ => nnC p) (Finset.prod_nonneg fun a _ => nnG a),
    ENNReal.ofReal_pow (by norm_num)]
  simp

end GlobalTheory.SnMass.VolN
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DeepRegionKernelDiagonalBound
section
open MeasureTheory NumberField Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.DeepRegion

theorem one_le_f (I : AutInst) : 1 ≤ I.f := by
  show 0 < Module.finrank ℚ I.F
  exact Module.finrank_pos

theorem one_le_rd (I : AutInst) : 1 ≤ I.rd := by
  have hd : (1 : ℝ) ≤ |(discr I.E : ℝ)| := by
    have h0 : discr I.E ≠ 0 := discr_ne_zero I.E
    have : (1 : ℤ) ≤ |discr I.E| := Int.one_le_abs h0
    exact_mod_cast this
  exact Real.one_le_rpow hd (by positivity)

theorem deepBound (hV : GlobalTheory.FlagMeas.AbsoluteVolume) (hK : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.DeepKernelBound) :
    GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.DeepBound := by
  intro Cg hCg
  refine ⟨8, ?_⟩
  intro B d p q b hq hH
  obtain ⟨hDS, hSig, hn0, hqn, hrd, hf, hb, hbb, hlam, hg1, hgb, hg0p, hg0, hsplit, hgap⟩ := id hH
  have hgc : ∀ v, ∃ c : ℝ, 0 < c ∧ IsGauge (B.I.ε v) c := fun v => by
    obtain ⟨c, hc, hc', -⟩ := GlobalTheory.GaugeConst.exists_unique_isGauge B.I.n (B.I.ε v)
    exact ⟨c, hc, hc'⟩
  choose c hc0 hc using hgc
  have hn8 : 8 ≤ B.I.n := hn0
  have hf1 : 1 ≤ B.I.f := one_le_f B.I
  have hrd1 : 1 ≤ B.I.rd := one_le_rd B.I
  have hnR : (8 : ℝ) ≤ B.I.n := by exact_mod_cast hn8
  have hfR : (1 : ℝ) ≤ B.I.f := by exact_mod_cast hf1
  have hgR : (1 : ℝ) ≤ B.g := by exact_mod_cast hg1
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b := ⟨_, rfl⟩
  have a1 : (8 : ℝ) ≤ B.I.n * B.I.f := by nlinarith
  have a2 : (8 : ℝ) ≤ B.I.n * B.I.f * B.g := by nlinarith
  have a3 : (16 : ℝ) ≤ B.I.n * B.I.f * B.g * b := by nlinarith
  have hXe : X = B.I.rd * (B.I.n * B.I.f * B.g * b) := by rw [hX]; ring
  have hX16 : 16 ≤ X := by rw [hXe]; nlinarith
  have hXrd : B.I.rd ≤ X := by rw [hXe]; nlinarith
  have hXf : 2 * B.I.f * B.I.rd ≤ X := by
    have : 2 * (B.I.f : ℝ) ≤ B.I.n * B.I.f * B.g * b := by nlinarith
    rw [hXe]; nlinarith
  have hXsq : 2 * B.I.f * B.I.rd ≤ X ^ 2 := by nlinarith
  have hVol := hV B.I p q (by first | exact hSig | exact fun v => hSig v) hqn hn8 X (by linarith) hXrd hXsq
    c B.μf (by first | exact hc | exact fun v => ⟨hc0 v, hc v⟩ | exact fun v => ⟨hc v, hc0 v⟩)
  obtain ⟨hKs, hKg0, hKsT⟩ := GlobalTheory.CongIndex.measure_Kset_le B.I B.μf B.g hg1
  obtain ⟨hcov, -⟩ := _root_.GlobalTheory.CovolRat.covol_eq_inter_fund B.I B.μf B.fund Set.univ B.fund_spec MeasurableSet.univ
    (fun _ _ _ _ => trivial)
  rw [Set.univ_inter] at hcov
  change ENNReal.ofReal (∏ v, c v) * _ / B.μf B.I.Kset ≤ _ at hVol
  rw [hcov] at hVol
  set N : ℕ := B.I.n ^ 2 * B.I.f with hN
  set P : ℝ := ∏ v, c v with hP
  have hP0 : 0 < P := Finset.prod_pos fun v _ => hc0 v
  have hKgT : B.μf (B.I.Kg B.g) ≠ ⊤ :=
    ne_top_of_le_ne_top hKsT.ne (measure_mono fun x hx => hx.1)
  set kR : ℝ := (B.μf (B.I.Kg B.g)).toReal with hkR
  have hkR0 : 0 < kR := ENNReal.toReal_pos hKg0.ne' hKgT
  have hX0 : 0 < X := by linarith
  have hg0' : (0 : ℝ) < B.g := by linarith
  have hm0 : B.μf B.I.Kset ≠ 0 := (lt_of_lt_of_le hKg0 (measure_mono fun x hx => hx.1)).ne'

  have hF : B.I.muA B.μf B.fund ≤ ENNReal.ofReal (X ^ N * (B.g : ℝ) ^ (2 * N) * kR / P) := by
    have h1 : ENNReal.ofReal P * B.I.muA B.μf B.fund ≤ ENNReal.ofReal (X ^ N) * B.μf B.I.Kset :=
      (ENNReal.div_le_iff hm0 hKsT.ne).1 hVol
    have h2 : B.μf B.I.Kset ≤ ENNReal.ofReal ((B.g : ℝ) ^ (2 * N) * kR) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hKgT, ENNReal.ofReal_pow hg0'.le,
        ENNReal.ofReal_natCast]
      exact hKs
    have h3 : ENNReal.ofReal P * B.I.muA B.μf B.fund ≤
        ENNReal.ofReal (X ^ N * ((B.g : ℝ) ^ (2 * N) * kR)) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      exact h1.trans (by gcongr)
    rw [ENNReal.ofReal_div_of_pos hP0, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hP0))
      (Or.inl ENNReal.ofReal_ne_top), mul_comm, ← mul_assoc]
    simpa [mul_assoc] using h3

  set Kc : ℝ := Real.exp (-(N : ℝ)) / ((B.g : ℝ) ^ (2 * N) * X ^ N) * B.D * P / kR with hKc
  have hpt : ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b,
      ENNReal.ofReal (kern B.I (phe B d) x x).re ≤ ENNReal.ofReal Kc := by
    intro x hx
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet, Set.mem_setOf_eq] at hx
    apply ENNReal.ofReal_le_ofReal
    have hτ0 : 0 < least B.I x :=
      ((_root_.GlobalTheory.CountSteps.steps B.I x 1 one_pos).2.2.2.2.2.2.2.2 (by omega)).1
    have hτle : least B.I x ≤ ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b)⁻¹ ^ (11 * q) := hx.2.le
    have hk := hK Cg 8 B d p q b c x hCg le_rfl hq hH hc hx.2
    have he := (GlobalTheory.deep_region_exponents B.I.n B.I.f q B.I.rd B.g b (least B.I x) hn8 hf1 hq hqn
      hrd1 hb hgR hτ0 hτle).2
    have hN' : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.dimN B = N := rfl
    have hst : GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe B.I.n b (8 * q * N + N) =
        √(B.I.n : ℝ) * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.stepBe
      have : (B.I.n : ℝ) ^ ((3 : ℝ) / 2) = B.I.n * √(B.I.n : ℝ) := by
        rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num,
          Real.rpow_add (by positivity), Real.rpow_one]
      rw [this]; push_cast; ring
    rw [hN', hst] at hk
    rw [hX] at hKc
    have hA : ((2 * GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh B q (least B.I x) * √(B.I.f : ℝ) *
          (√(B.I.n : ℝ) * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) + 3 * ((8 * q * N + N : ℕ) : ℝ))) ^
            (16 * q * N) *
          (6 * (√(B.I.n : ℝ) * b ^ 2 + 1.5 * (B.I.n : ℝ) ^ ((3 : ℝ) / 2) +
            3 * ((8 * q * N + N : ℕ) : ℝ))) ^ N *
          Real.exp B.I.f * (17 * √(B.I.n : ℝ) / least B.I x ^ 2) ^ (2 * N)) *
          ((B.g : ℝ) ^ (2 * N) * ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b) ^ N) ≤
          Real.exp (-(N : ℝ)) := by
      rw [show 16 * q * N = 2 * (8 * q * N) by ring]
      refine le_of_eq_of_le ?_ he
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.DeepKernelRadiusBound.radRh]
      ring
    have hD : (0 : ℝ) ≤ B.D := Nat.cast_nonneg _
    refine hk.trans ?_
    rw [hKc]
    have hpos : 0 < (B.g : ℝ) ^ (2 * N) * ((B.I.n : ℝ) * B.I.f * B.I.rd * B.g * b) ^ N := by
      rw [← hX]; positivity
    gcongr
    rw [le_div_iff₀ hpos]
    exact hA
  calc ∫⁻ x in GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b, ENNReal.ofReal (kern B.I (phe B d) x x).re ∂(B.I.muA B.μf)
      ≤ ∫⁻ _ in GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b, ENNReal.ofReal Kc ∂(B.I.muA B.μf) := by
        first
          | exact setLIntegral_mono measurable_const hpt
          | exact lintegral_mono_ae ((ae_restrict_iff' (by
              simp only [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet]; exact (measurableSet_eq_fun_of_countable
                measurable_const measurable_const))).2 (Filter.Eventually.of_forall hpt))
    _ = ENNReal.ofReal Kc * B.I.muA B.μf (GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet B q b) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal Kc * B.I.muA B.μf B.fund := by
        gcongr
        intro x hx
        simp only [GlobalTheory.IndefiniteRowSideFullHecke.DeepSet.deepSet, Set.mem_setOf_eq] at hx
        exact hx.1
    _ ≤ ENNReal.ofReal Kc * ENNReal.ofReal (X ^ N * (B.g : ℝ) ^ (2 * N) * kR / P) := by gcongr
    _ = ENNReal.ofReal ((B.D : ℝ) * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) := by
        rw [← ENNReal.ofReal_mul (by rw [hKc]; positivity)]
        congr 1
        rw [hKc, hN]
        push_cast
        field_simp

end GlobalTheory.DeepRegion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFinsetOfMemNhds
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Per MeasureTheory IsDedekindDomain NumberField
open Filter Topology
open scoped TensorProduct

namespace GlobalTheory.ThetaVacuumAE

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_finset_of_mem_nhds {F : Type} [Field F] [NumberField F] {N : Set (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F)} (hN : N ∈ 𝓝 0) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ α ∈ intAf F, (∀ v ∈ S, evalV F v α = 0) → α ∈ N := by
  have hc := (RestrictedProduct.isEmbedding_structureMap
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓕 := cofinite)).continuous
  have h := hc.tendsto (fun w => ⟨0, zero_mem (w.adicCompletionIntegers F)⟩) hN
  have h' := mem_map.1 h
  rw [nhds_pi, mem_pi'] at h'
  obtain ⟨I, t, ht, hI⟩ := h'
  refine ⟨I, fun α hα h0 => ?_⟩
  have hm : (fun w => (⟨evalV F w α, hα w⟩ : (w.adicCompletionIntegers F : Set (w.adicCompletion F)))) ∈
      Set.pi (I : Set (HeightOneSpectrum (𝓞 F))) t := by
    intro w hw
    have := mem_of_mem_nhds (ht w)
    convert this using 2
    exact h0 w hw
  exact hI hm

theorem fg_int {E : Type} [Field E] [NumberField E] {M : Submodule (𝓞 E) E} (h : M.FG) : (M.restrictScalars ℤ).FG :=
  Submodule.FG.restrictScalars h

theorem exists_fg_coord {D : D7} (V : HSp D) :
    ∃ M : Submodule ℤ D.host.E, M.FG ∧ ∀ x ∈ L0c D V, ∀ i, x i ∈ M ∧ star (x i) ∈ M := by
  let P : Submodule (𝓞 D.host.E) D.host.E := ⨆ i, V.L0.map ((V.frame.coord i).restrictScalars (𝓞 D.host.E))
  have hP : P.FG := Submodule.fg_iSup _ fun i => V.standardTuple_isLattice.fg.map _
  have hx : ∀ x ∈ L0c D V, ∀ i, x i ∈ P := fun x hx i =>
    Submodule.mem_iSup_of_mem i ⟨_, hx, by simp [Finsupp.single_apply]⟩
  let c : D.host.E →ₗ[ℤ] D.host.E := (starRingEnd D.host.E).toAddMonoidHom.toIntLinearMap
  refine ⟨P.restrictScalars ℤ ⊔ (P.restrictScalars ℤ).map c, (fg_int hP).sup ((fg_int hP).map c), fun x h i =>
    ⟨Submodule.mem_sup_left (hx x h i), Submodule.mem_sup_right ⟨x i, hx x h i, rfl⟩⟩⟩

theorem continuous_tmul (D : D7) (e : D.host.E) :
    Continuous fun α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => (pairA D.host.F 0 α ⊗ₜ[D.host.F] e : AE D) := by
  have hp : Continuous fun β : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F => pairA D.host.F 0 β := continuous_const.prodMk continuous_id
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have h := hp.smul (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D)))
  refine h.congr fun α => ?_
  simp only [Pi.smul_apply', TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end GlobalTheory.ThetaVacuumAE

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalFrameOfLe
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.IntertwinerFrame

theorem exists_orthonormal_frame_of_le : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → ∀ S : Submodule ℂ (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), S ≤ B.I.HomS B.σs B.μf B.fund B.R → FiniteDimensional ℂ S → ∃ T : Fin (Module.finrank ℂ S) → (B.Hs →L[ℂ] B.I.L2 B.μf B.fund), (∀ i, T i ∈ S) ∧ (∀ i u, ‖T i u‖ = ‖u‖) ∧ ∀ i j, i ≠ j → ∀ u u', ⟪T i u, T j u'⟫_ℂ = 0 := by
  intro B d hd S hle hfin
  obtain ⟨hU, hirr, -, hw, -⟩ := GlobalTheory.Dec.tensorRep B d hd
  obtain ⟨-, -, hR, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  let σ : B.I.Ginf →* (B.Hs →L[ℂ] B.Hs) :=
    { toFun := B.σs
      map_one' := hU.1
      map_mul' := hU.2.1 }
  obtain ⟨T, h1, h2, h3, -⟩ := exists_frame S (B.tens B.w) fun T hT T' hT' u u' =>
    inner_intertwiners σ hU.2.2.1 hirr (fun g => B.R (g, 1)) (fun g => hR _) _ hw T T' (hle hT) (hle hT') u u'
  exact ⟨T, h1, h2, h3⟩

end GlobalTheory.IntertwinerFrame
end
end

