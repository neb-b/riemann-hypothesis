module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Formalism.SatakeDualWeyl.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0771
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockDetSingleBlockSecondEqOneOfLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem mem_blockTriangular_singleBlock_of_le {κ : Type} [CommRing κ] {n r : ℕ} (h : n ≤ r) (g : GL (Fin n) κ) :
    g ∈ Formalism.L2.DIV.blockTri (κ := κ) (n := n) (Formalism.L2.DIV.blk2 r) := by
  rw [Formalism.L2.DIV.mem_blockTri]
  intro i j hij
  have hi : Formalism.L2.DIV.blk2 r i = 0 := by
    unfold Formalism.L2.DIV.blk2; exact if_pos (lt_of_lt_of_le i.isLt h)
  have hj : Formalism.L2.DIV.blk2 r j = 0 := by
    unfold Formalism.L2.DIV.blk2; exact if_pos (lt_of_lt_of_le j.isLt h)
  rw [hi, hj] at hij
  exact absurd hij (lt_irrefl 0)

theorem blockDet_singleBlock_second_eq_one_of_le {κ : Type} [CommRing κ] {n r : ℕ} (h : n ≤ r) (g : GL (Fin n) κ) :
    Formalism.L2.DIV.dBlk (κ := κ) (n := n) (Formalism.L2.DIV.blk2 r) 1 g = 1 := by
  have hm := mem_blockTriangular_singleBlock_of_le (κ := κ) h g
  haveI : IsEmpty {a : Fin n // Formalism.L2.DIV.blk2 r a = 1} := by
    refine ⟨fun a => ?_⟩
    have h1 := a.2
    have h2 := a.1.isLt
    unfold Formalism.L2.DIV.blk2 at h1
    split_ifs at h1 with hlt <;> omega
  apply Units.ext
  rw [Formalism.L2.DIV.diag_block_det_val 1 hm, Units.val_one]
  exact Matrix.det_isEmpty

theorem levG_twist_trivial_of_rank_eq :
    ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t : ℕ) (hr : r ≤ V.rank), V.rank = r → ∀ (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ), levG V β (datY V.rank r t 0 hr Pg Q P χ ξ Frm.B) = levG V β (datY V.rank r t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) ∧ ∀ k ∈ levG V β (datY V.rank r t 0 hr Pg Q P χ ξ Frm.B), levChi V β (datY V.rank r t 0 hr Pg Q P χ ξ Frm.B) k = levChi V β (datY V.rank r t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) k := by
  intro D V β r t hr hrk Pg Q P χ ξ
  subst hrk
  have hlev : Formalism.L2.DIV.lev D.sp.cm V.gram β (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B) =
      Formalism.L2.DIV.lev D.sp.cm V.gram β (datY V.rank V.rank t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) := by
    ext x
    simp only [Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev]
    constructor
    · rintro ⟨⟨h1, h2, h3, _⟩, h5⟩
      refine ⟨⟨h1, h2, h3, fun PP hPP => ?_⟩, h5⟩
      change PP ∈ (∅ : Finset (Formalism.L2.DIV.Pl D.host.E)) at hPP
      simp at hPP
    · rintro ⟨⟨h1, h2, h3, _⟩, h5⟩
      exact ⟨⟨h1, h2, h3, fun PP _ => mem_blockTriangular_singleBlock_of_le (r := V.rank) le_rfl _⟩, h5⟩
  have hfn : ∀ y, Formalism.L2.DIV.levFn β (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B) y =
      Formalism.L2.DIV.levFn β (datY V.rank V.rank t 0 hr Pg ∅ P χ (fun _ => 1) Frm.B) y := by
    intro y
    unfold Formalism.L2.DIV.levFn
    have hq : ∏ PP ∈ (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).Q,
        (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).xq PP
          (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 (datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).r) 1
            (Formalism.L2.DIV.redFn β PP y)) = 1 := by
      refine Finset.prod_eq_one fun PP _ => ?_
      have h2 := blockDet_singleBlock_second_eq_one_of_le (r := V.rank) (le_refl V.rank) (Formalism.L2.DIV.redFn β PP y)
      exact (congrArg (⇑((datY V.rank V.rank t 0 hr Pg Q P χ ξ Frm.B).xq PP)) h2).trans (map_one _)
    rw [hq]
    change _ = _ * ∏ PP ∈ (∅ : Finset (Formalism.L2.DIV.Pl D.host.E)), _
    rw [Finset.prod_empty]
    rfl
  refine ⟨?_, fun k _ => ?_⟩
  · unfold levG
    rw [hlev]
  · unfold levChi
    rw [hfn]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory NumberField IsDedekindDomain

noncomputable section
namespace GlobalTheory.SmGL.SphCompletion

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in
private theorem valuation_le_one_iff_adicValuation_le_one (x : v.adicCompletion F) :
    letI := _root_.GlobalTheory.LocalData.complRel v
    (valuation (v.adicCompletion F)) x ≤ 1 ↔ Valued.v x ≤ 1 := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  have : Valuation.Compatible
      (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))) :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (valuation (v.adicCompletion F)) Valued.v).le_one_iff_le_one

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in
private theorem residueFieldCard_adicCompletion_lemma :
    letI := _root_.GlobalTheory.LocalData.complRel v
    haveI := _root_.GlobalTheory.LocalData.isLocalField v
    _root_.GlobalTheory.SplitWeil.resCard (v.adicCompletion F) = _root_.Formalism.UG.qV F v := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  have hmem : ∀ x : v.adicCompletion F,
      x ∈ 𝒪[v.adicCompletion F] ↔ x ∈ v.adicCompletionIntegers F := fun x => by
    simpa [Valuation.mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers] using
      valuation_le_one_iff_adicValuation_le_one v x
  let e : 𝒪[v.adicCompletion F] ≃+* v.adicCompletionIntegers F :=
    { toFun := fun x => ⟨x, (hmem x).1 x.2⟩
      invFun := fun x => ⟨x, (hmem x).2 x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  unfold _root_.GlobalTheory.SplitWeil.resCard
  rw [← _root_.Formalism.UG.P.tjcosets_card_residue v]
  exact Nat.card_congr (IsLocalRing.ResidueField.mapEquiv e).toEquiv


open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.SmGL.SphCompletion.ord_completion (x : (v.adicCompletion F)ˣ) :
    letI := _root_.GlobalTheory.LocalData.complRel v
    haveI := _root_.GlobalTheory.LocalData.isLocalField v
    _root_.GlobalTheory.SmGL.ord (v.adicCompletion F) x =
      -WithZero.log (Valued.v (x : v.adicCompletion F)) := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  have h := _root_.GlobalTheory.LGrp.BorelCompletion.nabs_completion v x
  rw [_root_.GlobalTheory.LGrp.nabs_eq_zpow, residueFieldCard_adicCompletion_lemma] at h
  have hq : (1 : ℝ) < _root_.Formalism.UG.qV F v := by
    rw [← residueFieldCard_adicCompletion_lemma v]
    exact_mod_cast _root_.GlobalTheory.SplitWeil.one_lt_resCard _
  have := zpow_right_injective₀ (by linarith) hq.ne' h
  omega


open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.SmGL.SphCompletion.KO_completion (n : ℕ) :
    letI := _root_.GlobalTheory.LocalData.complRel v
    haveI := _root_.GlobalTheory.LocalData.isLocalField v
    _root_.GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n) = _root_.Formalism.UG.GLint (Fin n) (_root_.Formalism.UG.Ov F v) := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  haveI := _root_.Formalism.UG.P.tjcosets_isLocalRing v
  ext g
  rw [_root_.GlobalTheory.SplitFlip.mem_KO_iff, _root_.Formalism.UG.P.tjcosets_mem_K_iff]
  simp only [Valuation.mem_integer_iff, _root_.Formalism.UG.P.cartan_mem_Ov, valuation_le_one_iff_adicValuation_le_one]

open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in
private theorem natCast_zpow_neg_cpow_eq_cpow_mul (q : ℕ) (m : ℤ) (n : ℕ) (i : Fin n) :
    (((q : ℝ) ^ (-m) : ℝ) : ℂ) ^ ((((n : ℤ) - 1 - 2 * (i : ℤ) : ℤ) : ℂ) / 2) =
      (q : ℂ) ^ (-(m : ℂ) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2)) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : ((((n : ℤ) - 1 - 2 * (i : ℤ) : ℤ) : ℂ) / 2) =
      ((((n : ℝ) - 1 - 2 * (i : ℝ)) / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : (-(m : ℂ) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2)) =
      (((-m : ℝ) * (((n : ℝ) - 1 - 2 * (i : ℝ)) / 2) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h1, h2, ← Complex.ofReal_cpow (zpow_nonneg hq _), ← Complex.ofReal_natCast,
    ← Complex.ofReal_cpow hq, Real.rpow_mul hq, ← Real.rpow_intCast]
  push_cast
  rfl


open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.SmGL.SphCompletion.law_completion (n : ℕ) (α : Fin n → ℂˣ)
    (b : _root_.GlobalTheory.SmGL.borel (v.adicCompletion F) (Fin n)) (c : ℂ) :
    letI := _root_.GlobalTheory.LocalData.complRel v
    haveI := _root_.GlobalTheory.LocalData.isLocalField v
    (_root_.GlobalTheory.SmGL.deltaHalf (v.adicCompletion F) (fun _ : Fin n => Unit)
        (_root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b) : ℂ) •
      ((_root_.GlobalTheory.SmGL.ofChar
          (_root_.GlobalTheory.SmGL.torusChar fun i => _root_.GlobalTheory.SmGL.unrChar (v.adicCompletion F) (α i))).comp
        (_root_.GlobalTheory.SmGL.leviTorus (v.adicCompletion F) (Fin n)).symm.toMonoidHom)
        (_root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b) c =
      _root_.Formalism.UG.chiDelta F v (fun i => (α i : ℂ)) b.1 * c := by
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  set t := _root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b with ht
  have hdet : ∀ i, ((Matrix.GeneralLinearGroup.det (t i) : (v.adicCompletion F)ˣ) :
      v.adicCompletion F) = (b.1 : Matrix _ _ _) i i := by
    intro i
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_unique]
    exact _root_.GlobalTheory.SmGL.leviProj_apply _ (_root_.GlobalTheory.SmGL.points (Fin n)) b i () ()
  have hsymm : ∀ i, (_root_.GlobalTheory.SmGL.leviTorus (v.adicCompletion F) (Fin n)).symm t i =
      Matrix.GeneralLinearGroup.det (t i) := fun i => rfl
  rw [_root_.GlobalTheory.SmGL.deltaHalf_apply]
  simp only [MonoidHom.comp_apply, _root_.GlobalTheory.SmGL.ofChar_apply, smul_eq_mul,
    MulEquiv.coe_toMonoidHom, _root_.GlobalTheory.SmGL.torusChar_apply, _root_.GlobalTheory.SmGL.unrChar_apply,
    hsymm, Units.coe_prod, _root_.GlobalTheory.SmGL.val_absPow]
  unfold _root_.Formalism.UG.chiDelta
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have hord : _root_.GlobalTheory.SmGL.ord (v.adicCompletion F)
      (Matrix.GeneralLinearGroup.det (t i)) = _root_.Formalism.UG.ordV F v ((b.1 : Matrix _ _ _) i i) := by
    rw [_root_.GlobalTheory.SmGL.SphCompletion.ord_completion, _root_.GlobalTheory.LGrp.BorelCompletion.ordV_eq, hdet]
  rw [_root_.GlobalTheory.SmGL.modExp_fin _ (fun _ => Fintype.card_unit),
    _root_.GlobalTheory.LGrp.nabs_eq_zpow, hord, residueFieldCard_adicCompletion_lemma, mul_comm]
  rw [Units.val_zpow_eq_zpow_val, natCast_zpow_neg_cpow_eq_cpow_mul]


open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.SmGL.SphCompletion.exists_fixed_iff {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (χ : Fin n → kˣ →* ℂˣ)
    (φ : GL (Fin n) k → ℂ) :
    (∃ f ∈ _root_.GlobalTheory.PRep.fixed (_root_.GlobalTheory.SmGL.prinSeries χ)
        (_root_.GlobalTheory.SplitWeil.KO k (Fin n)), f.1.1 = φ) ↔
      (∀ (b : _root_.GlobalTheory.SmGL.borel k (Fin n)) g, φ (b * g) =
        (_root_.GlobalTheory.SmGL.deltaHalf k (fun _ : Fin n => Unit)
            (_root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b) : ℂ) •
          ((_root_.GlobalTheory.SmGL.ofChar (_root_.GlobalTheory.SmGL.torusChar χ)).comp
              (_root_.GlobalTheory.SmGL.leviTorus k (Fin n)).symm.toMonoidHom)
            (_root_.GlobalTheory.SmGL.leviProj _ (_root_.GlobalTheory.SmGL.points (Fin n)) b) (φ g)) ∧
      ∀ g ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n), ∀ x, φ (x * g) = φ x := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [_root_.GlobalTheory.LGrp.mem_fixed] at hf
    refine ⟨fun b g => _root_.GlobalTheory.SmGL.parInd_law _ _ f b g, fun g hg x => ?_⟩
    have := congrArg (fun f' => f'.1.1 x) (hf g hg)
    exact (_root_.GlobalTheory.SmGL.parInd_apply _ _ g x f).symm.trans this
  · rintro ⟨hlaw, hinv⟩
    let f₀ : _root_.GlobalTheory.PRep.indSpace (_root_.GlobalTheory.SmGL.parab k (_root_.GlobalTheory.SmGL.points (Fin n)))
        ((_root_.GlobalTheory.SmGL.twist
          ((_root_.GlobalTheory.SmGL.ofChar (_root_.GlobalTheory.SmGL.torusChar χ)).comp
            (_root_.GlobalTheory.SmGL.leviTorus k (Fin n)).symm.toMonoidHom)
          (_root_.GlobalTheory.SmGL.deltaHalf k (fun _ : Fin n => Unit))).comp
          (_root_.GlobalTheory.SmGL.leviProj k (_root_.GlobalTheory.SmGL.points (Fin n)))) :=
      ⟨φ, fun b g => hlaw b g⟩
    have hfix : ∀ g ∈ _root_.GlobalTheory.SplitWeil.KO k (Fin n),
        _root_.GlobalTheory.PRep.ind _ _ g f₀ = f₀ := fun g hg => by
      ext x
      exact hinv g hg x
    have hsm : f₀ ∈ _root_.GlobalTheory.PRep.smoothPart (_root_.GlobalTheory.PRep.ind _ _) := by
      apply _root_.GlobalTheory.SmGL.mem_smoothPart_of_nhds
      refine Filter.mem_of_superset
        (_root_.GlobalTheory.SplitFlip.isOpen_KO.mem_nhds (_root_.GlobalTheory.SplitWeil.KO k (Fin n)).one_mem)
        fun g hg => hfix g hg
    refine ⟨⟨f₀, hsm⟩, ?_, rfl⟩
    rw [_root_.GlobalTheory.LGrp.mem_fixed]
    intro g hg
    ext x
    exact (_root_.GlobalTheory.SmGL.parInd_apply _ _ g x _).trans (hinv g hg x)


open ValuativeRel MeasureTheory NumberField IsDedekindDomain in
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.SmGL.SphCompletion.isSpherical_iff : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (α : Fin n → ℂˣ)
    (φ : GL (Fin n) (v.adicCompletion F) → ℂ),
    letI := _root_.GlobalTheory.LocalData.complRel v; haveI := _root_.GlobalTheory.LocalData.isLocalField v;
    (_root_.Formalism.UG.IsSpherical F v (fun i => (α i : ℂ)) φ ↔
      ∃ f ∈ _root_.GlobalTheory.PRep.fixed
          (_root_.GlobalTheory.SmGL.prinSeries fun i => _root_.GlobalTheory.SmGL.unrChar (v.adicCompletion F) (α i))
          (_root_.GlobalTheory.SplitWeil.KO (v.adicCompletion F) (Fin n)), f.1.1 = φ) := by
  intro F _ _ v n α φ
  letI := _root_.GlobalTheory.LocalData.complRel v
  haveI := _root_.GlobalTheory.LocalData.isLocalField v
  have hlaw := _root_.GlobalTheory.SmGL.SphCompletion.law_completion v n α
  have hone : _root_.Formalism.UG.chiDelta F v (fun i => (α i : ℂ)) 1 = 1 := by
    unfold _root_.Formalism.UG.chiDelta
    simp [_root_.GlobalTheory.LGrp.BorelCompletion.ordV_eq]
  have hborel : ∀ b : GL (Fin n) (v.adicCompletion F),
      _root_.Formalism.UG.IsUpperB F v b ↔ b ∈ _root_.GlobalTheory.SmGL.borel (v.adicCompletion F) (Fin n) := by
    intro b
    rw [_root_.GlobalTheory.SmGL.mem_borel]
    rfl
  rw [_root_.GlobalTheory.SmGL.SphCompletion.exists_fixed_iff,
    _root_.GlobalTheory.SmGL.SphCompletion.KO_completion]
  unfold _root_.Formalism.UG.IsSpherical
  constructor
  · intro h
    refine ⟨fun b g => ?_, fun g hg x => ?_⟩
    · rw [hlaw b (φ g)]
      simpa only [mul_one] using h b g 1 ((hborel _).2 b.2) (one_mem _)
    · simpa only [one_mul, hone] using h 1 x g ((hborel 1).2 (one_mem _)) hg
  · rintro ⟨hL, hI⟩ b g k hb hk
    rw [hI k hk, ← hlaw ⟨b, (hborel b).1 hb⟩ (φ g)]
    exact hL ⟨b, (hborel b).1 hb⟩ g

end GlobalTheory.SmGL.SphCompletion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsThetaPOfIntegrable
section
open MeasureTheory Formalism.IndefR

namespace GlobalTheory.ThetaIntegralLinear

theorem exists_isThetaP_of_integrable {G' H' S' Sinf TK Tau : Type} [MeasurableSpace H'] [AddCommGroup S'] [Module ℂ S']
    [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]
    (ν : Measure H') (𝓕 : Set H') (th : G' → H' → S' →ₗ[ℂ] ℂ) (pt : Sinf →ₗ[ℂ] S')
    (io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf) (A : Submodule ℂ (H' → Tau))
    (hint : ∀ f : A, ∀ e g, IntegrableOn (fun h => th g h (pt (io e ((f : H' → Tau) h)))) 𝓕 ν) :
    ∃ thP, Lift.IsThetaP ν 𝓕 (fun g h s => th g h s) (fun s => pt s) io A thP := by

  refine ⟨LinearMap.mk₂ ℂ (fun f e g => ∫ h in 𝓕, th g h (pt (io e ((f : H' → Tau) h))) ∂ν)
    ?_ ?_ ?_ ?_, hint, ?_⟩
  · intro f₁ f₂ e
    funext g
    simp only [Submodule.coe_add, Pi.add_apply, map_add (f := _)]
    exact integral_add (hint f₁ e g) (hint f₂ e g)
  · intro c f e
    funext g
    simp only [Submodule.coe_smul, Pi.smul_apply, map_smul, smul_eq_mul]
    exact integral_const_mul c _
  · intro f e₁ e₂
    funext g
    simp only [map_add (f := _), LinearMap.add_apply, Pi.add_apply]
    exact integral_add (hint f e₁ g) (hint f e₂ g)
  · intro c f e
    funext g
    simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    exact integral_const_mul c _
  · intro f e g
    rfl

end GlobalTheory.ThetaIntegralLinear
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteRealPointsCommute
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.FinRealComm

private theorem eq_map_inl_fst_add_map_inr_snd_tmul {F A B E : Type} [CommRing F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (z : (A × B) ⊗[F] E) :
    z = TensorProduct.map (LinearMap.inl F A B) LinearMap.id
          (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
        TensorProduct.map (LinearMap.inr F A B) LinearMap.id
          (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, TensorProduct.map_tmul,
      TensorProduct.map_tmul, ← TensorProduct.add_tmul]
    congr 1
    ext <;> simp
  | add u v hu hv =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _)]
    conv_lhs => rw [hu, hv]
    abel

theorem tensor_prod_ext {F A B E : Type} [CommRing F] [CommRing A] [CommRing B] [CommRing E]
    [Algebra F A] [Algebra F B] [Algebra F E] (x y : (A × B) ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) y)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) x =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) y) : x = y := by
  rw [eq_map_inl_fst_add_map_inr_snd_tmul x, eq_map_inl_fst_add_map_inr_snd_tmul y, h1, h2]

theorem GA_ext_inf_fin {D : D7} (V : HSp D) (x y : GA D V)
    (h1 : infHom V x = infHom V y) (h2 : finHom V x = finHom V y) : x = y := by
  have hm : (matHom V x).1 = (matHom V y).1 := by
    ext i j
    have e1 := congrArg (fun g => g.1 i j) h1
    have e2 := congrArg (fun g => g.1 i j) h2
    simp only [infHom, finHom, MonoidHom.comp_apply, Formalism.UG.bc, Units.coe_map,
      MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply, Matrix.map_apply] at e1 e2
    exact tensor_prod_ext _ _ e1 e2
  exact Subtype.ext (Units.ext hm)

theorem finite_real_points_commute :
    ∀ {D : D7} (V : HSp D) (a b : GA D V), a ∈ GfC V → b ∈ GinfC V → a * b = b * a := by
  intro D V a b ha hb
  have ha' : infHom V a = 1 := ha
  have hb' : finHom V b = 1 := hb
  apply GA_ext_inf_fin V
  · rw [map_mul, map_mul, ha', one_mul, mul_one]
  · rw [map_mul, map_mul, hb', one_mul, mul_one]

end GlobalTheory.FinRealComm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FundamentalDomainSetIntegralMulRight
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem fundamentalDomain_setIntegral_mul_right :
    ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ k : G, Measure.map (fun g => g * k) μ = μ → ∀ f : G → ℂ, (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓕 μ → IntegrableOn (fun g => f (g * k)) 𝓕 μ ∧ ∫ g in 𝓕, f (g * k) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  intro G _ _ _ _ Γ _ μ _ 𝓕 h𝓕 k hk f hf hi
  have hmp : MeasurePreserving (fun g : G => g * k) μ μ := ⟨measurable_mul_const k, hk⟩
  have hemb : MeasurableEmbedding (fun g : G => g * k) := measurableEmbedding_mulRight k
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ (γ : Γ) (g : G), (fun g : G => f (g * k)) (γ • g) = (fun g : G => f (g * k)) g := by
    intro γ g
    simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
    exact hf γ γ.2 _
  refine ⟨?_, ?_⟩
  · rw [h𝓕.integrableOn_iff h2 hinv]
    exact (hmp.integrableOn_comp_preimage hemb).2 hi
  · rw [h𝓕.setIntegral_eq h2 hinv]
    exact hmp.setIntegral_preimage_emb hemb f 𝓕

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasTypeOfMemMult
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem hasType_of_mem_mult : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), ∀ T ∈ Mult θ M (levG V β L : Set (GA D V)) (levChi V β L), ∀ v, HasType V β L (T v) := by
  intro D V S θ M β L T hT v
  induction hT using Submodule.span_induction generalizing v with
  | mem x hx => exact fun κ hκ h => hx.lev v κ hκ h
  | zero => intro κ _ h; simp
  | add x y _ _ hx hy =>
    intro κ hκ h
    simp only [MultilinearMap.add_apply, Pi.add_apply]
    rw [hx v κ hκ h, hy v κ hκ h, mul_add]
  | smul a x _ hx =>
    intro κ hκ h
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [hx v κ hκ h, mul_left_comm]

end GlobalTheory
end

