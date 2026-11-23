module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeInfinitesimalCharLargeGap
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsLieIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0209

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelDatumConjugatePlacesLevelEqCharacters
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftDatComb

open GlobalTheory.LiftLevel GlobalTheory.LiftDat

variable {D : D7}

theorem conjI_eq_comap (P : Ideal (𝓞 D.host.E)) : conjI P = P.comap GlobalTheory.SW.Lev.bar := by
  ext a; rw [GlobalTheory.SW.Lev.mem_conjI, Ideal.mem_comap]

theorem bar_surj : Function.Surjective (GlobalTheory.SW.Lev.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
  fun a => ⟨GlobalTheory.SW.Lev.bar a, GlobalTheory.SW.Lev.bar_bar a⟩

theorem conjI_isMax (PP : Formalism.L2.DIV.Pl D.host.E) : (conjI PP.asIdeal).IsMaximal := by
  rw [conjI_eq_comap]
  exact Ideal.comap_isMaximal_of_surjective _ bar_surj

theorem conjI_inj {P P' : Ideal (𝓞 D.host.E)} (h : conjI P = conjI P') : P = P' := by
  ext a
  have := SetLike.ext_iff.1 h (GlobalTheory.SW.Lev.bar a)
  rwa [GlobalTheory.SW.Lev.mem_conjI, GlobalTheory.SW.Lev.mem_conjI, GlobalTheory.SW.Lev.bar_bar] at this

theorem mem_liftI {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {x : 𝓞 D.host.E} :
    x ∈ liftI Pg Q ↔ ∀ PP ∈ Pg ∪ Q, GlobalTheory.SW.Lev.bar x ∈ PP.asIdeal := by
  constructor
  · intro hx PP hPP
    exact GlobalTheory.SW.Lev.mem_conjI.1 (liftI_le hPP hx)
  · intro h
    unfold liftI
    rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
    · simp only [Submodule.mem_iInf]
      intro PP hPP
      exact GlobalTheory.SW.Lev.mem_conjI.2 (h PP hPP)
    · intro PP _ PP' _ hne
      have hne' : conjI PP.asIdeal ≠ conjI PP'.asIdeal := fun e =>
        hne (HeightOneSpectrum.ext (conjI_inj e))
      exact (Ideal.isCoprime_iff_sup_eq).2 ((conjI_isMax PP).coprime_of_ne (conjI_isMax PP') hne')

theorem isUnit_mk_liftI {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {x : 𝓞 D.host.E}
    (h : ∀ PP ∈ Pg ∪ Q, GlobalTheory.SW.Lev.bar x ∉ PP.asIdeal) : IsUnit (Ideal.Quotient.mk (liftI Pg Q) x) := by
  have hc : IsCoprime (Ideal.span {x}) (liftI Pg Q) := by
    unfold liftI
    refine IsCoprime.prod_right fun PP hPP => ?_
    have hx : x ∉ conjI PP.asIdeal := fun hm => h PP hPP (GlobalTheory.SW.Lev.mem_conjI.1 hm)
    obtain ⟨y, i, hi, e⟩ := (conjI_isMax PP).exists_inv hx
    exact Ideal.isCoprime_iff_exists.2 ⟨y * x, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x), i, hi, e⟩
  obtain ⟨i, hi, j, hj, e⟩ := Ideal.isCoprime_iff_exists.1 hc
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hi
  refine isUnit_iff_exists_inv.2 ⟨Ideal.Quotient.mk _ a, ?_⟩
  have : Ideal.Quotient.mk (liftI Pg Q) j = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hj
  rw [← map_mul, mul_comm, eq_sub_of_add_eq e, map_sub, this, sub_zero, map_one]

section CongLemmas
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)

theorem cong_of_sub_mem {𝔪 : Ideal (𝓞 E)} {u v : Fin r → E} (h : u - v ∈ 𝔪 • X.Λ) : GlobalTheory.SW.Cong X 𝔪 u v :=
  ⟨1, by rw [Ideal.span_singleton_one, Ideal.isCoprime_iff_sup_eq, top_sup_eq], by rwa [one_smul]⟩

theorem cong_congr_left {𝔪 : Ideal (𝓞 E)} {y u v : Fin r → E} (hy : y - u ∈ 𝔪 • X.Λ)
    (h : GlobalTheory.SW.Cong X 𝔪 y v) : GlobalTheory.SW.Cong X 𝔪 u v := by
  obtain ⟨s, hs, hm⟩ := h
  refine ⟨s, hs, ?_⟩
  have : s • (u - v) = s • (y - v) - s • (y - u) := by
    rw [← smul_sub]; congr 1; abel
  rw [this]
  exact sub_mem hm (Submodule.smul_mem _ s hy)

theorem sum_mem_of_coeff {𝔪 : Ideal (𝓞 E)} {m : ℕ} (β : Fin m → Fin r → E) (hβ : ∀ i, β i ∈ X.Λ)
    (d : Fin m → 𝓞 E) (hd : ∀ j, d j ∈ 𝔪) : ∑ j, d j • β j ∈ 𝔪 • X.Λ :=
  Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hd j) (hβ j)

end CongLemmas

section Mat
open GlobalTheory.LiftLevel GlobalTheory.LiftDat
variable {D : D7}

theorem mk_conjI_eq_iff (P : Ideal (𝓞 D.host.E)) (x y : 𝓞 D.host.E) :
    Ideal.Quotient.mk (conjI P) x = Ideal.Quotient.mk (conjI P) y ↔
      Ideal.Quotient.mk P (GlobalTheory.SW.Lev.bar x) = Ideal.Quotient.mk P (GlobalTheory.SW.Lev.bar y) := by
  rw [Ideal.Quotient.eq, Ideal.Quotient.eq, GlobalTheory.SW.Lev.mem_conjI, map_sub]

theorem mapMat_eq_one_iff {R' : Type*} [CommRing R'] {r : ℕ} (f : 𝓞 D.host.E →+* R')
    (A : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) :
    A.map f = 1 ↔ ∀ a b, f (A a b) = f ((1 : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) a b) := by
  rw [← Matrix.map_one f (map_zero f) (map_one f), ← Matrix.ext_iff]
  simp only [Matrix.map_apply]

theorem jgrp_iff {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {r : ℕ} (κ : GL (Fin r) (𝓞 D.host.E ⧸ liftI Pg Q))
    (ct : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) (hκ : κ.val = ctᵀ.map (Ideal.Quotient.mk _)) :
    κ ∈ Jgrp Pg Q r ↔ ∀ PP ∈ Pg, ct.map ((Ideal.Quotient.mk PP.asIdeal).comp GlobalTheory.SW.Lev.bar) = 1 := by
  rw [mem_Jgrp]
  refine forall₂_congr fun PP hPP => ?_
  rw [Units.ext_iff]
  have e1 : ((Matrix.GeneralLinearGroup.map (toConj Pg Q PP (Finset.mem_union_left _ hPP)) κ :
      GL (Fin r) _) : Matrix (Fin r) (Fin r) _) = ct.transpose.map (Ideal.Quotient.mk (conjI PP.asIdeal)) := by
    ext a b
    rw [Matrix.GeneralLinearGroup.map_apply, hκ]
    rfl
  rw [e1, Units.val_one, Matrix.transpose_map, Matrix.transpose_eq_one, mapMat_eq_one_iff, mapMat_eq_one_iff]
  exact forall₂_congr fun a b => mk_conjI_eq_iff _ _ _

theorem conjRes_det {Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {PP : Formalism.L2.DIV.Pl D.host.E} (h : PP ∈ Pg ∪ Q) {r : ℕ}
    (ct : Matrix (Fin r) (Fin r) (𝓞 D.host.E)) :
    conjRes Pg Q PP h (ctᵀ.map (Ideal.Quotient.mk (liftI Pg Q))).det =
      (ct.map ((Ideal.Quotient.mk PP.asIdeal).comp GlobalTheory.SW.Lev.bar)).det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_map, Matrix.transpose_map, Matrix.det_transpose]
  rfl

end Mat

end GlobalTheory.LiftDatComb

namespace GlobalTheory.LiftDat

open GlobalTheory.LiftDatComb GlobalTheory.LiftLevel

theorem dat_mkLevel_eq : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (hn : T.rank ≤ S.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (h1 : GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤) (h2 : GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥) (h3 : IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q))) (h4 : IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2})) (β : Fin T.rank → Fin T.rank → D.host.E) (hβ : ∀ i, β i ∈ C.X.Λ) (hsp : C.X.Λ ≤ Submodule.span (𝓞 D.host.E) (Set.range β) ⊔ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) (Lv0 : GlobalTheory.SW.Level C.X), (∀ d : Fin T.rank → 𝓞 D.host.E, GlobalTheory.SW.Cong C.X (GlobalTheory.LiftLevel.liftI Pg Q) (∑ j, d j • β j) 0 → ∀ j, d j ∈ GlobalTheory.LiftLevel.liftI Pg Q) → ∀ (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) (c : Fin S.rank → Fin T.rank → 𝓞 D.host.E), (∀ i, y i - ∑ j, c i j • β j ∈ GlobalTheory.LiftLevel.liftI Pg Q • C.X.Λ) → ∀ Y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin S.rank) (Fin T.rank) (Formalism.L2.DIV.kP PP), (∀ PP ∈ Pg ∪ Q, ∀ i j, Y PP i j = Ideal.Quotient.mk PP.asIdeal (GlobalTheory.SW.Lev.bar (c i j))) → (GlobalTheory.LiftDat.mkLevel C Pg Q ξ h1 h2 h3 h4 β hβ hsp Lv0).dat hn y = omegaK Pg Y * omegaQ Q T.rank ξ (-1) Y := by
  intro D S T C hn Pg Q ξ h1 h2 h3 h4 β hβ hsp Lv0 hind y c hyc Y hY
  set ct : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E) := fun a b => c (Fin.castLE hn a) b with hct
  have hTop : ∀ PP ∈ Pg ∪ Q, topL T.rank (Y PP) = ct.map ((Ideal.Quotient.mk PP.asIdeal).comp Lev.bar) := by
    intro PP hPP
    ext a b
    rw [topL, dite_eq_left ⟨lt_of_lt_of_le a.2 hn, b.2⟩, hY PP hPP]
    rfl
  have hcong0 : ∀ i, GlobalTheory.SW.Cong C.X (liftI Pg Q) (y i) 0 ↔ ∀ j, c i j ∈ liftI Pg Q := by
    intro i
    constructor
    · intro hc
      obtain ⟨s, hs, hm⟩ := cong_congr_left C.X (hyc i) hc
      exact hind (c i) ⟨s, hs, hm⟩
    · intro hc
      refine cong_of_sub_mem C.X ?_
      rw [sub_zero, ← sub_add_cancel (y i) (∑ j, c i j • β j)]
      exact add_mem (hyc i) (sum_mem_of_coeff C.X β hβ _ hc)
  have hrow : ∀ PP ∈ Pg ∪ Q, ∀ i j, (Y PP i j = 0 ↔ Lev.bar (c i j) ∈ PP.asIdeal) := by
    intro PP hPP i j
    rw [hY PP hPP, Ideal.Quotient.eq_zero_iff_mem]
  have hdetU : ∀ PP ∈ Pg ∪ Q, IsUnit (topL T.rank (Y PP)).det → Lev.bar ct.det ∉ PP.asIdeal := by
    intro PP hPP hu hm
    have e : (ct.map ((Ideal.Quotient.mk PP.asIdeal).comp Lev.bar)).det =
        ((Ideal.Quotient.mk PP.asIdeal).comp Lev.bar) ct.det := (RingHom.map_det _ _).symm
    rw [hTop PP hPP, e, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hm] at hu
    exact not_isUnit_zero hu
  set L := mkLevel C Pg Q ξ h1 h2 h3 h4 β hβ hsp Lv0 with hL
  unfold Level.dat
  by_cases h : (∃ k : L.J, L.Red (fun i => y (Fin.castLE hn i)) k) ∧
      ∀ k : Fin S.rank, T.rank ≤ (k : ℕ) → GlobalTheory.SW.Cong C.X L.𝔪 (y k) 0
  · rw [dite_eq_left h]
    obtain ⟨k', hk'm, hk'c⟩ := h.1.choose_spec
    set κ := h.1.choose with hκdef
    have hκval : (κ.1 : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q)).val =
        ctᵀ.map (Ideal.Quotient.mk (liftI Pg Q)) := by
      rw [← hk'm]
      ext a b
      simp only [Matrix.map_apply, Matrix.transpose_apply]
      refine Ideal.Quotient.eq.2 ?_
      obtain ⟨s, hs, hm⟩ := cong_congr_left C.X (hyc (Fin.castLE hn b)) (hk'c b)
      have := hind (fun j => c (Fin.castLE hn b) j - k' j b)
        ⟨s, hs, by
          convert hm using 2
          simp only [sub_zero, sub_smul, Finset.sum_sub_distrib]
          rfl⟩ a
      rw [← neg_sub]
      exact neg_mem this
    have hJ := (jgrp_iff (κ.1 : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q)) ct hκval).1 κ.2
    have hlowc : ∀ i : Fin S.rank, T.rank ≤ (i : ℕ) → ∀ j, c i j ∈ liftI Pg Q :=
      fun i hi => (hcong0 i).1 (h.2 i hi)
    have hLow : ∀ PP ∈ Pg ∪ Q, LowZero T.rank (Y PP) :=
      fun PP hPP i j hi _ => (hrow PP hPP i j).2 (mem_liftI.1 (hlowc i hi j) PP hPP)
    have hdetQ : ∀ PP (hPP : PP ∈ Pg ∪ Q), conjRes Pg Q PP hPP
        (κ.1 : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q)).val.det = (topL T.rank (Y PP)).det := by
      intro PP hPP
      rw [hκval]
      exact (conjRes_det hPP ct).trans (congrArg Matrix.det (hTop PP hPP).symm)
    have hQc : ∀ PP ∈ Q, LowZero T.rank (Y PP) ∧ IsUnit (topL T.rank (Y PP)).det := fun PP hPP =>
      ⟨hLow PP (Finset.mem_union_right _ hPP), by
        rw [← hdetQ PP (Finset.mem_union_right _ hPP), ← Matrix.GeneralLinearGroup.val_det_apply]
        exact (Units.isUnit _).map _⟩
    have hK : omegaK Pg Y = 1 := by
      unfold omegaK
      rw [if_pos]
      intro PP hPP
      exact ⟨hLow PP (Finset.mem_union_left _ hPP), by rw [hTop PP (Finset.mem_union_left _ hPP)]; exact hJ PP hPP⟩
    rw [hK, one_mul]
    unfold omegaQ
    rw [dite_eq_left hQc]
    show ((lamHom Pg Q T.rank ξ (⟨κ.1, κ.2⟩ : Jgrp Pg Q T.rank) : ℂˣ) : ℂ) = _
    rw [lamHom_apply, Units.val_inv_eq_inv_val, Units.coe_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have e : Units.map (conjRes Pg Q PP.1 (Finset.mem_union_right _ PP.2)).toMonoidHom
        (Matrix.GeneralLinearGroup.det (κ.1 : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q))) =
        (hQc PP.1 PP.2).2.unit := by
      ext
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, IsUnit.unit_spec,
        Matrix.GeneralLinearGroup.val_det_apply]
      exact hdetQ _ _
    rw [e, _root_.zpow_neg_one]
  · rw [dite_eq_right h]
    symm
    by_contra hne
    have hK : omegaK Pg Y ≠ 0 := left_ne_zero_of_mul hne
    have hQ : omegaQ Q T.rank ξ (-1) Y ≠ 0 := right_ne_zero_of_mul hne
    have hKc : ∀ PP ∈ Pg, LowZero T.rank (Y PP) ∧ topL T.rank (Y PP) = 1 := by
      by_contra hc
      exact hK (by unfold omegaK; rw [if_neg hc])
    have hQc : ∀ PP ∈ Q, LowZero T.rank (Y PP) ∧ IsUnit (topL T.rank (Y PP)).det := by
      by_contra hc
      exact hQ (by unfold omegaQ; rw [dite_eq_right hc])
    apply h
    have hLow : ∀ PP ∈ Pg ∪ Q, LowZero T.rank (Y PP) := by
      intro PP hPP
      rcases Finset.mem_union.1 hPP with hP | hP
      exacts [(hKc PP hP).1, (hQc PP hP).1]
    have hlowc : ∀ i : Fin S.rank, T.rank ≤ (i : ℕ) → ∀ j, c i j ∈ liftI Pg Q := fun i hi j =>
      mem_liftI.2 fun PP hPP => (hrow PP hPP i j).1 (hLow PP hPP i j hi j.2)
    have hdet : IsUnit (ctᵀ.map (Ideal.Quotient.mk (liftI Pg Q))).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_transpose]
      refine isUnit_mk_liftI fun PP hPP => hdetU PP hPP ?_
      rcases Finset.mem_union.1 hPP with hP | hP
      · rw [(hKc PP hP).2, Matrix.det_one]
        exact isUnit_one
      · exact (hQc PP hP).2
    set κ : GL (Fin T.rank) (𝓞 D.host.E ⧸ liftI Pg Q) :=
      ((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit with hκ
    have hκval : κ.val = ctᵀ.map (Ideal.Quotient.mk (liftI Pg Q)) := IsUnit.unit_spec _
    have hκJ : κ ∈ Jgrp Pg Q T.rank := (jgrp_iff κ ct hκval).2 fun PP hPP => by
      rw [← hTop PP (Finset.mem_union_left _ hPP)]
      exact (hKc PP hPP).2
    exact ⟨⟨⟨κ, hκJ⟩, ctᵀ, hκval.symm, fun i => cong_of_sub_mem C.X (hyc (Fin.castLE hn i))⟩,
      fun k hk => (hcong0 k).2 (hlowc k hk)⟩

end GlobalTheory.LiftDat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeLieWordNormBound
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal

namespace GlobalTheory.SepReal.LieWords

theorem dR_eq_dAct {m : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : Mat m → (H →L[ℂ] H)) : dR π = GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π := by
  funext X w
  unfold dR GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.orbit
  congr 1

theorem one_le_of_bound {m : ℕ} (hm : 3 ≤ m) {lam : Fin m → ℝ} (hc : IsHCParam lam) {B : ℝ}
    (hB : ∀ a, |lam a| ≤ B) : 1 ≤ B := by
  have hint : ∀ a c : Fin m, a < c → 1 ≤ lam a - lam c := by
    intro a c hac
    obtain ⟨ka, hka⟩ := hc.2 a
    obtain ⟨kc, hkc⟩ := hc.2 c
    have e : lam a - lam c = ((ka - kc : ℤ) : ℝ) := by push_cast; linarith
    have hpos : (0 : ℝ) < ((ka - kc : ℤ) : ℝ) := by rw [← e]; linarith [hc.1 hac]
    have h1 : (0 : ℤ) < ka - kc := by exact_mod_cast hpos
    have h2 : (1 : ℝ) ≤ ((ka - kc : ℤ) : ℝ) := by exact_mod_cast h1
    linarith
  have h01 := hint ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.lt_def])
  have h12 := hint ⟨1, by omega⟩ ⟨2, by omega⟩ (by simp [Fin.lt_def])
  have a0 := abs_le.mp (hB ⟨0, by omega⟩)
  have a2 := abs_le.mp (hB ⟨2, by omega⟩)
  linarith [a0.1, a0.2, a2.1, a2.2]

theorem stepConst_le {m : ℕ} (hm : 3 ≤ m) {B : ℝ} (hB : 1 ≤ B) (P : ℕ) (hP : P ≤ m + 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst m (Real.sqrt B) P ≤ (8 * (m : ℝ) * B) ^ 2 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hB0 : (0 : ℝ) ≤ B := by linarith
  unfold GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst
  rw [Real.sq_sqrt hB0]
  have h12 : (m : ℝ) ^ (1 / 2 : ℝ) ≤ m := by
    calc (m : ℝ) ^ (1 / 2 : ℝ) ≤ (m : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = m := Real.rpow_one _
  have h32 : (m : ℝ) ^ (3 / 2 : ℝ) ≤ (m : ℝ) ^ 2 := by
    calc (m : ℝ) ^ (3 / 2 : ℝ) ≤ (m : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (m : ℝ) ^ 2 := Real.rpow_two _
  have hPr : (P : ℝ) ≤ m + 1 := by exact_mod_cast hP
  have a1 : (m : ℝ) ^ (1 / 2 : ℝ) * B ≤ m * B := mul_le_mul_of_nonneg_right h12 hB0
  have hmB : 1 ≤ (m : ℝ) * B := by nlinarith
  have a2 : (m : ℝ) * B ≤ (m * B) ^ 2 := by nlinarith
  have a3 : (m : ℝ) ^ 2 ≤ (m * B) ^ 2 := by
    have hB2 : 1 ≤ B ^ 2 := one_le_pow₀ hB
    rw [mul_pow]
    calc (m : ℝ) ^ 2 = (m : ℝ) ^ 2 * 1 := (mul_one _).symm
      _ ≤ (m : ℝ) ^ 2 * B ^ 2 := mul_le_mul_of_nonneg_left hB2 (sq_nonneg _)
  have a4 : 3 * (P : ℝ) ≤ 2 * (m : ℝ) ^ 2 := by nlinarith
  have e : (8 * (m : ℝ) * B) ^ 2 = 64 * (m * B) ^ 2 := by ring
  rw [e]
  nlinarith [sq_nonneg ((m : ℝ) * B)]

theorem rk_le {m : ℕ} (hm : 3 ≤ m) (ε : Fin m → Bool) :
    120 * (m : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 1000 * (m : ℝ) ^ 3 := by
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hrk : GlobalTheory.Count.rkR ε ≤ m := by
    unfold GlobalTheory.Count.rkR
    exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
  have h1 : ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hrk) (by norm_num)
  have h32 : (m : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ 2 := by
    calc (m : ℝ) ^ ((3 : ℝ) / 2) ≤ (m : ℝ) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = (m : ℝ) ^ 2 := Real.rpow_two _
  have h0 : 0 ≤ ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) := by positivity
  have h2 : 120 * (m : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (m : ℝ) * (m : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left (h1.trans h32) (by positivity)
  nlinarith

end GlobalTheory.SepReal.LieWords


open GlobalTheory.SepReal.LieWords in
theorem GlobalTheory.SepReal.lieBound : LieBound := by
  intro m ε lam B hm hc hgap hB H _ _ π hDS v₀ hv₀
  haveI : CompleteSpace H := hDS.1
  have hU : IsURepOn (UJset ε) π := hDS.2.2.1
  have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hgap2 : ∀ a b : Fin m, ε a ≠ ε b → 2 * (m : ℝ) < |lam a - lam b| := by
    intro a b hab
    have h := hgap a b hab
    nlinarith [sq_nonneg (m : ℝ)]
  have hK := GlobalTheory.Jet.MultGap.isKTypeOf_lowKSub m ε lam H π hc hDS hgap2
  have hZ := GlobalTheory.DSId.LowCharGap.lowChar m ε lam H π hc hDS _ hgap (rk_le hm ε)
  have hB1 : 1 ≤ B := one_le_of_bound hm hc hB
  have hb : ∀ a, |lam a| ≤ (Real.sqrt B) ^ 2 := by
    rw [Real.sq_sqrt (by linarith)]; exact hB
  have hSB := GlobalTheory.StepBoundOneRep.stepBound_of_eigen m ε H π lam (Real.sqrt B) hU hK hZ hb
  refine ⟨?_, ?_⟩
  · have hs := GlobalTheory.StepBoundOneRep.smooth_of_mem_lowKSub ε lam π hU hK v₀ hv₀.2
    have hJ : IsUnit (Jm ε) := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse (Jm_mul_self ε))
    exact (GlobalTheory.SmChart.smV_iff_smoothOnH hJ hU.1 v₀).2 hs
  · rw [dR_eq_dAct]
    intro l
    induction l with
    | nil => intro _ _; simp [hv₀.1]
    | cons X l ih =>
      intro hl hlen
      have hX : inG ε X := hl X List.mem_cons_self
      have hl' : ∀ Y ∈ l, Y ∈ lieOf (Jm ε) := fun Y hY => hl Y (List.mem_cons_of_mem _ hY)
      have hlen' : l.length ≤ m + 2 := by simp at hlen; omega
      have hmem : l.foldr (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π) v₀ ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam π l.length :=
        Submodule.subset_span ⟨l, v₀, le_rfl, hl', hv₀.2, rfl⟩
      have h1 := (hSB l.length).2.2.2 X hX _ hmem
      have hcst := stepConst_le hm hB1 l.length (by simp at hlen; omega)
      have hrest := ih hl' hlen'
      have hsq : Real.sqrt (hs X) = hsn X := rfl
      have hh : 0 ≤ hsn X := Real.sqrt_nonneg _
      rw [List.foldr_cons, List.map_cons, List.prod_cons]
      calc ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π X (l.foldr (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π) v₀)‖
          ≤ Real.sqrt (hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst m (Real.sqrt B) l.length *
              ‖l.foldr (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct π) v₀‖ := h1
        _ ≤ ((8 * (m : ℝ) * B) ^ 2 * hsn X) * (l.map fun X => (8 * (m : ℝ) * B) ^ 2 * hsn X).prod := by
          rw [hsq]
          refine mul_le_mul ?_ hrest (norm_nonneg _) (by positivity)
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right hcst hh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapConjSmallerUnitaryFlagUnipotentHaar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FlagModulus

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

theorem wittHyperbolic_conj_smallerGroup_coords (d : HypDec S S₀ ρ) (h : GA D S₀) (u : GL (Fin ρ) (AE D)) (b : Mx D ρ S₀.rank)
    (c : skewA D ρ) : d.emb0 h * (d.levi u * (d.nB b * d.nC c)) * (d.emb0 h)⁻¹ =
      d.levi u * (d.nB (b ⬝ mt S₀ h⁻¹) * d.nC c) := by
  simp only [mul_assoc]
  rw [← mul_assoc (d.emb0 h) (d.levi u), d.wittHyperbolic_anisotropic_commute_levi h u, mul_assoc, ← mul_assoc (d.emb0 h) (d.nB b),
    d.wittHyperbolic_anisotropic_conj_nB b h, mul_assoc, ← mul_assoc (d.emb0 h) (d.nC c), d.wittHyperbolic_anisotropic_commute_nC c h, mul_assoc, mul_inv_cancel,
    mul_one]

theorem map_conj_smallerUnitary_flagUnipotent_haar : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (ν : Measure (flagN d)),
    ν.IsHaarMeasure → ∀ h : GA D S₀,
      ν.map (fun n : flagN d => d.emb0 h * n.1 * (d.emb0 h)⁻¹) = ν.map Subtype.val := by
  intro D S S₀ ρ d ν hν h
  haveI : BorelSpace (GA D S) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ S₀.rank) := ⟨rfl⟩
  obtain ⟨hlc, hsc, -, -⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S (isIsoSub_e d)
  obtain ⟨μ, lB, lC, hμ, hB, hC, sμ, sB, sC, hΦ, ν₀, hν₀, hmap⟩ := GlobalTheory.HaarCoords.haar_coords D S S₀ ρ d
  have hk : ν = Measure.haarScalarFactor ν ν₀ • ν₀ := Measure.isMulLeftInvariant_eq_smul ν ν₀
  have hconj : Measurable (fun g : GA D S => d.emb0 h * g * (d.emb0 h)⁻¹) :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hval : Measurable (Subtype.val : flagN d → GA D S) := measurable_subtype_coe
  have hf : Measurable (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h⁻¹) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hT : Measurable (Prod.map (id : UX D ρ → UX D ρ)
      (Prod.map (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h⁻¹) (id : skewA D ρ → skewA D ρ))) :=
    measurable_id.prodMap (hf.prodMap measurable_id)
  have key : ν₀.map (fun n : flagN d => d.emb0 h * n.1 * (d.emb0 h)⁻¹) = ν₀.map Subtype.val := by
    have e1 : (fun n : flagN d => d.emb0 h * n.1 * (d.emb0 h)⁻¹) =
        (fun g : GA D S => d.emb0 h * g * (d.emb0 h)⁻¹) ∘ Subtype.val := rfl
    rw [e1, ← Measure.map_map hconj hval, hmap, Measure.map_map hconj hΦ]
    have e2 : (fun g : GA D S => d.emb0 h * g * (d.emb0 h)⁻¹) ∘
        (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) =
        (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) ∘
          Prod.map (id : UX D ρ → UX D ρ)
            (Prod.map (fun b : Mx D ρ S₀.rank => b ⬝ mt S₀ h⁻¹) (id : skewA D ρ → skewA D ρ)) :=
      funext fun p => wittHyperbolic_conj_smallerGroup_coords d h p.1.1 p.2.1 p.2.2
    rw [e2, ← Measure.map_map hΦ hT]
    congr 1
    rw [← Measure.map_prod_map _ _ measurable_id (hf.prodMap measurable_id), ← Measure.map_prod_map _ _ hf measurable_id,
      Measure.map_id, Measure.map_id, GlobalTheory.AdelicModulus.RowMat.map_mul_mt_eq D S₀ ρ lB hB h⁻¹]
  rw [hk, Measure.map_smul, Measure.map_smul, key]
  · exact hval.aemeasurable
  · exact (hconj.comp hval).aemeasurable

end GlobalTheory.FlagModulus

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemConjugatePlacesProductIdealOfForallConjPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftLevel.InfMem

theorem conjI_eq_comap (D : D7) (P : Ideal (𝓞 D.host.E)) : conjI P = P.comap GlobalTheory.SW.Lev.bar := by
  ext a; rw [GlobalTheory.SW.Lev.mem_conjI, Ideal.mem_comap]

theorem bar_surj (D : D7) : Function.Surjective (GlobalTheory.SW.Lev.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
  fun a => ⟨GlobalTheory.SW.Lev.bar a, GlobalTheory.SW.Lev.bar_bar a⟩

theorem conjI_isMaximal (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E) : (conjI PP.asIdeal).IsMaximal := by
  rw [conjI_eq_comap]
  haveI := PP.isMaximal
  exact Ideal.comap_isMaximal_of_surjective _ (bar_surj D)

theorem conjI_inj (D : D7) {PP PP' : Formalism.L2.DIV.Pl D.host.E} (h : conjI PP.asIdeal = conjI PP'.asIdeal) : PP = PP' := by
  apply HeightOneSpectrum.ext
  ext a
  have := congrArg (fun I => GlobalTheory.SW.Lev.bar a ∈ I) h
  simp only [GlobalTheory.SW.Lev.mem_conjI, GlobalTheory.SW.Lev.bar_bar] at this
  exact Iff.of_eq this

theorem mem_liftI (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (x : 𝓞 D.host.E)
    (hx : ∀ PP ∈ Pg ∪ Q, x ∈ conjI PP.asIdeal) : x ∈ GlobalTheory.LiftLevel.liftI Pg Q := by
  unfold GlobalTheory.LiftLevel.liftI
  rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · simp only [Submodule.mem_iInf]
    exact hx
  · intro PP _ PP' _ hne
    have hne' : conjI PP.asIdeal ≠ conjI PP'.asIdeal := fun h => hne (conjI_inj D h)
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne (conjI_isMaximal D PP) (conjI_isMaximal D PP') hne'

theorem main : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (x : 𝓞 D.host.E), (∀ PP ∈ Pg ∪ Q, x ∈ conjI PP.asIdeal) → x ∈ GlobalTheory.LiftLevel.liftI Pg Q := fun D Pg Q x hx => mem_liftI D Pg Q x hx

end GlobalTheory.LiftLevel.InfMem
end

