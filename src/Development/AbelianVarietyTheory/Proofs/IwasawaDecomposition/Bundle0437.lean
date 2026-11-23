module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianFormLastCoordinateUniformizerVectorSelf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtMMulVecFix
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0428
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0426
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsWeilOnOfCoord
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Formalism.UnipotentAdelicQuotients.Bundle0002
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ClosedBallValuationSubringToSubring

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TupleLayerCompatibilitiesOfXPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.Col2.TC.tupleLayer_compatibility : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (inQ : I.ι → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)) (T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ) (J : Formalism.L2.Herm.TwChJointS T H) (W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F) (Lv : SymmetricTwistedLevelData W), (∀ a v, inQ a v ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → I.StdW l Z l0 W → I.StdLv l Z l0 Lv → (∀ u a (ha : a ≠ I.mu0) (h1 : 1 ≤ B.R.m), ∃ k, I.Reads u a B.R.m (T.chOf u a B.R.m) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.Lb)
      (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.U) (fun β => (W.ch u a ha B.R.m h1 le_rfl β).lev.chi)
      (fun c => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).y ⟨c, rfl⟩).1)
      (fun c s => ((W.ch u a ha B.R.m h1 le_rfl (T.chOf u a B.R.m c)).stabI ⟨c, rfl⟩ s).1) k ∧
      ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
        IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
        PtOf (g * k β) (tilF I.sel (I.tup a) u d)) → ∃ (Pt : TwPTiedS Lv) (E : TwPEvzS Pt), TwPAtGS Pt ∧ I.StdP l Z l0 Pt E := by
  intro B X I hI hP l Z l0 inQ H F T J W Lv hQ hF hW hLv hTop
  have hQ' : ∀ a v, v ∈ T.Q a ↔ I.UnderQ a v := fun a v => (T.Q_iff a v).trans (hQ a v)
  have hC := fun u a => GlobalTheory.T.tuplePrimedSpaceClasses_level_and_comparison I hI hP l Z u a (T.Q a) (F u).clsP (hQ' a) (J.Q_off u a) (hF u).1.what₂
  choose K hLb hfin hrd hU hchi using hC
  have hV := fun u a => _root_.GlobalTheory.Mem.Col2.TwP.forms_tw I hI hP l Z u a (T.Q a) (K u a) (hQ' a) (J.Q_off u a) (hrd u a)
  choose V hN hE using hV
  choose k hk hkT using hTop
  have hTil := fun u a ha h1 => GlobalTheory.Mem.Col2.TwP.til_tw I hI hP l Z hF hW hLv u a ha h1 (K u a) (hrd u a) (hk u a ha h1) (hkT u a ha h1)
  choose Tl hz hev using hTil
  choose jM hj0 hj1 hj2 hj3 hj4 using fun u a => GlobalTheory.Mem.Col2.PerConj.period_conj I hI hP l Z u a
  let Pt : TwPTiedS Lv :=
    { cls := fun u a _ => K u a
      Lb := fun u a _ => hLb u a
      chi_fin := fun u a _ => hfin u a
      val := fun u a _ => V u a
      norm := fun u a _ => hN u a
      til := fun u a ha h1 => Tl u a ha h1 }
  let E : TwPEvzS Pt :=
    { eWz := fun u a => LinearEquiv.refl ℂ _
      evz := fun u a ha h1 φ c s s' hs => hev u a ha h1 φ c s s' hs
      jM := jM
      per := fun u a _ => ⟨hj1 u a, hj2 u a, hj3 u a⟩ }
  refine ⟨Pt, E, ⟨fun u a _ v hv => hU u a v hv, fun u a _ κ κ' h h' => hchi u a κ κ' h h'⟩, ⟨fun u a _ => hrd u a, fun u a _ z c s s' h => hE u a z c s s' h, fun u a ha h1 => hz u a ha h1, fun u a z => rfl⟩⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilOnEqExOfKnownTheorem
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.OrientedCoord GlobalTheory.Mem.WeilTransport
open scoped TensorProduct

namespace GlobalTheory.Mem.WeilEqRank

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isCoord_coord (S T : HSp D) (hr : S.rank ≤ T.rank) : IsCoord S T S T (coord S T) := {
  cont := continuous_coord S T
  cont' := continuous_coord_symm S T
  sympl := symplOH_eq S T hr
  rat x := by
    constructor
    · rintro ⟨γ, rfl⟩
      exact ⟨(γ * S.gram⁻¹)ᵀ, (coord_ratW S T γ).symm⟩
    · rintro ⟨γ, hγ⟩
      have hγ' : ratW S T γ = coord S T x := hγ
      refine ⟨γᵀ * S.gram, ?_⟩
      change ratW T S _ = x
      rw [← coord_symm_ratW, hγ', AddEquiv.symm_apply_apply]
  inf x := ⟨coord_map_zero S T _ x, fun h => by
    simpa only [AddEquiv.symm_apply_apply] using coord_symm_map_zero S T _ _ h⟩
  fin x := ⟨coord_map_zero S T _ x, fun h => by
    simpa only [AddEquiv.symm_apply_apply] using coord_symm_map_zero S T _ _ h⟩
  part a x h i j := by
    show a * ∑ k, x j k * incA D (S.gram⁻¹ k i) = ∑ k, x j k * incA D (S.gram⁻¹ k i)
    simp only [Finset.mul_sum, ← mul_assoc, h] }

theorem weilOnEqEx_of_weilRepresentation : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ D : D7, WeilOnEqEx D := by
  intro hP D ψ hψ V W χ χ' ⟨hr, h1, h2, h3, h4⟩
  obtain ⟨om, H⟩ := hP D ψ V W χ χ' hψ h1.1 h2.1 h3 h4
  refine exists_isWeilOn_of_coord (isCoord_coord V W hr.le) H (MonoidHom.id _) continuous_id
    (fun g h x => (GlobalTheory.OrientedSmall.bridgeSmall D V W hr.le).2 g h x) (fun _ a _ b => ⟨a, b⟩)
    fun e g h hg hh x y hx hy => ⟨x, y, hg, hh, hx, hy, ?_⟩
  unfold splitFacO splitFac
  rw [if_pos hr.le]

end GlobalTheory.Mem.WeilEqRank

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylLatticeDualInvariantUnitIff
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DelWSub

def intBall (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] := GlobalTheory.ClosedBallValuationSubring.closedBallSubring ℂ_[p]

theorem eval_rowAct {R : Type} [CommRing R] {N : ℕ} (G Y : Matrix (Fin N) (Fin N) R)
    (P : MvPolynomial (Fin N × Fin N) R) :
    MvPolynomial.eval (fun k => Y k.1 k.2) (Formalism.GradedWeylDivisibility.rowAct R G P) =
      MvPolynomial.eval (fun k => (G * Y) k.1 k.2) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [map_mul, MvPolynomial.eval_mul, MvPolynomial.eval_mul, hp]
    simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]

theorem weyl_eq (N : ℕ) (ν : Fin N → ℕ) :
    WeylLatticeDuality.weyl ℤ N N le_rfl ν = Formalism.GradedWeylDivisibility.weyl ℤ N N le_rfl ν := rfl

theorem rowSub_expand (p : ℕ) [Fact p.Prime] {N : ℕ} (ν : Fin N → ℕ)
    (g : Matrix (Fin N) (Fin N) ℂ_[p]) (hg : ∀ a b, ‖g a b‖ ≤ 1)
    (f : MvPolynomial (Fin N × Fin N) ℤ) (hf : f ∈ WeylLatticeDuality.weyl ℤ N N le_rfl ν) :
    ∃ (s : Finset (List (Fin N × Fin N × ℕ))) (o : List (Fin N × Fin N × ℕ) → ℂ_[p]),
      (∀ w, ‖o w‖ ≤ 1) ∧ ∀ Y : Matrix (Fin N) (Fin N) ℂ_[p],
        MvPolynomial.eval (fun k => (g * Y) k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p]) f) =
          ∑ w ∈ s, o w * MvPolynomial.eval (fun k => Y k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p])
            (WeylLatticeDuality.applyWord ℤ w (WeylLatticeDuality.hw ℤ le_rfl ν))) := by
  classical
  let O := intBall p
  let gO : Matrix (Fin N) (Fin N) O := fun a b => ⟨g a b, hg a b⟩
  have hgO : gO.map O.subtype = g := by ext a b; rfl
  have hfO : MvPolynomial.map (Int.castRingHom O) f ∈ Formalism.GradedWeylDivisibility.weyl O N N le_rfl ν :=
    GlobalTheory.WeylRowAll.map_mem_weyl (Int.castRingHom O) le_rfl ν f (by rw [← weyl_eq]; exact hf)
  have hQ := GlobalTheory.WeylRowAll.rowAct_mem_weyl O le_rfl ν gO _ hfO
  unfold Formalism.GradedWeylDivisibility.weyl at hQ
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hQ
  refine ⟨c.support, fun w => (c w : ℂ_[p]), fun w => (c w).2, fun Y => ?_⟩
  have h1 : MvPolynomial.map (Int.castRingHom ℂ_[p]) f =
      MvPolynomial.map O.subtype (MvPolynomial.map (Int.castRingHom O) f) := by
    rw [MvPolynomial.map_map]; congr 1
  have hterm : ∀ w, MvPolynomial.map O.subtype (Formalism.GradedWeylDivisibility.applyWord O w (Formalism.GradedWeylDivisibility.hw O le_rfl ν)) =
      MvPolynomial.map (Int.castRingHom ℂ_[p])
        (WeylLatticeDuality.applyWord ℤ w (WeylLatticeDuality.hw ℤ le_rfl ν)) := by
    intro w
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
    show _ = MvPolynomial.map _ (Formalism.GradedWeylDivisibility.applyWord ℤ w (Formalism.GradedWeylDivisibility.hw ℤ le_rfl ν))
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, ← eval_rowAct, ← hgO, ← GlobalTheory.WeylRowAll.map_rowAct, ← hc, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, hterm]
  rfl

def act (p : ℕ) [Fact p.Prime] (T : Type) (N : ℕ) (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) :
    ((T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) →+ ((T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) where
  toFun F := fun y => c * F (fun τ => g τ * y τ)
  map_zero' := by funext y; simp
  map_add' F G := by funext y; simp [mul_add]

theorem mem_delW_act (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ)
    (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]) (hg : ∀ τ a b, ‖g τ a b‖ ≤ 1) (hc : ‖c‖ ≤ 1)
    (F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p]) (hF : F ∈ WeylLatticeDuality.DelW p T N ν) :
    (fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν := by
  classical
  refine (AddSubgroup.closure_le ((WeylLatticeDuality.DelW p T N ν).comap (act p T N g c))).2 ?_ hF
  rintro _ ⟨r, f, hr, hf, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_comap]
  choose s o ho hexp using fun τ => rowSub_expand p (ν τ) (g τ) (hg τ) (f τ) (hf τ)
  have heq : act p T N g c (fun y => r * ∏ τ, MvPolynomial.eval (fun k : Fin N × Fin N => y τ k.1 k.2)
      (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f τ))) =
      ∑ x ∈ Fintype.piFinset s, fun y => (c * r * ∏ τ, o τ (x τ)) *
        ∏ τ, MvPolynomial.eval (fun k : Fin N × Fin N => y τ k.1 k.2) (MvPolynomial.map (Int.castRingHom ℂ_[p])
          (WeylLatticeDuality.applyWord ℤ (x τ) (WeylLatticeDuality.hw ℤ le_rfl (ν τ)))) := by
    funext y
    rw [Finset.sum_apply]
    show c * (r * ∏ τ, MvPolynomial.eval (fun k : Fin N × Fin N => (g τ * y τ) k.1 k.2)
      (MvPolynomial.map (Int.castRingHom ℂ_[p]) (f τ))) = _
    simp only [hexp]
    rw [Finset.prod_univ_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.prod_mul_distrib]; ring
  rw [heq]
  refine AddSubgroup.sum_mem _ fun x _ => AddSubgroup.subset_closure
    ⟨c * r * ∏ τ, o τ (x τ), fun τ => WeylLatticeDuality.applyWord ℤ (x τ) (WeylLatticeDuality.hw ℤ le_rfl (ν τ)),
      ?_, fun τ => Submodule.subset_span ⟨x τ, rfl⟩, rfl⟩
  rw [norm_mul, norm_mul, norm_prod]
  exact mul_le_one₀ (mul_le_one₀ hc (norm_nonneg _) hr) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun τ _ => ho τ _)

theorem exists_int_inv (p : ℕ) [Fact p.Prime] {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ_[p])
    (hg : ∀ a b, ‖g a b‖ ≤ 1) (hdet : ‖g.det‖ = 1) :
    ∃ h : Matrix (Fin N) (Fin N) ℂ_[p], (∀ a b, ‖h a b‖ ≤ 1) ∧ g * h = 1 := by
  classical
  let O := intBall p
  let gO : Matrix (Fin N) (Fin N) O := fun a b => ⟨g a b, hg a b⟩
  have hmap : gO.map O.subtype = g := by ext a b; rfl
  have hd : O.subtype gO.det = g.det := by rw [RingHom.map_det]; rfl
  have hdne : g.det ≠ 0 := norm_ne_zero_iff.1 (by rw [hdet]; exact one_ne_zero)
  have hu : IsUnit gO.det := by
    refine IsUnit.of_mul_eq_one (⟨g.det⁻¹, ?_⟩ : O) ?_
    · show ‖g.det⁻¹‖ ≤ 1
      rw [norm_inv, hdet, inv_one]
    · apply Subtype.ext
      show O.subtype gO.det * g.det⁻¹ = 1
      rw [hd, mul_inv_cancel₀ hdne]
  refine ⟨gO⁻¹.map O.subtype, fun a b => (gO⁻¹ a b).2, ?_⟩
  rw [← hmap, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]

theorem delW_rowSub : ∀ (p : ℕ) [Fact p.Prime] (T : Type) [Fintype T] (N : ℕ) (ν : T → Fin N → ℕ) (g : T → Matrix (Fin N) (Fin N) ℂ_[p]) (c : ℂ_[p]), (∀ τ a b, ‖g τ a b‖ ≤ 1) → (∀ τ, ‖(g τ).det‖ = 1) → ‖c‖ = 1 → ∀ F : (T → Matrix (Fin N) (Fin N) ℂ_[p]) → ℂ_[p], F ∈ WeylLatticeDuality.DelW p T N ν ↔ (fun y => c * F (fun τ => g τ * y τ)) ∈ WeylLatticeDuality.DelW p T N ν := by
  intro p _ T _ N ν g c hg hdet hc F
  constructor
  · exact mem_delW_act p T N ν g c hg hc.le F
  · intro h
    have hinv := fun τ => exists_int_inv p (g τ) (hg τ) (hdet τ)
    choose hm hmI hmul using hinv
    have hc0 : c ≠ 0 := norm_ne_zero_iff.1 (by rw [hc]; exact one_ne_zero)
    have := mem_delW_act p T N ν hm c⁻¹ hmI (by rw [norm_inv, hc, inv_one]) _ h
    convert this using 1
    funext y
    rw [inv_mul_cancel_left₀ hc0]
    congr 1
    funext τ
    simp [← Matrix.mul_assoc, hmul]

end GlobalTheory.DelWSub
end
end

