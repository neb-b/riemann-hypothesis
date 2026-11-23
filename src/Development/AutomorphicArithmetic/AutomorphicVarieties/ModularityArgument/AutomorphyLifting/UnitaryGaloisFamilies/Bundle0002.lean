module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0058
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CharpolyEqProd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0748
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0750
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0240
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.PlainRec

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.FrobTotT
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.PRep GlobalTheory.SmGL
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Gu

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem unr_lpSum {x y : WD h} (hx : x.unr) (hy : y.unr) : (x.lpSum y).unr := by
  induction x using Quotient.inductionOn with | h a => ?_
  induction y using Quotient.inductionOn with | h b => ?_
  have ha : a.2.Unr := hx
  have hb : b.2.Unr := hy
  show (WD.mk (a.2.sum b.2)).unr
  rw [WD.unr_mk]
  refine ⟨?_, fun σ => ?_⟩
  · rw [WDRep.sum_N, ha.1, hb.1, LinearMap.prodMap_zero]
  · rw [WDRep.sum_ρ, ha.2, hb.2]; exact LinearMap.prodMap_one

private theorem sumList_spec (g : Weil h) : ∀ (c : ℕ) (f : Fin c → WD h) (M : Fin c → Multiset ℂ),
    (∀ i, (f i).unr ∧ (f i).charPol g = ((M i).map fun b => X - C b).prod) →
    (sumList (List.ofFn f)).unr ∧ (sumList (List.ofFn f)).charPol g = ((∑ i, M i).map fun b => X - C b).prod := by
  intro c
  induction c with
  | zero =>
    intro f M _
    have e : sumList (List.ofFn f) = WD.lpZero (h := h) := by simp [sumList]
    rw [e, WD.lpZero, WD.unr_mk, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd]
    exact ⟨WDRep.unr_diag _, by simp⟩
  | succ c ih =>
    intro f M H
    obtain ⟨h1, h2⟩ := ih (fun i => f i.succ) (fun i => M i.succ) fun i => H i.succ
    have e : sumList (List.ofFn f) = (f 0).lpSum (sumList (List.ofFn fun i => f (Fin.succ i))) := by
      rw [List.ofFn_succ]; rfl
    rw [e, WD.charPol_lpSum, h2, (H 0).2, Fin.sum_univ_succ, Multiset.map_add (f := _), Multiset.prod_add]
    exact ⟨unr_lpSum (H 0).1 h1, rfl⟩

private theorem rec_eq_diagV {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecV h rc) {a : ℕ}
    {σ : IrrRep (GL (Fin a) (w.adicCompletion E))} {α : Fin a → ℂˣ} (hα : HasSatake σ.ρ α) :
    rc (cls σ) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) := by
  obtain ⟨_, _, _, L⟩ := H
  have φ := equivRep σ
  exact L.sat (cls σ) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
    (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩

private theorem rec_tw_diag {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecV h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) (s : ℝ) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      (rc (cl σ)).lpTw s = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w s) := by
  have hsph : IsSpherical (ParLaws.toRep σ).ρ := by
    have := hB.1
    unfold IsSpherical IsSphericalFor
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact this
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.main UpperTheory.Zero.LLC.Pr.bz (w.adicCompletion E) n
    ⟨_, σ.ρ, σ.smooth, σ.irred⟩ hsph
  refine ⟨α, hB.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα), ?_⟩
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    rec_eq_diagV H (σ := ParLaws.toRep σ) hα
  rw [e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]

private theorem val_inv_eq (n d k : ℕ) (a : ℂˣ) :
    (((a⁻¹ * qPow w ((ex n d k : ℝ) / 2) : ℂˣ) : ℂ)) ^ (-1 : ℤ) =
      ((((normV w : ℕ) : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) *
        ((a * qPow w ((k : ℝ) - ((d : ℝ) - 1) / 2) : ℂˣ) : ℂ) := by
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (zero_lt_one.trans (one_lt_normV w)).ne'
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv,
    coe_qPow, ← Complex.cpow_neg, Units.val_mul, coe_qPow, mul_left_comm, Complex.ofReal_natCast, ← Complex.cpow_add _ _ hq]
  congr 2
  simp only [ex]
  push_cast
  ring

private theorem totPar_spec {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecV h rc) (n c : ℕ) (a d : Fin c → ℕ)
    (ρ : ∀ i, SmIrr (GL (Fin (a i)) (w.adicCompletion E))) (S : Fin c → Multiset ℂˣ)
    (hS : ∀ i, GlobalTheory.LFun.HasSatGL w (ρ i).ρ (S i)) (g : Weil h) (hg : deg g = -1) :
    (totPar n d ρ A h rc).unr ∧
      (totPar n d ρ A h rc).charPol g = ((algSat n (normV w) (satTot w d S)).map fun b => X - C b).prod := by
  have e : algSat n (normV w) (satTot w d S) = ∑ i, ∑ k : Fin (d i),
      algSat n (normV w) ((S i).map (· * qPow w (((k : ℕ) : ℝ) - ((d i : ℝ) - 1) / 2))) := by
    have hm : ∀ {α β ι : Type} (f : α → β) (s : Finset ι) (M : ι → Multiset α),
        (∑ i ∈ s, M i).map f = ∑ i ∈ s, (M i).map f := fun f s M => map_sum (Multiset.mapAddMonoidHom f) M s
    simp only [algSat, satTot, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton, hm]
  rw [e]
  refine sumList_spec g c _ _ fun i => sumList_spec g (d i) _ _ fun k => ?_
  obtain ⟨α, hα, e⟩ := rec_tw_diag H (ρ i) (S i) (hS i) ((ex n (d i) k : ℝ) / 2)
  rw [e, hα, WD.unr_mk, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, hg]
  refine ⟨WDRep.unr_diag _, ?_⟩
  simp only [val_inv_eq, algSat, Multiset.map_map, Multiset.pure_def, Multiset.bind_def, Multiset.bind_singleton]
  rfl

end UpperTheory.V.Z.Win.Gu

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.FrobTwT
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win.Gu.FrobTwTAux

open Polynomial GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands UpperTheory.Zero.LLC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem tw_diag (X : ExtraV) {rc : IrrGL (k := w.adicCompletion E) → WD h} (H : IsRecT h rc) {n : ℕ}
    (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B) (t : ℝ) :
    ∃ α : Fin n → ℂˣ, B = Finset.univ.val.map α ∧
      (rc (cl σ)).lpTw t = WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w t) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)
  refine ⟨α, hαB.symm, ?_⟩
  have φ := IrrGL.equivOf σ.ρ σ.smooth σ.irred
  obtain ⟨a, ha, ε, L⟩ := X E Ω A w h rc H
  have e : rc (IrrGL.of σ.ρ σ.smooth σ.irred) = WD.mk (WDRep.diag h fun i => (α i)⁻¹) :=
    L.sat (IrrGL.of σ.ρ σ.smooth σ.irred) α ⟨IrrRep.irr _, fixed_ne_bot_of_equiv φ hα.2.1,
      (IsSubquotient.of_surjective φ.toIntertwiningMap φ.toLinearEquiv.surjective).trans hα.2.2⟩
  rw [cl, e, WD.lpTw_mk]
  refine WD.sound ⟨.refl _ _, fun g v => funext fun i => ?_, fun v => rfl⟩
  simp [mul_zpow, mul_comm, mul_left_comm, mul_assoc]

private theorem val_tw (t : ℝ) (x : ℂˣ) :
    (((x⁻¹ * qPow w t : ℂˣ) : ℂ)) ^ (-1 : ℤ) = (x : ℂ) * ((normV w : ℕ) : ℂ) ^ (-(t : ℂ)) := by
  rw [zpow_neg_one, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val, inv_inv, coe_qPow, ← Complex.cpow_neg]

end UpperTheory.V.Z.Win.Gu.FrobTwTAux

open UpperTheory.V.Z.Win.Gu.FrobTwTAux in
theorem UpperTheory.V.Z.Win.Gu.frobTwT :
    ExtraV → GdLaws → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G E Ω →* GL (Fin a) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → ∀ t : ℝ, (ParAtT ι r w fun _ _ rc => (rc (cl σ)).lpTw t) → FrobEig ι r w (B.map fun α : ℂˣ => (α : ℂ) * ((normV w : ℕ) : ℂ) ^ (-(t : ℂ))) := by
  intro X hG E Ω _ _ _ _ _ l _ ι a r w hl σ B hB t H A h
  obtain ⟨rc, hrec⟩ := UpperTheory.Zero.LLC.recTExists E Ω A w h
  obtain ⟨α, rfl, e⟩ := tw_diag X hrec σ B hB t
  have hu : (WD.mk (WDRep.diag h fun i => (α i)⁻¹ * qPow w t)).unr := (WD.unr_mk _).2 (WDRep.unr_diag _)
  have hg : UpperTheory.V.Z.Win.Gd ((rc (cl σ)).lpTw t) := by
    rw [e]
    exact (hG E Ω A w h).2.2.2 _ hu
  have hk : WDT ι r ((rc (cl σ)).lpTw t) := (H A h rc hrec).1 hl
  have hx := hk.isWDOf hg
  have hw := (hx.wdOf_eq hl).trans e
  obtain ⟨t', ht, φ, hφ, N, b, hN, -⟩ := hx
  refine ⟨(hN.unr_wdOf_iff hl ht ι).1 (by rw [hw]; exact hu), fun s hs => ?_⟩
  have hd : deg (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h) = 1 := deg_eq_one_iff.2 hs
  have := hN.charPol_wdOf hl ht ι (⟨s, mem_Weil_of_isFrob h hs⟩ : Weil h)⁻¹
  rw [hw, WD.charPol_mk, WDRep.diag_ρ, charpoly_diagEnd, deg_inv, hd] at this
  refine this.symm.trans ?_
  simp only [val_tw, Multiset.map_map]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.PlainGd
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Af.Gu
open UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


namespace UpperTheory.V.Z.Win.Gu.PrincipalSeriesDeterminant

private theorem equiv_prinSeries {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V)
    (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ i, IsSmoothChar (ξ i)) (hs : HasSupport ρ (GlobalTheory.RoadU.chars ξ hξ))
    (hu : GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ξ hξ)) : Nonempty (ρ.Equiv (prinSeries ξ)) := by
  obtain ⟨hi, hq⟩ := (UpperTheory.Gal.LocD.ofSupport_holds k n V ρ ξ hξ).1 hs
  let y : Fin n → IrrGL (k := k) := fun i => IrrGL.ofChar (ξ i) (hξ i)
  have hy : ∀ i, (y i).IsCusp := fun i => IrrGL.isCusp_ofChar _ _
  have hd : ∑ i, (y i).1 = n := by simp [y, IrrGL.ofChar]
  have hmem : ∀ i, y i ∈ GlobalTheory.RoadU.chars ξ hξ := fun i => Multiset.mem_map_of_mem _ (Finset.mem_univ i)
  have hP : (prodIrr y hd).IsIrreducible :=
    GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (y i) (hy i)) y hd
      (fun i j => GlobalTheory.CompanionTheory.BZPair.not_linked_single (hy i) (hy j) (hu _ (hmem j) _ (hmem i)) (hu _ (hmem i) _ (hmem j)))
      (fun i => (single_spec (hy i)).2.1)
  let e₀ := Equiv.sigmaUnique (Fin n) fun _ => Fin 1
  obtain ⟨p⟩ := (Placing.parInd_jac_placing k _ _ _ e₀ (stdBlocks (fun i => (y i).1) hd) _).1
    (piTensor fun i => detRep (Fin 1) (ξ i))
  have hM : (multiProd e₀ fun i => detRep (Fin 1) (ξ i)).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv
      (p.trans (multiProdEquiv (stdBlocks (fun i => (y i).1) hd)
        fun i => equivRep (IrrRep.det (Fin 1) (ξ i) (hξ i)))).symm hP
  haveI := nontrivial_of_irreducible hM
  haveI : Nontrivial (IndSp _ _) := by
    obtain ⟨S, f, hf⟩ := GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries e₀ ξ
    have := hf.nontrivial
    exact Subtype.val_injective.nontrivial (α := S.toSubmodule)
  have equiv_of_isSubquotient_local {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
      [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) [Nontrivial W]
      (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
    obtain ⟨S, f, hf⟩ := h
    obtain ⟨y, hy⟩ := exists_ne (0 : W)
    obtain ⟨v, rfl⟩ := hf y
    haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
    rcases eq_bot_or_eq_top S with rfl | rfl
    · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy
    let F : ρ.IntertwiningMap σ := f.comp (topEquiv ρ).symm.toIntertwiningMap
    have hs : Function.Surjective F := hf.comp (topEquiv ρ).symm.toLinearEquiv.surjective
    refine ⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩
    haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
    rcases eq_bot_or_eq_top F.ker with h | h
    · have : x ∈ F.ker := hx
      rw [h] at this
      exact this
    · have : v.1 ∈ F.ker := by rw [h]; trivial
      exact absurd this hy
  
  obtain ⟨e⟩ := equiv_of_isSubquotient_local (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n ξ) hM
  obtain ⟨f⟩ := hq.nonempty_equiv hi (GlobalTheory.Parabolic.isIrreducible_of_equiv e hM)
  exact ⟨f.symm⟩

end UpperTheory.V.Z.Win.Gu.PrincipalSeriesDeterminant

open UpperTheory.V.Z.Win.Gu.PrincipalSeriesDeterminant in
theorem UpperTheory.V.Z.Win.Gu.plainGd :
    PlainGd := open scoped commutatorElement in by
  intro E Ω _ _ _ _ _ A w h rc ⟨a, ha, L⟩ n σ hP
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hP
  have hs' : HasSupport σ.ρ (GlobalTheory.RoadU.chars ξ hξ) := hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
  obtain ⟨e⟩ := equiv_prinSeries σ.ρ ξ hξ hs' hu
  have isL_chars_local {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V)
      (hρ : ρ.IsIrreducible) (ξ : Fin n → kˣ →* ℂˣ) (hξ : ∀ i, IsSmoothChar (ξ i))
      (hu : GlobalTheory.RoadU.Unlinked (GlobalTheory.RoadU.chars ξ hξ)) (e : ρ.Equiv (prinSeries ξ)) :
      IsL ((List.ofFn fun i => Segment.single (IrrGL.ofChar (ξ i) (hξ i)) (IrrGL.isCusp_ofChar _ _) : List (Segment k)) :
        Multiset (Segment k)) ρ := by
    let y : Fin n → IrrGL (k := k) := fun i => IrrGL.ofChar (ξ i) (hξ i)
    have hy : ∀ i, (y i).IsCusp := fun i => IrrGL.isCusp_ofChar _ _
    have hd : ∑ i, (y i).1 = n := by simp [y, IrrGL.ofChar]
    have hmem : ∀ i, y i ∈ GlobalTheory.RoadU.chars ξ hξ := fun i => Multiset.mem_map_of_mem _ (Finset.mem_univ i)
    have hnl : ∀ i j, ¬ (Segment.single (y i) (hy i)).Linked (Segment.single (y j) (hy j)) := fun i j =>
      GlobalTheory.CompanionTheory.BZPair.not_linked_single (hy i) (hy j) (hu _ (hmem j) _ (hmem i)) (hu _ (hmem i) _ (hmem j))
    have hP : (prodIrr y hd).IsIrreducible :=
      GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n (fun i => Segment.single (y i) (hy i)) y hd hnl
        (fun i => (single_spec (hy i)).2.1)
    obtain ⟨p⟩ := (Placing.parInd_jac_placing k _ _ _ (Equiv.sigmaUnique (Fin n) fun _ => Fin 1)
      (stdBlocks (fun i => (y i).1) hd) _).1 (piTensor fun i => detRep (Fin 1) (ξ i))
    let q := multiProdEquiv (stdBlocks (fun i => (y i).1) hd) fun i => equivRep (IrrRep.det (Fin 1) (ξ i) (hξ i))
    have hM : (multiProd (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) fun i => detRep (Fin 1) (ξ i)).IsIrreducible :=
      GlobalTheory.Parabolic.isIrreducible_of_equiv (p.trans q).symm hP
    haveI := nontrivial_of_irreducible hM
    haveI : Nontrivial (IndSp _ _) := by
      obtain ⟨S, f, hf⟩ := GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) ξ
      have := hf.nontrivial
      exact Subtype.val_injective.nontrivial (α := S.toSubmodule)
    have equiv_of_isSubquotient_local {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
        [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) [Nontrivial W]
        (hρ : ρ.IsIrreducible) : Nonempty (ρ.Equiv σ) := by
      obtain ⟨S, f, hf⟩ := h
      obtain ⟨y, hy⟩ := exists_ne (0 : W)
      obtain ⟨v, rfl⟩ := hf y
      haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
      rcases eq_bot_or_eq_top S with rfl | rfl
      · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy
      let F : ρ.IntertwiningMap σ := f.comp (topEquiv ρ).symm.toIntertwiningMap
      have hs : Function.Surjective F := hf.comp (topEquiv ρ).symm.toLinearEquiv.surjective
      refine ⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩
      haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
      rcases eq_bot_or_eq_top F.ker with h | h
      · have : x ∈ F.ker := hx
        rw [h] at this
        exact this
      · have : v.1 ∈ F.ker := by rw [h]; trivial
        exact absurd this hy
    
    obtain ⟨e1⟩ := equiv_of_isSubquotient_local (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n ξ) hM
    have φ : ρ.Equiv (prodIrr y hd) := (e.trans e1.symm).trans (p.trans q)
    exact ⟨n, y, hd, ⟨fun i => Segment.single (y i) (hy i), ⟨Fin.univ_val_map _, fun i j _ hp => hnl i j hp.1⟩,
      fun i => (single_spec (hy i)).2.1⟩, (isCosocle_self hρ).of_equiv (.refl _) φ⟩
  have hL := (isL_chars_local σ.ρ σ.irred ξ hξ hu e).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  have hr : rc (IrrGL.of σ.ρ σ.smooth σ.irred) =
      sumList (List.ofFn fun i => WD.lpOfChar h ((ξ i).comp a) (ha.smooth (hξ i))) := by
    rw [L.langlands _ _ hL, segSum, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.mpr (funext fun i => ?_)
    simp only [Function.comp_apply, Segment.single, Segment.first_ofFirst, Segment.len_ofFirst, Nat.cast_one, sub_self,
      zero_div, WD.lpTw_zero, Test.lpChar_lpSp_one, L.one]
  have hA : rc (algNorm σ) = (sumList (List.ofFn fun i => WD.lpOfChar h ((ξ i).comp a) (ha.smooth (hξ i)))).lpTw
      ((1 - (n : ℝ)) / 2) := by
    rw [algNorm, L.nu, hr]
  have monodromy_free_sum_list (l : List (WD h)) (hl : ∀ z ∈ l, z.mono0) : (sumList l).mono0 := by
    induction l with
    | nil =>
      show (WD.lpZero (h := h)).mono0
      rw [WD.lpZero, WD.monodromyZero_ofWeilDeligneRepClass_iff]
      rfl
    | cons b l ih =>
      show (WD.lpSum b (sumList l)).mono0
      exact (WD.monomial_sum_iff _ _).2 ⟨hl b (by simp), ih fun z hz => hl z (by simp [hz])⟩
  have monodromy_free_of_character (c : Weil h →* ℂˣ) (hc : GlobalTheory.WeilDeligne.IsSmooth c) : (WD.lpOfChar h c hc).mono0 := by
    rw [WD.lpOfChar, WD.monodromyZero_ofWeilDeligneRepClass_iff]
    rfl
  have comm_one {G : Type} [Group G] {H : Type} [CommGroup H] (f : G →* H) (s t : G) : f (@Bracket.bracket _ _ commutatorElement s t) = 1 := by
    rw [map_commutatorElement]
    exact (Commute.all _ _).commutator_eq
  have tor_sum {n : ℕ} (c : Fin n → Weil h →* ℂˣ) (hc : ∀ i, GlobalTheory.WeilDeligne.IsSmooth (c i)) (r : ℝ)
      (hd : ((sumList (List.ofFn fun i => WD.lpOfChar h (c i) (hc i))).lpTw r).lpDim = n) :
      UpperTheory.GalStar.Tor ((sumList (List.ofFn fun i => WD.lpOfChar h (c i) (hc i))).lpTw r) := by
    intro s t
    show WD.charPol _ _ = _
    rw [hd, GlobalTheory.GalCut.AwayMono.charPol_lpTw, comm_one, GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_ofFn]
    have h1 : ∀ i, (WD.lpOfChar h (c i) (hc i)).charPol (@Bracket.bracket _ _ commutatorElement s t) = X - 1 := fun i => by
      rw [WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
      simp only [comm_one]
      simp
    simp [h1, List.prod_ofFn]
  refine ⟨?_, ?_⟩
  · rw [hA]
    exact tor_sum _ _ _ (by rw [← hA, L.dim]; rfl)
  · rw [hA, WD.monomial_twist_iff]
    exact monodromy_free_sum_list _ fun z hz => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hz
      exact monodromy_free_of_character _ _
end
end

