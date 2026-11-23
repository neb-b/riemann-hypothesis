module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1741

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatOIffOfSt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.CutStdLat

open GlobalTheory.FunObj Matrix

theorem latO_iff_of_St {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (j : ℕ) (βS : GL (Fin (G.V (.top j)).rank) (Lev.EAf D))
    (βT : GL (Fin (G.V (.top (j + 1))).rank) (Lev.EAf D)) (hβS : IsFrame βS (colLat (S.N.fr (.top j))))
    (hβT : IsFrame βT (colLat (S.N.fr (.top (j + 1))))) (g : GA D (G.V (.top (j + 1))))
    (hT : Lev.finE (G.V (.top (j + 1))) g ∈ St βT) (x : WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :
    x ∈ stdLatO S (.top t j) ↔ actO _ _ 1 g x ∈ stdLatO S (.top t j) := by
  unfold stdLatO
  exact GlobalTheory.VecInv.mem_latO_iff (S := G.V (.top j)) (T := G.V (.top (j + 1))) hβS hβT (g := 1) (h := g)
    (by rw [map_one]; exact one_mem _) hT x

theorem keep_stdLatO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ e : AE D, IsIdemSum e (locPl G t) →
    ∀ g : GA D (G.V (.top (j + 1))),
      Formalism.L2.Theta.mt _ g = (1 - (e + cA D e)) • Formalism.L2.Theta.mt _ ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) :
        FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))) + (e + cA D e) • (1 : Matrix (Fin (G.V (.top (j + 1))).rank)
        (Fin (G.V (.top (j + 1))).rank) (AE D)) →
      ∀ x : WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)),
        x ∈ stdLatO S (.top t j) ↔ actO _ _ 1 g x ∈ stdLatO S (.top t j) := by
  intro D T L sc G W U S t ht Φ β j hj k hk e he g hg x
  classical
  have hfull {n : ℕ} (B : GL (Fin n) D.host.E) : (colLat B).IsFullLattice D.host.E := by
    letI := GlobalTheory.FunObj.VecEx.isLattice_colLat B
    refine ⟨?_⟩
    rw [colLat, Submodule.span_span_of_tower]
    change Submodule.span D.host.E (Set.range (B : Matrix (Fin n) (Fin n) D.host.E).col) = ⊤
    rw [← Matrix.range_mulVecLin]
    exact LinearMap.range_eq_top.mpr (Matrix.mulVec_surjective_iff_isUnit.mpr B.isUnit)
  obtain ⟨βS, hβS⟩ := frame_exists_alt D.host.F D.host.E _ (colLat (S.N.fr (.top j))) (hfull _)
  obtain ⟨βT, hβT⟩ := frame_exists_alt D.host.F D.host.E _ (colLat (S.N.fr (.top (j + 1)))) (hfull _)
  set a : AE D := e + cA D e with ha
  set b : Lev.EAf D := toEAf D (1 - a) with hbdef
  have hcb : ∀ w, GlobalTheory.StdFrames.cpt (D := D) w b = 1 - GlobalTheory.StdFrames.cpt (D := D) w (toEAf D a) := fun w => by
    rw [hbdef, RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one]
  have hca := GlobalTheory.T.idempotentSum_add_conj_component_indicator he
  have hb : b * b = b := GlobalTheory.StdFrames.cpt_ext fun w => by
    rw [RingHom.map_mul, hcb]
    by_cases h1 : w ∈ locPl G t ∨ GlobalTheory.IdemSupport.cP w ∈ locPl G t
    · rw [(hca w).1 h1]; ring
    · push_neg at h1; rw [(hca w).2 h1.1 h1.2]; ring
  have hfh : Lev.finE (G.V (.top (j + 1))) (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) :
      GA D (G.V (.top (j + 1)))) = (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * finG (G.V (.top (j + 1))) k * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) := by
    have e0 : Lev.finE (G.V (.top (j + 1))) (((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) :
        GA D (G.V (.top (j + 1)))) = finG (G.V (.top (j + 1))) ((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1))) := rfl
    rw [e0, map_mul, map_mul, map_inv]
  have hfg : Lev.finE (G.V (.top (j + 1))) g = GlobalTheory.UnitaryIdemCut.cutGL b hb
      ((finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * finG (G.V (.top (j + 1))) k * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))) := by
    apply Units.ext
    rw [GlobalTheory.UnitaryIdemCut.cutGL_val, ← hfh, GlobalTheory.VecInv.finE_val, GlobalTheory.VecInv.finE_val, hg]
    ext i l
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, RingHom.map_add (f := _), RingHom.map_mul, hbdef,
      RingHom.map_sub, RingHom.map_one, Matrix.one_apply]
    split_ifs <;> simp only [RingHom.map_one, RingHom.map_zero] <;> ring
  obtain ⟨Pu, eu, heu, hsu, hoff⟩ := S.N.u_supp (.top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  have hnot : ∀ Q ∈ Pu, ∀ w : Pl D.host.E, w.under (𝓞 D.host.F) = Q.under (𝓞 D.host.F) → w ∉ locPl G t := by
    intro Q hQ w hw hwl
    obtain ⟨h1, h2, -⟩ := S.N.off Q (hoff Q hQ)
    unfold locPl at hwl
    rcases Finset.mem_union.1 hwl with h3 | h3
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h3
      have h4 := G.pl.w_over v hv
      exact h1 ((hw.symm.trans h4) ▸ hv)
    · exact h2 t ht w h3 hw.symm
  have hub : b * toEAf D (eu + cA D eu) = toEAf D (eu + cA D eu) := GlobalTheory.StdFrames.cpt_ext fun w => by
    rw [RingHom.map_mul, hcb]
    have hu := GlobalTheory.T.idempotentSum_add_conj_component_indicator heu w
    by_cases h1 : w ∈ Pu ∨ GlobalTheory.IdemSupport.cP w ∈ Pu
    · rw [hu.1 h1]
      have hw1 : w ∉ locPl G t := by
        rcases h1 with h1 | h1
        · exact hnot w h1 w rfl
        · exact hnot _ h1 w (GlobalTheory.IdemSupport.under_cP w).symm
      have hw2 : GlobalTheory.IdemSupport.cP w ∉ locPl G t := by
        rcases h1 with h1 | h1
        · exact hnot w h1 _ (GlobalTheory.IdemSupport.under_cP w)
        · exact hnot _ h1 _ rfl
      rw [(hca w).2 hw1 hw2]; ring
    · push_neg at h1; rw [hu.2 h1.1 h1.2, mul_zero]
  have hU : GlobalTheory.UnitaryIdemCut.cutGL b hb (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))) = finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) := by
    apply Units.ext
    rw [GlobalTheory.UnitaryIdemCut.cutGL_val]
    show b • (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1).val + (1 - b) • 1 = (Lev.finE (G.V (.top (j + 1))) (S.N.u (.top (j + 1))).1).val
    rw [GlobalTheory.VecInv.finE_val]
    ext i l
    have h0 := hsu i l
    have h3 : b * toEAf D ((Formalism.L2.Theta.mt _ (S.N.u (.top (j + 1))).1 - 1) i l) =
        toEAf D ((Formalism.L2.Theta.mt _ (S.N.u (.top (j + 1))).1 - 1) i l) := by
      rw [← h0, RingHom.map_mul, ← mul_assoc, hub]
    have h4 : toEAf D ((1 : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) (AE D)) i l) =
        (1 : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) (Lev.EAf D)) i l := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [Matrix.sub_apply, RingHom.map_sub, h4] at h3
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    linear_combination h3
  have hK : GlobalTheory.UnitaryIdemCut.cutGL b hb (finG (G.V (.top (j + 1))) k) ∈ St (S.βp (j + 1)) :=
    GlobalTheory.T.idempotentCut_mem_latticeStabilizer_of_productLevel _ _ _ _ _ hk b hb fun w ⟨PP, hPP, hw⟩ => by
      rw [hcb]
      rcases GlobalTheory.IdemSupport.eq_or_eq_cP hw with rfl | rfl
      · rw [(hca _).1 (Or.inl hPP)]; ring
      · rw [(hca _).1 (Or.inr (by rwa [GlobalTheory.StdFrames.cP_cP]))]; ring
  have hcut : Lev.finE (G.V (.top (j + 1))) g = (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * GlobalTheory.UnitaryIdemCut.cutGL b hb (finG (G.V (.top (j + 1))) k) *
      finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) := by
    rw [hfg, map_mul, map_mul, map_inv, hU]
  have hp := S.βp_is (j + 1) (by omega)
  have hl := S.N.u_lat (.top (j + 1)) (show j + 1 ≤ D.R.m by omega)
  have keep : ∀ X ∈ St (S.βp (j + 1)), ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.top (j + 1)))),
      ((finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * X * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))).val *ᵥ y ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr (.top (j + 1)))) := by
    intro X hX y hy
    have h1 : (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))).val *ᵥ y ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.top (j + 1))) := (hl y).1 hy
    have h2 := ((GlobalTheory.LevSplit.mem_St_iff _ _ hp X).1 hX).1 _ h1
    refine (hl _).2 ?_
    change (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1)))).val *ᵥ _ ∈ _
    generalize finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) = Uu at h2 ⊢
    have e3 : Uu.val * (Uu⁻¹ * X * Uu).val = X.val * Uu.val := by
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [Matrix.mulVec_mulVec y Uu.val (Uu⁻¹ * X * Uu).val, e3, ← Matrix.mulVec_mulVec y X.val Uu.val]
    exact h2
  have st : ∀ X ∈ St (S.βp (j + 1)),
      (finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))))⁻¹ * X * finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) ∈ St βT := by
    intro X hX
    refine (GlobalTheory.LevSplit.mem_St_iff _ _ hβT _).2 ⟨keep X hX, fun y hy => ?_⟩
    have h5 := keep _ (inv_mem hX) y hy
    generalize finG (G.V (.top (j + 1))) (S.N.u (.top (j + 1))) = Uu at h5 ⊢
    have e1 : (Uu⁻¹ * X * Uu)⁻¹ = Uu⁻¹ * X⁻¹ * Uu := by group
    rw [e1]
    exact h5
  have hT : Lev.finE (G.V (.top (j + 1))) g ∈ St βT := by
    rw [hcut]
    exact st _ hK
  exact latO_iff_of_St S j βS βT hβS hβT g hT x

end GlobalTheory.CutStdLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSelfDualLatticeOfMemAllLatticeCompletions
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.FinPl.LocGlob

variable {D : D7}

theorem swap_finPart_pure (α : Af D.host.F) (e : D.host.E) :
    Formalism.IndefR.Lev.swapAE D (finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e)) = e ⊗ₜ[D.host.F] α := by
  have h1 : finPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] e) = α ⊗ₜ[D.host.F] e := by
    unfold finPart
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
    rfl
  rw [h1]
  rfl

theorem mem_of_local {S : HSp D} {L : GlobalTheory.FinPl.Lat S} (hL : IsSelfDualC S L) (z : Fin S.rank → D.host.E)
    (hz : ∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈
      GlobalTheory.FinPl.latV S L (· = v)) : z ∈ L := by
  classical
  have hlat := hL.1
  have hfull : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
      IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
    intro V Λ hΛ
    haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
    refine ⟨?_⟩
    obtain ⟨s, hs⟩ := hΛ.1.fg
    apply eq_top_iff.mpr
    intro y _
    let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
      ∑ i, ∑ j, star (x i) * V.gram i j * y j
    obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
    have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
      exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
    let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
      carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
      zero_mem' := by refine ⟨0, ?_⟩; simp [f]
      add_mem' := by
        rintro x z ⟨b, hb⟩ ⟨c, hc⟩
        refine ⟨b + c, ?_⟩
        change (b : D.host.E) + c = _
        rw [hb, hc]
        simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
      smul_mem' := by
        rintro c x ⟨b, hb⟩
        refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
        simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        change star (c : D.host.E) * _ = _
        ring }
    have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
      intro x hx
      obtain ⟨b, hb⟩ := ha x hx
      exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
    have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
      apply (hΛ.2 _).2
      intro x hx
      have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
      obtain ⟨b, hb⟩ := hxP
      refine ⟨b, ?_⟩
      rw [hb]
      dsimp only [f, Pi.smul_apply]
      simp only [smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
      Submodule.subset_span hy
    have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
      (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
    change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
      ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
    rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
    exact this
  have hspan := Submodule.IsFullLattice.span_eq_top (self := hfull S L hL)
  obtain ⟨d, hd, hdz⟩ := GlobalTheory.FinPl.exists_int_smul_le (Submodule.span (𝓞 D.host.E) {z}) L
    (Submodule.fg_span_singleton z) hspan
  set T := (GlobalTheory.FinPl.finite_places_int (D := D) d hd).toFinset with hT
  set β : Af D.host.F := 1 - ∑ v ∈ T, GlobalTheory.FinPl.LatMem.indP D.host.F (· = v) with hβ
  have hβv : ∀ w, evalV D.host.F w β = if w ∈ T then 0 else 1 := by
    intro w
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hβ, map_sub, map_one, map_sum]
    simp only [GlobalTheory.FinPl.LatMem.evalV_indP]
    rw [Finset.sum_ite_eq]
    split_ifs <;> simp
  have hoff : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] ((1 : D.host.E) * z i)) ∈
      GlobalTheory.FinPl.latV S L (fun w => w ∉ T) := by
    apply GlobalTheory.FinPl.LocAgree.latV_le_of_int_smul_on S (Submodule.span (𝓞 D.host.E) {z}) L d hd hdz
    · intro v hv hmem
      exact hv ((Set.Finite.mem_toFinset _).2 hmem)
    · apply AddSubgroup.subset_closure
      refine ⟨β, fun w => ?_, fun w hw => ?_, 1, rfl, z, Submodule.mem_span_singleton_self z, rfl⟩
      · rw [hβv]
        split_ifs
        · exact zero_mem _
        · exact one_mem _
      · rw [hβv, if_pos (not_not.1 hw)]
  have hall : (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) ∈ GlobalTheory.FinPl.latV S L (fun _ => True) := by
    have e : (fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i) =
        ∑ v ∈ T, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) +
          (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] ((1 : D.host.E) * z i)) := by
      funext i
      rw [Pi.add_apply, Finset.sum_apply, one_mul, ← TensorProduct.sum_tmul, ← TensorProduct.add_tmul]
      congr 1
      have hpa : ∀ a b : Af D.host.F, pairA D.host.F 0 a + pairA D.host.F 0 b = pairA D.host.F 0 (a + b) :=
        fun a b => Prod.ext (add_zero 0) rfl
      have hsum : ∀ (s : Finset (Pl D)) (f : Pl D → Af D.host.F),
          ∑ v ∈ s, pairA D.host.F 0 (f v) = pairA D.host.F 0 (∑ v ∈ s, f v) := by
        intro s f
        induction s using Finset.induction_on with
        | empty => exact Prod.ext rfl rfl
        | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, hpa]
      rw [hsum, hpa, hβ, add_sub_cancel]
    rw [e]
    exact add_mem (sum_mem fun v _ => GlobalTheory.FinPl.KSplit.latV_mono S L (fun _ _ => trivial) (hz v))
      (GlobalTheory.FinPl.KSplit.latV_mono S L (fun _ _ => trivial) hoff)
  have hhat := GlobalTheory.LatVHat.latV_mem_hatL D S L _ _ hall
  have e2 : (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (pairA D.host.F 0 1 ⊗ₜ[D.host.F] z i))) =
      fun i => Formalism.L2.Col.iA D.host.F D.host.E (z i) := by
    funext i
    rw [swap_finPart_pure]
    rfl
  rw [e2] at hhat
  exact (GlobalTheory.CongStdLoc.incl_mem_hatL_iff hlat.fg hspan z).1 hhat

theorem mem_of_mem_latV_all : ∀ {D : D7} {S : HSp D} {L : Lat S}, IsSelfDualC S L → (∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L) :=
  fun hL z hz => mem_of_local hL z hz

end GlobalTheory.FinPl.LocGlob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureVacInj
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.SmallGauss

open GlobalTheory.SmallDat GlobalTheory.TripleCplxAt
open scoped ComplexConjugate

theorem pure_vac_inj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} (hG : M.IsGood ψ)
    {f f' : SInf F (Fin n × Fin d)} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' M.vac) : f = f' := by
  classical
  choose ξ hξ using fun v => Function.ne_iff.1 (hG.vac v).2.1
  have hS := Filter.eventually_cofinite.1 hG.std
  let y : Fin n × Fin d → Af F := fun k => ∑ v ∈ hS.toFinset, singleFin v (ξ v k)
  have hy : finPartFn M.vac y ≠ 0 := by
    refine finprod_induction (· ≠ (0 : ℂ)) one_ne_zero (fun _ _ => mul_ne_zero) fun v => ?_
    by_cases hv : v ∈ hS.toFinset
    · have : (fun k => evalV F v (y k)) = ξ v := funext fun k => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_eq_single_of_mem v hv fun v' _ h => evalV_singleFin_ne h.symm _, evalV_singleFin_self]
      rw [this]
      exact hξ v
    · have : (fun k => evalV F v (y k)) = 0 := funext fun k => by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        exact Finset.sum_eq_zero fun v' h => evalV_singleFin_ne (fun e : v = v' => hv (e ▸ h)) _
      rw [this, of_not_not (mt hS.mem_toFinset.2 hv), Set.indicator_of_mem (by exact fun _ => zero_mem _)]
      exact one_ne_zero
  ext z
  have := congrFun h fun k => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace _).symm (z k)) (y k)
  simp only [pure_eq, pureA, pairA, RingEquiv.apply_symm_apply] at this
  exact mul_right_cancel₀ hy this

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ}

theorem compAt_mapA (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (t : T) (e : Num G i j) (u : PtS G i j) :
    compAt θ τ (mapA t e u) = ((compAt θ τ u).submatrix id fun k => e (.inl k))ᵀ * gramAt D (spW₁ G i j) τ := by
  show compAt θ τ (HMul.hMul (colV e u)ᵀ ((spW₁ G i j).gram.map (incA D))) = _
  rw [compAt_mul', compAt_inc θ hθ]
  rfl

theorem compAt_mapB (θ : InfFam D) (hθ : IsInfFam θ) (τ : D.what₂.Tau) (e : Num G i j) (u : PtS G i j) :
    compAt θ τ (mapB e u) = -(((compAt θ τ u).submatrix id fun k => e (.inr k)).map conj * gramAt D (spV₁ G i j) τ) := by
  show compAt θ τ (-HMul.hMul ((u.submatrix id fun k => e (.inr k)).map (cA D)) ((spV₁ G i j).gram.map (incA D))) = _
  rw [compAt_neg', compAt_mul', compAt_inc θ hθ, compAt_conj θ hθ]
  rfl


open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (blk) in
theorem cplx_pairS {W : G.Weil} {M : Vol G} {t : T} {i j : Fin D.R.m} {e : Num G i j} {Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E}
    {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j} {X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} (h : IsTripleOf W M t i j e Bs Γ X) (u u' : PtS G i j)
    (hu : ∀ w, u'.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) =
      Complex.I • (Γ.V'.θ w * u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) * (Γ.W.θ w)ᵀ)) (τ : D.what₂.Tau) :
    compAt W.θ τ (mapA t e u') = cplxO (W.cart (.grid i j) τ) (W.cart (.grid i (j + 1)) τ) (compAt W.θ τ (mapA t e u)) ∧
    compAt W.θ τ (mapB e u') = cplxO (-W.cart (.grid (i + 1) j) τ) (W.cart (.grid i j) τ) (compAt W.θ τ (mapB e u)) := by
  obtain ⟨w, hpi, hV, hWW⟩ : ∃ w, (∀ y, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w) y = conj (W.θ τ (infPart D y))) ∧
      Γ.V'.θ w = -W.cart (.grid i j) τ ∧
      Γ.W.θ w = (blk e (W.cart (.grid i (j + 1)) τ) (W.cart (.grid (i + 1) j) τ)).map conj := by
    obtain ⟨w, hw⟩ : ∃ w : InfinitePlace D.host.F, w = InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E)) :=
      ⟨_, rfl⟩
    obtain ⟨τ', hemb, -, hV, hWW⟩ := h.cart w
    have h1 : (Bs.emb w).1.comp (algebraMap D.host.F D.host.E) = w.embedding := (Bs.emb w).2
    have h2 : (tauE D τ').comp (algebraMap D.host.F D.host.E) = NumberField.ComplexEmbedding.conjugate w.embedding := by
      ext x
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq, ← h1]
      simp [hemb]
    have hh : ((starRingEnd ℂ).comp (tauE D τ')).comp (algebraMap D.host.F D.host.E) = w.embedding := by
      rw [← h1]; ext x; simp [hemb]
    have hb : Bs.emb w = ⟨_, hh⟩ := Subtype.ext (RingHom.ext hemb)
    have hτ : τ' = τ := (GlobalTheory.CMTypePlaces.places_bijective D).1 (by
      show InfinitePlace.mk ((tauE D τ').comp _) = InfinitePlace.mk ((tauE D τ).comp _)
      rw [h2, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding, hw])
    subst hτ
    exact ⟨w, fun y => by rw [hb]; exact GlobalTheory.ConjInfExp.piInf_eq W.θ W.θ_is _ w hh y, hV, hWW⟩
  have hmap : ∀ v : PtS G i j, v.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (Bs.emb w)) = (compAt W.θ τ v).map conj :=
    fun v => Matrix.ext fun a b => hpi _
  have hX := hu w
  rw [hmap, hmap, hV, hWW] at hX
  have cW₁ := W.cart_is (.grid (i : ℕ) (j : ℕ)) ⟨by omega, by omega⟩ τ
  have cV₁ := W.cart_is (.grid ((i : ℕ) + 1) (j : ℕ)) ⟨by omega, by omega⟩ τ
  refine ⟨?_, ?_⟩
  · have hs : (-W.cart (.grid i j) τ)ᴴ * (-gramAt D (spW₁ G i j) τ) =
        (-gramAt D (spW₁ G i j) τ) * (-W.cart (.grid i j) τ) := by
      rw [Matrix.conjTranspose_neg, neg_mul_neg, neg_mul_neg]
      exact cartan_comm cW₁
    have := algV e _ _ _ _ _ _ hX hs
    simp only [neg_neg] at this
    rw [compAt_mapA W.θ W.θ_is, compAt_mapA W.θ W.θ_is]
    exact this
  · have := algW e _ _ _ _ _ _ hX (cartan_comm cV₁)
    rw [compAt_mapB W.θ W.θ_is, compAt_mapB W.θ W.θ_is, this]
    show _ = Complex.I • (_ * _ * _)
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]

theorem isGauss : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : Fin D.R.m) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    ∀ (f₁ : GlobalTheory.SmallDat.HomA G t i j → ℂ) (f₂ : GlobalTheory.SmallDat.HomB G i j → ℂ), W.IsVac (.mu t i j) f₁ → W.IsVac (.chi i j) f₂ →
    ∀ (c : ℂ) (f₀ : SInf D.host.F (GlobalTheory.SmallDat.IxS G i j)),
      GlobalTheory.SmallDat.thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₀ Γ.M'.vac) = c • GlobalTheory.SmallDat.boxS t e f₁ f₂ → Γ.M'.IsGauss Bs.ψ Bs.emb f₀ := by
  intro D T L sc G W M t i j e Bs Γ X om om' h hT f₁ f₂ h₁ h₂ c f₀ hb
  obtain ⟨-, hinj, -⟩ := _root_.GlobalTheory.SmallDat.ThBox.thetaS_box W M t i j e Bs Γ X om om' h hT
  have hG : Γ.M'.IsGood W.ψ := h.ψ ▸ hT.geo.hM'
  have hm := fun f => (isFinPart_vac hG ∅).fam.mem hG f
  rw [h.ψ]
  refine ⟨1, fun u u' _ _ hJ f f' hf hf' => pure_vac_inj hG (hinj _ (hm _) _ (hm _) (funext fun x => ?_))⟩
  have hc := cplx_pairS h u u' fun w => by simpa using hJ w
  obtain ⟨a, ha, ha'⟩ := _root_.GlobalTheory.FockLineJ.fock_line_J W.ψ W.θ _ _ _ _ f₁ W.ψ_std W.θ_is h₁.2.theta h₁.2.fock _ _ (fun τ => (hc τ).1)
    (mapA t e x)
  obtain ⟨b, hb₁, hb'⟩ := _root_.GlobalTheory.FockLineJ.fock_line_J W.ψ W.θ _ _ _ _ f₂ W.ψ_std W.θ_is h₂.2.theta h₂.2.fock _ _ (fun τ => (hc τ).2)
    (mapB e x)
  have hr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evI D.host.F) f₀ fun y : IxS G i j → AF D.host.F => finPartFn Γ.M'.vac fun k => (y k).2 := by
    refine ⟨fun y z hz => ?_, hm f₀⟩
    refine congrArg (finPartFn Γ.M'.vac) (funext fun k => ?_)
    have : (pairA D.host.F 0 1 * z k).2 = 0 :=
      congrArg (fun q => (q k).2) (hz (pairA D.host.F 0 1) (map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace _)))
    exact (add_eq_left (a := (y k).2)).2 ((one_mul (z k).2).symm.trans this)
  have key : ∀ u (g : SInf D.host.F (IxS G i j)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (evI D.host.F) (Γ.M'.heisLine W.ψ u) f₀ g →
      HasDerivAt (fun s : ℝ => c * (heisO W.ψ _ _ (realAd D.host.F s • mapA t e u) f₁ (mapA t e x) *
        heisO W.ψ _ _ (realAd D.host.F s • mapB e u) f₂ (mapB e x))) (thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g Γ.M'.vac) x) 0 := by
    intro u g hg
    have := _root_.GlobalTheory.ThetaLineDeriv.hasDerivAt_thetaSum_rho Γ.M'.co W.ψ inferInstance W.ψ_std.1 u _ (hm f₀) _ (hm g) (hg _ hr) x
    convert this using 2 with s
    refine Eq.trans ?_ (congrFun (thetaS_rho Γ W.ψ _ (realAd D.host.F s • u)) x).symm
    rw [hb, ← mapA_smul, ← mapB_smul]
    refine Eq.trans (congrArg (c * ·) (congrFun (heisS_box t e Γ h.JW₁ h.JWW W.ψ _ f₁ f₂) x).symm) ?_
    simp only [heisS, Pi.smul_apply, smul_eq_mul]
    ring
  have e1 := (key u f hf).unique ((ha.mul hb₁).const_mul c)
  have e2 := (key u' f' hf').unique ((ha'.mul hb').const_mul c)
  have e3 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (Complex.I • f) Γ.M'.vac = Complex.I • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M'.vac :=
    funext fun _ => mul_assoc _ _ _
  have e4 : realAd D.host.F 0 = 0 := by
    unfold realAd
    rw [map_zero (algebraMap ℝ _), map_zero (RingEquiv.symm _)]
    rfl
  have e5 : thetaS Γ W.ψ (Complex.I • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M'.vac) x =
      Complex.I * thetaS Γ W.ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f Γ.M'.vac) x := thetaS_smul _ _ _ _ _
  rw [e3, e5, e1, e2]
  simp only [e4, zero_smul]
  ring

end GlobalTheory.SmallGauss
end
end

