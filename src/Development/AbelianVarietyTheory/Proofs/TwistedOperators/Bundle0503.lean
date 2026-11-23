module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0405
public import Formalism.LocalToGlobal.Divisibility.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0488
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0486
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0415
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0476
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0473
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0477

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexNsmulHalfOrthogonalIdempotentSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.HalfSplit

def kIdx (k : ℕ) (A : Type) [AddCommGroup A] : ℕ := (nsmulAddMonoidHom k : A →+ A).range.index

theorem relIndex_eq_kIdx {G : Type} [AddCommGroup G] (H : AddSubgroup G) (k : ℕ) :
    (AddSubgroup.map (nsmulAddMonoidHom k) H).relIndex H = kIdx k H := by
  unfold kIdx AddSubgroup.relIndex
  congr 1
  ext x
  simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hyx)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, by simp⟩

theorem kIdx_congr {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (k : ℕ) :
    kIdx k A = kIdx k B := by
  unfold kIdx
  rw [← AddSubgroup.index_map_equiv _ e]
  congr 1
  ext x
  simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨e y, by simp⟩
  · rintro ⟨y, rfl⟩
    exact ⟨k • e.symm y, ⟨e.symm y, rfl⟩, by simp⟩

theorem kIdx_prod {A B : Type} [AddCommGroup A] [AddCommGroup B] (k : ℕ) :
    kIdx k (A × B) = kIdx k A * kIdx k B := by
  unfold kIdx
  rw [← AddSubgroup.index_prod]
  congr 1
  ext ⟨a, b⟩
  simp only [AddSubgroup.mem_prod, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨⟨x, y⟩, hxy⟩
    exact ⟨⟨x, congrArg Prod.fst hxy⟩, ⟨y, congrArg Prod.snd hxy⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨(x, y), Prod.ext hx hy⟩

theorem kIdx_subsingleton {A : Type} [AddCommGroup A] [Subsingleton A] (k : ℕ) : kIdx k A = 1 :=
  AddSubgroup.index_eq_one.2 (eq_top_iff.2 fun x _ => ⟨0, Subsingleton.elim _ _⟩)

variable {R M : Type} [Ring R] [AddCommGroup M] [Module R M]

section split

variable (h : R → AddSubgroup M) (hmem : ∀ e u, u ∈ h e ↔ e • u = u) (Λ : AddSubgroup M) {e f : R}

include hmem in
theorem smul_mem_inf (he : e * e = e) (hΛe : ∀ u ∈ Λ, e • u ∈ Λ) {u : M} (hu : u ∈ Λ) : e • u ∈ Λ ⊓ h e :=
  AddSubgroup.mem_inf.2 ⟨hΛe u hu, (hmem _ _).2 (by rw [smul_smul, he])⟩

def splitEquiv (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0)
    (hΛe : ∀ u ∈ Λ, e • u ∈ Λ) (hΛf : ∀ u ∈ Λ, f • u ∈ Λ) :
    ↥(Λ ⊓ h (e + f)) ≃+ ↥(Λ ⊓ h e) × ↥(Λ ⊓ h f) where
  toFun u := (⟨e • u.1, smul_mem_inf h hmem Λ he hΛe (AddSubgroup.mem_inf.1 u.2).1⟩,
    ⟨f • u.1, smul_mem_inf h hmem Λ hf hΛf (AddSubgroup.mem_inf.1 u.2).1⟩)
  invFun p := ⟨p.1.1 + p.2.1, AddSubgroup.mem_inf.2 ⟨add_mem (AddSubgroup.mem_inf.1 p.1.2).1
      (AddSubgroup.mem_inf.1 p.2.2).1, (hmem _ _).2 (by
        have h1 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.1.2).2
        have h2 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.2.2).2
        have h3 : f • (p.1.1 : M) = 0 := by rw [← h1, smul_smul, hfe, zero_smul]
        have h4 : e • (p.2.1 : M) = 0 := by rw [← h2, smul_smul, hef, zero_smul]
        rw [smul_add, add_smul, add_smul, h1, h2, h3, h4, add_zero, zero_add])⟩⟩
  left_inv u := by
    apply Subtype.ext
    change e • (u : M) + f • (u : M) = u
    rw [← add_smul]
    exact (hmem _ _).1 (AddSubgroup.mem_inf.1 u.2).2
  right_inv p := by
    have h1 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.1.2).2
    have h2 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.2.2).2
    have h3 : f • (p.1.1 : M) = 0 := by rw [← h1, smul_smul, hfe, zero_smul]
    have h4 : e • (p.2.1 : M) = 0 := by rw [← h2, smul_smul, hef, zero_smul]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change e • ((p.1 : M) + p.2) = p.1
      rw [smul_add, h1, h4, add_zero]
    · change f • ((p.1 : M) + p.2) = p.2
      rw [smul_add, h2, h3, zero_add]
  map_add' u v := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change e • ((u : M) + v) = e • (u : M) + e • (v : M)
      exact smul_add _ _ _
    · change f • ((u : M) + v) = f • (u : M) + f • (v : M)
      exact smul_add _ _ _

end split

theorem sum_idem {ι : Type} (s : Finset ι) (cs : ι → R) (hid : ∀ i ∈ s, cs i * cs i = cs i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → cs i * cs j = 0) :
    (∑ i ∈ s, cs i) * (∑ i ∈ s, cs i) = ∑ i ∈ s, cs i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j hj hji => horth i hi j hj (Ne.symm hji)) (fun h => absurd hi h), hid i hi]

theorem kIdx_half_sum (h : R → AddSubgroup M) (hmem : ∀ e u, u ∈ h e ↔ e • u = u) (Λ : AddSubgroup M)
    {ι : Type} (P : Finset ι) (cs : ι → R) (hid : ∀ i ∈ P, cs i * cs i = cs i)
    (horth : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → cs i * cs j = 0) (hΛ : ∀ i ∈ P, ∀ u ∈ Λ, cs i • u ∈ Λ) (k : ℕ) :
    kIdx k ↥(Λ ⊓ h (∑ i ∈ P, cs i)) = ∏ i ∈ P, kIdx k ↥(Λ ⊓ h (cs i)) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    haveI : Subsingleton ↥(Λ ⊓ h 0) := ⟨fun a b => by
      have ha := (hmem _ _).1 (AddSubgroup.mem_inf.1 a.2).2
      have hb := (hmem _ _).1 (AddSubgroup.mem_inf.1 b.2).2
      rw [zero_smul] at ha hb
      exact Subtype.ext (ha.symm.trans hb)⟩
    exact kIdx_subsingleton k
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    have ha' : a ∈ insert a s := Finset.mem_insert_self a s
    have hne : ∀ j ∈ s, a ≠ j := fun j hj haj => ha (haj ▸ hj)
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      ← ih (fun i hi => hid i (hs i hi)) (fun i hi j hj => horth i (hs i hi) j (hs j hj))
        (fun i hi => hΛ i (hs i hi)),
      kIdx_congr (splitEquiv h hmem Λ (hid a ha')
        (sum_idem s cs (fun i hi => hid i (hs i hi)) (fun i hi j hj => horth i (hs i hi) j (hs j hj)))
        (by rw [Finset.mul_sum]; exact Finset.sum_eq_zero fun j hj => horth a ha' j (hs j hj) (hne j hj))
        (by rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun j hj => horth j (hs j hj) a ha' (hne j hj).symm)
        (hΛ a ha')
        (fun u hu => by rw [Finset.sum_smul]; exact AddSubgroup.sum_mem _ fun i hi => hΛ i (hs i hi) u hu)),
      kIdx_prod]

theorem relIndex_nsmul_half_sum : ∀ {D : D7} (S T : HSp D) (Λ : AddSubgroup (WO S T)) {ι : Type} (P : Finset ι) (cs : ι → AE D), (∀ i ∈ P, cs i * cs i = cs i) → (∀ i ∈ P, ∀ j ∈ P, i ≠ j → cs i * cs j = 0) → (∀ i ∈ P, ∀ u ∈ Λ, cs i • u ∈ Λ) → ∀ k : ℕ, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i)) = ∏ i ∈ P, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i)) := by
  intro D S T Λ ι P cs hid horth hΛ k
  rw [relIndex_eq_kIdx]
  simp only [relIndex_eq_kIdx]
  exact kIdx_half_sum (GlobalTheory.PlaceModel.half S T) (fun e u => GlobalTheory.PlaceModel.mem_half S T) Λ P cs hid horth hΛ k

end GlobalTheory.HalfSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexNsmulIdempotentHalfAtSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.HalfIndex

theorem relIndex_nsmul_half : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ (c : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D c → GlobalTheory.SplitHecke.Chart c v π → ∀ k : ℕ, 0 < k → (AddSubgroup.map (nsmulAddMonoidHom k) ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c) = Nat.card (v.adicCompletionIntegers D.host.F ⧸ Ideal.span {(k : v.adicCompletionIntegers D.host.F)}) ^ (S.rank * T.rank) := by
  intro D S T ΛS ΛT hS hT c v π hc hπ k hk
  haveI : CharZero (Fv D.host.F v) := algebraRat.charZero _
  obtain ⟨σ, q1, q2⟩ := GlobalTheory.SplitLinear.exists_section (S := S) (T := T) hc.1 hπ
  have inj : Function.Injective σ := fun w w' h => by rw [← q1 w, h, q1]
  have hinf : infPart D c = 0 := GlobalTheory.PlaceModelSum.infPart_split hc
  set L0 := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hL0
  set L := L0.comap σ with hL
  have hM : L0 ⊓ GlobalTheory.PlaceModel.half S T c = L.map σ := by
    rw [hL, AddSubgroup.map_comap_eq, ← GlobalTheory.SplitLinear.section_range hπ q1 q2, inf_comm]
  let nk : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) →+ Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) :=
    nsmulAddMonoidHom k
  have hcomm : (L.map σ).map (nsmulAddMonoidHom k) = (L.map nk).map σ := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    exact AddMonoidHom.ext fun w => (map_nsmul σ k w).symm
  have e1 : ((L0 ⊓ GlobalTheory.PlaceModel.half S T c).map (nsmulAddMonoidHom k)).relIndex (L0 ⊓ GlobalTheory.PlaceModel.half S T c) =
      (L.map nk).relIndex L := by
    rw [hM, hcomm, AddSubgroup.relIndex_map_map_of_injective _ _ inj]
  have hk0 : (k : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hnk : ∀ w, nk w = (k : Fv D.host.F v) • w := fun w => (Nat.cast_smul_eq_nsmul (Fv D.host.F v) k w).symm
  have nkinj : Function.Injective nk := fun w w' h => by
    rw [hnk, hnk] at h
    exact smul_right_injective _ hk0 h
  have nksurj : Function.Surjective nk := fun w => ⟨(k : Fv D.host.F v)⁻¹ • w, by rw [hnk, smul_inv_smul₀ hk0]⟩
  have e2 : (L.map nk).relIndex L = L.relIndex (L.comap nk) := by
    rw [← AddSubgroup.relIndex_map_map_of_injective L (L.comap nk) nkinj,
      AddSubgroup.map_comap_eq_self_of_surjective nksurj]
  let u : (Fv D.host.F v)ˣ := Units.mk0 _ hk0
  have hH : ∀ w : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v),
      ((k : Fv D.host.F v) • (1 : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v))) * w * (1 : Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v)) = nk w := fun w => by
    rw [hnk, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
  have hA := GlobalTheory.SplitLinear.relIndex_matrix_lattice D.host.F v S.rank T.rank L (L.comap nk)
    (fun o ho m hm => GlobalTheory.SplitLinear.section_smul hc.1 hπ q1 q2 o ho m hm)
    (GlobalTheory.SplitLinear.section_den hS.toIsLattice hT.toIsLattice hπ q1 q2) (fun w => ?_)
    ((k : Fv D.host.F v) • 1) 1 1 (u ^ T.rank) (by simp) (by simp [u, Matrix.det_smul]) (fun m hm => ?_) (fun w => ?_)
  rotate_left
  · obtain ⟨N, hN, h1⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS hT (σ w)
      (GlobalTheory.PlaceDatum.infPart_of_half hinf (q2 w))
    exact ⟨N, hN, by rwa [AddSubgroup.mem_comap, map_nsmul]⟩
  · rw [hH]
    exact nsmul_mem hm k
  · rw [hH]
    rfl
  have hkc : (((k : v.adicCompletionIntegers D.host.F)) : Fv D.host.F v) = (k : Fv D.host.F v) := by simp
  have hv : Valued.v (k : Fv D.host.F v) ≠ 0 := by simpa using hk0
  have h1 : Valued.v (k : Fv D.host.F v) ≤ 1 := hkc ▸ (k : v.adicCompletionIntegers D.host.F).2
  have hl : WithZero.log (Valued.v (k : Fv D.host.F v)) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hv, WithZero.exp_zero]; exact h1
  obtain ⟨e, he⟩ : ∃ e : ℕ, WithZero.log (Valued.v (k : Fv D.host.F v)) = -(e : ℤ) :=
    ⟨(-WithZero.log (Valued.v (k : Fv D.host.F v))).toNat, by omega⟩
  have he' : Valued.v (k : Fv D.host.F v) = WithZero.exp (-(e : ℤ)) := by
    rw [← he, WithZero.exp_log hv]
  have hcard := (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers D.host.F v).2
    (k : v.adicCompletionIntegers D.host.F) e (by rw [hkc]; exact he')
  have hu : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV D.host.F v u = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ e)⁻¹ := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV, Units.val_mk0, he, zpow_neg, zpow_natCast]
  have h1' : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV D.host.F v 1 = 1 := by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
  rw [e1, e2, hcard]
  apply Nat.cast_injective (R := ℝ)
  rw [hA, GlobalTheory.SplitLinear.absV_pow, hu, h1']
  push_cast
  rw [one_pow, one_mul, ← pow_mul, inv_pow, inv_inv, mul_comm T.rank S.rank]

end GlobalTheory.HalfIndex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ResidueConjugatePlaceCharacterArgumentSignedSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjChar.AtConj

theorem resT_of_mem {D : D7} (PP : Pl D.host.E) {x : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resT PP x = Formalism.L2.DIV.resS D.host.F PP ⟨x, hx⟩ := by
  unfold resT; rw [dite_eq_left hx]

theorem resT_zero {D : D7} (PP : Pl D.host.E) : resT PP (0 : EAf D) = 0 := by
  rw [resT_of_mem PP (zero_mem _)]
  exact map_zero (Formalism.L2.DIV.resS D.host.F PP)

theorem resT_add {D : D7} (PP : Pl D.host.E) {x y : EAf D} (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hy : y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : resT PP (x + y) = resT PP x + resT PP y := by
  rw [resT_of_mem PP hx, resT_of_mem PP hy, resT_of_mem PP (add_mem hx hy)]
  exact map_add (Formalism.L2.DIV.resS D.host.F PP) ⟨x, hx⟩ ⟨y, hy⟩

theorem resT_sum {D : D7} (PP : Pl D.host.E) {ι : Type} [Fintype ι] (f : ι → EAf D)
    (hf : ∀ i, f i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : resT PP (∑ i, f i) = ∑ i, resT PP (f i) := by
  have hs : (∑ i, f i) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := sum_mem fun i _ => hf i
  rw [resT_of_mem PP hs]
  have e : (⟨∑ i, f i, hs⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ∑ i, (⟨f i, hf i⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) := by
    apply Subtype.ext
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  exact Finset.sum_congr rfl fun i _ => (resT_of_mem PP (hf i)).symm

theorem flagV_f {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : ρ + k < i.1) (h2 : i.1 < 2 * ρ + k + 1) :
    GlobalTheory.SeeConjRead.flagV ρ k n e f b z i = f ⟨2 * ρ + k - i.1, by omega⟩ := by
  unfold GlobalTheory.SeeConjRead.flagV
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h2]

theorem symmetricFlagBasisVectors_apply_middle {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : i.1 = ρ + k) : GlobalTheory.SeeConjRead.flagV ρ k n e f b z i = z := by
  unfold GlobalTheory.SeeConjRead.flagV
  rw [dite_eq_right (by omega), dite_eq_right (by omega), dite_eq_left h1]

theorem flagV_b {M : Type} [Zero M] {ρ k n : ℕ} (e f : Fin ρ → M) (b : Fin k → M) (z : M) (i : Fin n)
    (h1 : ρ ≤ i.1) (h2 : i.1 < ρ + k) : GlobalTheory.SeeConjRead.flagV ρ k n e f b z i = b ⟨i.1 - ρ, by omega⟩ := by
  unfold GlobalTheory.SeeConjRead.flagV
  rw [dite_eq_right (by omega), dite_eq_left h2]

end GlobalTheory.SeeConjChar.AtConj

open GlobalTheory.SeeConjChar GlobalTheory.SeeConjChar.AtConj

theorem GlobalTheory.SeeConjChar.resT_cP_argT : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → ∀ β : GL (Fin (Yc D 0).rank) (EAf D), IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → (∀ PP ∈ R.Pg, RedIs β PP (flagAt X h PP)) → ∀ PP ∈ R.Pg, ∀ κ : GA D (Yc D 0), finE (Yc D 0) κ ∈ St β → ((iotaX X h).toMulEquiv κ).2 ∈ X.K2 → GlobalTheory.SeeConjChar.resT (GlobalTheory.IdemSupport.cP PP) (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) = GlobalTheory.SeeConjChar.conjRes PP (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then ((GlobalTheory.SeeConjChar.wB D.R.rS D.R.k (GlobalTheory.SeeConjChar.sideAt X h PP) i j : ℤ) : kP PP) * ((upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) : GL (Fin D.R.r) (kP PP)).val i j) else 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL hGrp β hβ hred PP hP κ hS hK2
  classical
  have hn : (Yc D 0).rank = 2 * D.R.rS + D.R.k + 1 := by
    have e := X.n_eq
    rw [h] at e
    have e2 := Formalism.L2.DIV.ranks_r_sym D
    change (Formalism.L2.SG.InstExistsPf.instOf D).n = _
    omega
  have hrn : D.R.r = (Yc D 0).rank := by
    have e := X.n_eq
    rw [h] at e
    change D.R.r = (Formalism.L2.SG.InstExistsPf.instOf D).n
    omega
  have hK : ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset := (Formalism.L2.SG.Closed.level_subgroup_properties X).2.1 _ hK2
  have hU : upperLeftBlock (r_le_Y (D := D) 0) (redFn β PP (finE (Yc D 0) κ)) ∈ unip (kP PP) D.R.r :=
    unipCol_le _ _ _ (((GlobalTheory.T.mem_K2_iff_upperLeftBlock_reductions R F X h hL hGrp β hβ hred κ hK hS).1 hK2) PP hP)
  have hMinv : (finE (Yc D 0) κ)⁻¹ ∈ St β := inv_mem hS
  have hredinv : redFn β PP (finE (Yc D 0) κ)⁻¹ = (redFn β PP (finE (Yc D 0) κ))⁻¹ := extendOne_inv _ hS
  have hC : ∀ a j, hT X h (flagAt X h PP j) (Matrix.mulVec (finE (Yc D 0) κ).val (pairAt X h PP a)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      resT (GlobalTheory.IdemSupport.cP PP) (hT X h (flagAt X h PP j) (Matrix.mulVec (finE (Yc D 0) κ).val (pairAt X h PP a))) =
        conjRes PP ((sgnD D.R.rS D.R.k a : kP PP) * ((redFn β PP (finE (Yc D 0) κ))⁻¹).val a j) := by
    intro a j
    have c1 := _root_.GlobalTheory.SeeConjAdj.resCP_adjoint X h PP κ (flagAt X h PP j) (pairAt X h PP a)
    have c2 := _root_.GlobalTheory.SeeConjChar.resT_hT_mulVec_stab X h β PP (flagAt X h PP) (hred PP hP) _ hMinv (pairAt X h PP a) (_root_.GlobalTheory.SeeConjChar.hT_pairAt_int X h β hβ PP a) j
    refine ⟨c1.1.2 c2.1, ?_⟩
    rw [c1.2, c2.2, hredinv]
    congr 1
    simp only [_root_.GlobalTheory.SeeConjChar.resT_hT_pair_flag R X h hL PP hP a, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

  let fF : Fin D.R.rS → Fin (Yc D 0).rank := fun a => ⟨2 * D.R.rS + D.R.k - a.1, by have := a.2; omega⟩
  let fN : Fin D.R.rS → Fin (Yc D 0).rank := fun a =>
    ⟨if a.1 + 1 < D.R.rS then 2 * D.R.rS + D.R.k - (a.1 + 1) else D.R.rS + D.R.k, by have := a.2; split_ifs <;> omega⟩
  let gB : Fin D.R.k → Fin (Yc D 0).rank := fun i => ⟨D.R.rS + D.R.k - 1 - i.1, by have := i.2; omega⟩
  have hF : ∀ a, f0T X h a = flagAt X h PP (fF a) := by
    intro a
    have ha := a.2
    have e : (fF a).1 = 2 * D.R.rS + D.R.k - a.1 := rfl
    have h1 : D.R.rS + D.R.k < (fF a).1 := by omega
    have h2 : (fF a).1 < 2 * D.R.rS + D.R.k + 1 := by omega
    unfold flagAt
    split_ifs <;> rw [flagV_f _ _ _ _ _ h1 h2] <;> congr 1 <;> ext <;> simp only [e] <;> omega
  have hNx : ∀ a, Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a = pairAt X h PP (fN a) := by
    intro a
    have ha := a.2
    have e : (fN a).1 = if a.1 + 1 < D.R.rS then 2 * D.R.rS + D.R.k - (a.1 + 1) else D.R.rS + D.R.k := rfl
    unfold Formalism.L2.SG.HidaSetting.nxt
    by_cases hlt : a.1 + 1 < D.R.rS
    · rw [dite_eq_left hlt]
      rw [if_pos hlt] at e
      have h1 : D.R.rS + D.R.k < (fN a).1 := by omega
      have h2 : (fN a).1 < 2 * D.R.rS + D.R.k + 1 := by omega
      unfold pairAt
      split_ifs <;> rw [flagV_f _ _ _ _ _ h1 h2] <;> congr 1 <;> ext <;> simp only [e] <;> omega
    · rw [dite_eq_right hlt]
      rw [if_neg hlt] at e
      unfold pairAt
      split_ifs <;> rw [symmetricFlagBasisVectors_apply_middle _ _ _ _ _ e]
  have hBd : GlobalTheory.SeeConjChar.sideAt X h PP ≠ true → ∀ i, bwdT X h i = flagAt X h PP (gB i) := by
    intro hs i
    have hi := i.2
    have e : (gB i).1 = D.R.rS + D.R.k - 1 - i.1 := rfl
    have hs' : ¬ GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 := by simpa [GlobalTheory.SeeConjChar.sideAt] using hs
    unfold flagAt
    rw [if_neg hs', flagV_b _ _ _ _ _ (by omega) (by omega)]
    congr 1; ext; simp only [e, Fin.val_rev]; omega
  have hBw : GlobalTheory.SeeConjChar.sideAt X h PP ≠ true → ∀ i : Fin D.R.k, bwT X h i = pairAt X h PP (gB i) := by
    intro hs i
    have hi := i.2
    have e : (gB i).1 = D.R.rS + D.R.k - 1 - i.1 := rfl
    have hs' : ¬ GlobalTheory.StdFrames.cpt PP (ewT X h) = 1 := by simpa [GlobalTheory.SeeConjChar.sideAt] using hs
    unfold pairAt
    rw [if_neg hs', flagV_b _ _ _ _ _ (by omega) (by omega)]
    congr 1; ext; simp only [e, Fin.val_rev]; omega

  have hfterm : ∀ a, hT X h (f0T X h a) (Matrix.mulVec (finE (Yc D 0) κ).val (Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      resT (GlobalTheory.IdemSupport.cP PP) (hT X h (f0T X h a) (Matrix.mulVec (finE (Yc D 0) κ).val (Formalism.L2.SG.HidaSetting.nxt (e0T X h) (z0T X h) a))) =
        conjRes PP ((sgnD D.R.rS D.R.k (fN a) : kP PP) * ((redFn β PP (finE (Yc D 0) κ))⁻¹).val (fN a) (fF a)) := by
    intro a
    rw [hF a, hNx a]
    exact hC _ _
  have hbterm : ∀ i : Fin D.R.k, (if hi : i.1 + 1 < D.R.k then hT X h (bwdT X h i) (Matrix.mulVec (finE (Yc D 0) κ).val (bwT X h ⟨i.1 + 1, hi⟩)) else 0) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧
      resT (GlobalTheory.IdemSupport.cP PP) (if hi : i.1 + 1 < D.R.k then hT X h (bwdT X h i) (Matrix.mulVec (finE (Yc D 0) κ).val (bwT X h ⟨i.1 + 1, hi⟩)) else 0) =
        conjRes PP (if hi : i.1 + 1 < D.R.k then (if GlobalTheory.SeeConjChar.sideAt X h PP then 0 else (sgnD D.R.rS D.R.k (gB ⟨i.1 + 1, hi⟩) : kP PP) * ((redFn β PP (finE (Yc D 0) κ))⁻¹).val (gB ⟨i.1 + 1, hi⟩) (gB i)) else 0) := by
    intro i
    by_cases hi : i.1 + 1 < D.R.k
    · rw [dite_eq_left hi, dite_eq_left hi]
      by_cases hs : GlobalTheory.SeeConjChar.sideAt X h PP = true
      · rw [if_pos hs]
        obtain ⟨h1, h2⟩ := _root_.GlobalTheory.SeeConjChar.resT_cP_hT_bwd_eq_zero X h β hβ PP hs _ hS i ⟨i.1 + 1, hi⟩
        exact ⟨h1, by rw [h2, map_zero]⟩
      · rw [if_neg hs, hBd hs i, hBw hs ⟨i.1 + 1, hi⟩]
        exact hC _ _
    · rw [dite_eq_right hi, dite_eq_right hi]
      exact ⟨zero_mem _, by rw [map_zero, resT_zero]⟩
  unfold argT
  set_option synthInstance.maxHeartbeats 100000 in
    rw [resT_add _ (sum_mem fun a _ => (hfterm a).1) (sum_mem fun i _ => (hbterm i).1), resT_sum _ _ (fun a => (hfterm a).1),
    resT_sum _ _ (fun i => (hbterm i).1), Finset.sum_congr rfl fun a _ => (hfterm a).2,
    Finset.sum_congr rfl fun i _ => (hbterm i).2, ← map_sum, ← map_sum, ← map_add]
  congr 1
  exact _root_.GlobalTheory.SeeConjComb.conj_residue_reindex (r_le_Y (D := D) 0) D.R.rS D.R.k hn hrn _ hU (GlobalTheory.SeeConjChar.sideAt X h PP) fF fN gB (fun a => rfl) (fun a => rfl) (fun i => rfl)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData

noncomputable section

namespace GlobalTheory.FirstRowEndLaw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}


open Classical in
def stepType (L : LevCh D T) (t : T) (w : Pl D.host.E) (j : ℕ) : TypeDatum (Kw w) (Ix (Fin D.R.r) (Fin D.R.t) j) :=
  if w ∈ L.Pg then
    (TypeDatum.principal (Kw w) (Fin D.R.r)).iter (Fin D.R.t) (fun c => ((muBase L c).loc w)⁻¹) (isTame_muBase w) j
  else if h : w ∈ L.Q t ∧ IsTame ((L.xiH t).loc w)⁻¹ then parahoric (Fin D.R.r) (Fin j × Fin D.R.t) _ h.2
  else TypeDatum.full _ _


open Classical in
def endLamAt (G : GridData L sc) (t : T) (w : Pl D.host.E) (j : ℕ) (κ : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)) : ℂ :=
  if h : (reGL (ixFin G t w j)).symm κ ∈ (stepType L t w j).J then (((stepType L t w j).lam ⟨_, h⟩)⁻¹ : ℂˣ) else 1

def endLam (G : GridData L sc) (t : T) (w : Pl D.host.E) (κ : GL (Fin ((locGrid G t w).rank (0, D.R.m))) (Kw w)) : ℂ :=
  endLamAt G t w D.R.m κ

end GlobalTheory.FirstRowEndLaw
end
end

