module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMovesKernelCommonStabilizerSmulEq
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.KernInv

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

def mvEquiv (h : S.GLV) : S.MW ≃+ S.MW :=
  (h.toAddEquiv.prodCongr h.toAddEquiv).prodCongr (h.toAddEquiv.prodCongr (AddEquiv.refl E))

end GlobalTheory.HL.KernInv

namespace GlobalTheory.HL

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma form_apply_apply_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (x y : S.V) :
    S.h (h x) (h y) = S.h x y := by
  unfold _root_.GlobalTheory.HL.Frames.St at hh
  have hN := (Subgroup.mem_inf.mp hh).1
  unfold _root_.GlobalTheory.HL.Frames.N _root_.GlobalTheory.HL.Frames.Nof at hN
  have hI := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hN).1).1
  unfold _root_.GlobalTheory.HL.isomG at hI
  unfold _root_.GlobalTheory.HL.Frames.h
  exact hI x y

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma addSubgroup_eq_map_of_apply_mem_iff {M : Type} [AddCommGroup M] (e : M ≃+ M)
    (A B : AddSubgroup M) (hAB : ∀ w, e w ∈ B ↔ w ∈ A) : B = A.map e.toAddMonoidHom := by
  ext w
  constructor
  · intro hw
    exact ⟨e.symm w, (hAB _).mp (by simpa using hw), by simp⟩
  · rintro ⟨w, hw, rfl⟩
    exact (hAB w).mpr hw

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma mem_refB_iff (J : ℕ) (Λ : Submodule L.O S.V) (a b : S.V) :
    (a, b) ∈ S.refB J Λ ↔ a ∈ S.spanTo S.f J ∧ b ∈ S.spanTo S.f' J ∧
      ∃ y ∈ Λ, a + b = (algebraMap F E) S.th • y := by
  unfold _root_.GlobalTheory.HL.Frames.refB
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_prod, AddSubgroup.mem_comap, AddSubgroup.mem_map,
    Submodule.mem_toAddSubgroup, and_assoc]
  exact Iff.rfl.and (Iff.rfl.and (exists_congr fun _ => Iff.rfl.and eq_comm))

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma apply_mem_sup_iff_of_apply_mem_iff (h : S.GLV) (A B : Submodule E S.V)
    (hA : ∀ v, h v ∈ A ↔ v ∈ A) (hB : ∀ v, h v ∈ B ↔ v ∈ B) (v : S.V) :
    h v ∈ A ⊔ B ↔ v ∈ A ⊔ B := by
  simp only [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    refine ⟨h.symm y, (hA _).mp (by simpa using hy), h.symm z, (hB _).mp (by simpa using hz), ?_⟩
    rw [← map_add (f := _), hyz, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact ⟨h y, (hA y).mpr hy, h z, (hB z).mpr hz, (map_add h y z).symm⟩

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma apply_mem_perp_Ysp_iff_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (J : ℕ) (u : S.V) :
    h u ∈ _root_.GlobalTheory.HL.perp L S.Hm (S.Ysp J) ↔
      u ∈ _root_.GlobalTheory.HL.perp L S.Hm (S.Ysp J) := by
  have hform : ∀ x y, _root_.GlobalTheory.HL.hf L S.Hm (h x) (h y) =
      _root_.GlobalTheory.HL.hf L S.Hm x y := form_apply_apply_of_mem_St S hh
  have hY : ∀ v, h v ∈ S.Ysp J ↔ v ∈ S.Ysp J := by
    unfold _root_.GlobalTheory.HL.Frames.Ysp
    exact apply_mem_sup_iff_of_apply_mem_iff S h _ _
      (_root_.GlobalTheory.FrameAct.spanTo_iff S h hh J)
      (_root_.GlobalTheory.FrameAct.spanTo_iff' S h hh J)
  unfold _root_.GlobalTheory.HL.perp
  show (∀ y ∈ S.Ysp J, _ = 0) ↔ (∀ y ∈ S.Ysp J, _ = 0)
  constructor
  · intro H y hy
    rw [← hform]
    exact H _ ((hY y).mpr hy)
  · intro H y hy
    have hyy : h (h.symm y) = y := h.apply_symm_apply y
    rw [← hyy, hform]
    exact H _ ((hY _).mp (hyy.symm ▸ hy))

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma coe_smul_submodule_eq_iff_of_apply_mem_iff (h : S.GLV) (Λ₁ : Submodule L.O S.V) (P Q : Set S.V)
    (hPQ : ∀ v, h v ∈ Q ↔ v ∈ P) :
    ((h • Λ₁ : Submodule L.O S.V) : Set S.V) = Q ↔ (Λ₁ : Set S.V) = P := by
  simp only [Set.ext_iff, SetLike.mem_coe]
  rw [h.surjective.forall]
  simp only [_root_.GlobalTheory.FrameAct.mem_smul_iff, hPQ]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma eich_apply_apply_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (a b v : S.V) (c : E) :
    _root_.GlobalTheory.HL.eich L S.Hm (h a) (h b) c (h v) = h (_root_.GlobalTheory.HL.eich L S.Hm a b c v) := by
  have hform : ∀ x y, _root_.GlobalTheory.HL.hf L S.Hm (h x) (h y) =
      _root_.GlobalTheory.HL.hf L S.Hm x y := form_apply_apply_of_mem_St S hh
  unfold _root_.GlobalTheory.HL.eich
  rw [hform, hform]
  simp only [map_add (f := _), map_sub, map_smul]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
private lemma apply_mem_moved_smul_iff_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (Λ : Submodule L.O S.V) (a b v : S.V) (c : E) :
    h v ∈ S.moved (h • Λ) (h a) (h b) c ↔ v ∈ S.moved Λ a b c := by
  unfold _root_.GlobalTheory.HL.Frames.moved
  show _root_.GlobalTheory.HL.eich L S.Hm (h a) (h b) c (h v) ∈ h • Λ ↔
    _root_.GlobalTheory.HL.eich L S.Hm a b c v ∈ Λ
  rw [eich_apply_apply_of_mem_St S hh, _root_.GlobalTheory.FrameAct.mem_smul_iff]


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
theorem _root_.GlobalTheory.HL.kern_smul_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (β J βJ : ℕ) (Λ₁ : Submodule L.O S.V), ∀ h ∈ S.St, S.kern β J βJ d (h • Λ) (h • Λ₁) = S.kern β J βJ d Λ Λ₁ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT β J βJ Λ₁ h hh
  have hform := form_apply_apply_of_mem_St S hh
  have hmove := (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ hT h hh).2.2.2.2.2.2.2.2.2.2
  have hA : S.refA J (h • Λ) =
      (S.refA J Λ).map (_root_.GlobalTheory.HL.KernInv.mvEquiv S h).toAddMonoidHom := by
    refine addSubgroup_eq_map_of_apply_mem_iff _ _ _ ?_
    rintro ⟨⟨a, b⟩, u, t⟩
    unfold _root_.GlobalTheory.HL.Frames.refA
    simp only [AddSubgroup.mem_prod]
    change (h a, h b) ∈ S.refB J (h • Λ) ∧ h u ∈ S.refU J (h • Λ) ∧ t ∈ S.refT ↔
      (a, b) ∈ S.refB J Λ ∧ u ∈ S.refU J Λ ∧ t ∈ S.refT
    rw [mem_refB_iff, mem_refB_iff, ← map_add (f := _),
      _root_.GlobalTheory.FrameAct.spanTo_iff S h hh,
      _root_.GlobalTheory.FrameAct.spanTo_iff' S h hh]
    have hth := _root_.GlobalTheory.FrameAct.inTh_iff S h Λ (a + b)
    unfold _root_.GlobalTheory.HL.Frames.InTh at hth
    rw [hth]
    unfold _root_.GlobalTheory.HL.Frames.refU
    simp only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup,
      _root_.GlobalTheory.FrameAct.mem_smul_iff, apply_mem_perp_Ysp_iff_of_mem_St S hh]
  have hP : ∀ w, _root_.GlobalTheory.IdxInt.ind (S.MvTo J d (h • Λ) (h • Λ₁))
      (_root_.GlobalTheory.HL.KernInv.mvEquiv S h w) = _root_.GlobalTheory.IdxInt.ind (S.MvTo J d Λ Λ₁) w := by
    rintro ⟨⟨a, b⟩, u, t⟩
    have hs : S.sOf ((h a, h b), (h u, t)) = S.sOf ((a, b), (u, t)) := by
      unfold _root_.GlobalTheory.HL.Frames.sOf
      simp only [hform]
    have hiff : S.MvTo J d (h • Λ) (h • Λ₁) ((h a, h b), (h u, t)) ↔
        S.MvTo J d Λ Λ₁ ((a, b), (u, t)) := by
      unfold _root_.GlobalTheory.HL.Frames.MvTo _root_.GlobalTheory.HL.Frames.Mv
      change S.IsMove J d (h • Λ) (h a) (h b) (h u) (S.sOf ((h a, h b), (h u, t))) ∧
          ((h • Λ₁ : Submodule L.O S.V) : Set S.V) =
            S.moved (h • Λ) (h a) (h u) (S.sOf ((h a, h b), (h u, t))) ↔
        S.IsMove J d Λ a b u (S.sOf ((a, b), (u, t))) ∧
          (Λ₁ : Set S.V) = S.moved Λ a u (S.sOf ((a, b), (u, t)))
      rw [hs]
      exact and_congr (hmove J a b u _).symm
        (coe_smul_submodule_eq_iff_of_apply_mem_iff S h Λ₁ _ _ fun v => apply_mem_moved_smul_iff_of_mem_St S hh Λ a u v _)
    unfold _root_.GlobalTheory.IdxInt.ind
    exact if_congr hiff rfl rfl
  unfold _root_.GlobalTheory.HL.Frames.kern
  rw [hA, (_root_.GlobalTheory.IdxInt.Transport.cint_map_and_change.1 _ _ _).2]
  simp only [hP]

end GlobalTheory.HL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GoodPlaceGramInvariantMinorsValuationZero
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StdPlace.UnitVal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem vE_eq_zero_of_unit (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {c : F}
    (hc : algebraMap F E c ∈ L.O) (hu : ∃ y ∈ L.O, algebraMap F E c * y = 1) :
    vE L ϖ (algebraMap F E c) = 0 := by
  obtain ⟨hadd, -, hint, -⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  obtain ⟨y, hy, hcy⟩ := hu
  have hE : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; omega)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hcy
    exact zero_ne_one hcy
  have hyc : y = algebraMap F E c⁻¹ := by
    have h1 : algebraMap F E c * algebraMap F E c⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
    calc y = (algebraMap F E c⁻¹ * algebraMap F E c) * y := by rw [mul_comm (algebraMap F E c⁻¹), h1, one_mul]
      _ = algebraMap F E c⁻¹ * (algebraMap F E c * y) := by ring
      _ = algebraMap F E c⁻¹ := by rw [hcy, mul_one]
  have hci : c⁻¹ ∈ 𝒪[F] := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 (hyc ▸ hy)
  have hcO : c ∈ 𝒪[F] := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 hc
  have h1 := (hint c hc0).2 hcO
  have h2 := (hint c⁻¹ (inv_ne_zero hc0)).2 hci
  have h11 := hadd 1 1 one_ne_zero one_ne_zero
  rw [one_mul] at h11
  have h3 := hadd c c⁻¹ hc0 (inv_ne_zero hc0)
  rw [mul_inv_cancel₀ hc0] at h3
  omega

end GlobalTheory.HL.StdPlace.UnitVal


open GlobalTheory.HL.StdPlace.UnitVal in
theorem GlobalTheory.HL.StdPlace.vE_G_D_eq_zero : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → vE L S.ϖ S.G = 0 ∧ ∀ l, S.D l ≠ 0 → vE L S.ϖ (S.D l * L.cj (S.D l)) = 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S hS
  obtain ⟨-, -, ⟨c, -, hGc⟩, -⟩ := GlobalTheory.FrameBasic.main L r k S
  refine ⟨?_, fun l hl => ?_⟩
  · rw [hGc]
    obtain ⟨hG, y, hy, hGy⟩ := hS.G_unit
    exact vE_eq_zero_of_unit L S.ϖ_irr (hGc ▸ hG) ⟨y, hy, hGc ▸ hGy⟩
  · obtain ⟨hD, y, hy, hDy⟩ := hS.D_unit l hl
    obtain ⟨c, hc⟩ := GlobalTheory.UnramOrder.exists_norm L hD
    rw [hc]
    refine vE_eq_zero_of_unit L S.ϖ_irr (hc ▸ L.O.mul_mem hD (GlobalTheory.UnramOrder.cj_mem L hD))
      ⟨y * L.cj y, L.O.mul_mem hy (GlobalTheory.UnramOrder.cj_mem L hy), ?_⟩
    rw [← hc]
    calc S.D l * L.cj (S.D l) * (y * L.cj y) = (S.D l * y) * L.cj (S.D l * y) := by rw [map_mul]; ring
      _ = 1 := by rw [hDy, map_one, mul_one]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianTermSplitsUnimodularComplement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.UnimodSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]


omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem eq_zero_of_forall_hf (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
    (hd : IsUnit Hm.det) {z : Fin n → E} (hz : ∀ v, hf L Hm z v = 0) : z = 0 := by
  have h1 : Matrix.vecMul z Hm = 0 := by
    funext j
    have := hz (Pi.single j 1)
    simp only [hf, Pi.single_apply, apply_ite (⇑L.cj), map_one, map_zero, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    simpa [Matrix.vecMul, dotProduct] using this
  have := congrArg (fun u => Matrix.vecMul u Hm⁻¹) h1
  simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hd] using this


omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem cj_mem (L : LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.O_def] at hx ⊢
  exact hx.map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem hf_add_left (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    hf L Hm (x + x') y = hf L Hm x y + hf L Hm x' y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem hf_add_right (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) :
    hf L Hm x (y + y') = hf L Hm x y + hf L Hm x y' := by
  simp [hf, mul_add, Finset.sum_add_distrib]

omit [IsNonarchimedeanLocalField F] [CharZero F] in
theorem hf_sum_right {L : LocE F E} {r k : ℕ} (S : Frames L r k) {ι : Type} [Fintype ι] (x : S.V)
    (c : ι → E) (g : ι → S.V) :
    hf L S.Hm x (∑ l, c l • g l) = ∑ l, hf L S.Hm x (g l) * L.cj (c l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [FrameBasic.hf_conj L S.herm.1 x, UnimodTerm.hf_sum_left S, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, ← FrameBasic.hf_conj L S.herm.1 x (g l)]

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.a = 0 → ∃ b : Fin (k - 1) → S.V, (∀ i, b i ∈ S.W0) ∧ Λ = S.M d Λ ⊔ Submodule.span L.O (Set.range b) ∧ (∀ i j, hf L S.Hm (b i) (b j) ∈ L.O) ∧ ∃ P : Matrix (Fin (k - 1)) (Fin (k - 1)) E, IsIntM L P ∧ (Matrix.of fun i j => hf L S.Hm (b i) (b j)) * P = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT ha
  obtain ⟨hSD, hW, hM, -⟩ := TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, hc, -⟩ := FrameBasic.main L r k S
  obtain ⟨-, -, -, hW0, -, b, hbli, hb⟩ := Gluing.main L r k S d Λ hT
  have hMΛ : ∀ m ∈ S.M d Λ, m ∈ Λ := fun m h => (hM h).1
  have hMME : ∀ m ∈ S.M d Λ, m ∈ S.ME := fun m h => (hM h).2
  have hbL : ∀ w, w ∈ Submodule.span L.O (Set.range b) ↔ w ∈ S.complementLatticeOfDatum d := fun w => by
    rw [hb]; rfl
  have hbW : ∀ i, b i ∈ S.W0 := fun i => ((hbL _).1 (Submodule.subset_span ⟨i, rfl⟩)).1
  have hspan : ∀ w ∈ S.W0, (w ∈ Λ ↔ w ∈ Submodule.span L.O (Set.range b)) := by
    intro w hw
    rw [hbL]
    constructor
    · intro h; exact ((hW0 w hw).1 h).1
    · intro h; exact (UnimodTerm.mem_iff_graph S hT ha hw).2 h.2.2.2
  have hdec : ∀ x, ∃ m ∈ S.ME, ∃ w ∈ S.W0, x = m + w := by
    intro x
    have hx : x ∈ S.ME ⊔ S.W0 := by rw [hc.sup_eq_top]; trivial
    obtain ⟨m, hm, w, hw, h⟩ := Submodule.mem_sup.1 hx
    exact ⟨m, hm, w, hw, h.symm⟩
  have hΛ : Λ = S.M d Λ ⊔ Submodule.span L.O (Set.range b) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨m, hm, w, hw, rfl⟩ := hdec x
      have h1 : m ∈ S.M d Λ := UnimodTerm.proj_mem S hT ha hx hm (by simpa using hw)
      have h2 : w ∈ Λ := by simpa using Λ.sub_mem hx (hMΛ m h1)
      exact Submodule.mem_sup.2 ⟨m, h1, w, (hspan w hw).1 h2, rfl⟩
    · refine sup_le (fun m h => hMΛ m h) (fun w h => ?_)
      exact (hspan w ((hbL w).1 h).1).2 h
  have hbΛ : ∀ i, b i ∈ Λ := fun i => (hspan _ (hbW i)).2 (Submodule.subset_span ⟨i, rfl⟩)
  have hG : ∀ i j, hf L S.Hm (b i) (b j) ∈ L.O := fun i j => (hSD.2 (b j)).2 (hbΛ j) (b i) (hbΛ i)
  have hYW : Submodule.span E (Set.range b) ≤ S.W0 :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hbW i)
  have hOY : ∀ w ∈ Submodule.span L.O (Set.range b), w ∈ Submodule.span E (Set.range b) :=
    fun w h => Submodule.span_le_restrictScalars L.O E (Set.range b) h
  have hWY : S.W0 ≤ Submodule.span E (Set.range b) := by
    have htop : (⊤ : Submodule E S.V) ≤ S.ME ⊔ Submodule.span E (Set.range b) := by
      rw [← hSD.1.2, Submodule.span_le]
      intro x hx
      have hx' : x ∈ S.M d Λ ⊔ Submodule.span L.O (Set.range b) := by rw [← hΛ]; exact hx
      obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
      exact Submodule.mem_sup.2 ⟨m, hMME m hm, w, hOY w hw, rfl⟩
    intro w hw
    obtain ⟨m, hm, y, hy, rfl⟩ := Submodule.mem_sup.1 (htop (Submodule.mem_top (x := w)))
    have hm0 : m ∈ S.ME ⊓ S.W0 := ⟨hm, by simpa using S.W0.sub_mem hw (hYW hy)⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at hm0
    rw [hm0, zero_add]; exact hy
  have hzero : ∀ z ∈ S.W0, (∀ j, hf L S.Hm z (b j) = 0) → z = 0 := by
    intro z hz hzb
    apply eq_zero_of_forall_hf L S.herm.2
    intro v
    obtain ⟨m, hm, w, hw, rfl⟩ := hdec v
    have e1 : hf L S.Hm z m = 0 := hz m hm
    have e2 : hf L S.Hm z w = 0 := by
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 (hWY hw)
      rw [hf_sum_right S]
      simp [hzb]
    rw [hf_add_right, e1, e2, add_zero]
  set Gb : Matrix (Fin (k - 1)) (Fin (k - 1)) E := Matrix.of fun i j => hf L S.Hm (b i) (b j) with hGb
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have : IsArtinianRing E := IsArtinianRing.of_finite F E
  have hunit : IsUnit Gb := by
    rw [← Matrix.vecMul_surjective_iff_isUnit]
    have hinj : Function.Injective Gb.vecMulLinear := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro c hc
      have hz : ∑ i, c i • b i = 0 := by
        apply hzero _ (S.W0.sum_mem fun i _ => S.W0.smul_mem _ (hbW i))
        intro j
        have := congrFun hc j
        simp only [Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, Pi.zero_apply, hGb,
          Matrix.of_apply] at this
        rw [UnimodTerm.hf_sum_left S, ← this]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      funext i
      exact Fintype.linearIndependent_iff.1 hbli c hz i
    exact IsArtinian.surjective_of_injective_endomorphism Gb.vecMulLinear hinj
  have hdet := (Matrix.isUnit_iff_isUnit_det Gb).1 hunit
  have hGP : Gb * Gb⁻¹ = 1 := Matrix.mul_nonsing_inv Gb hdet
  refine ⟨b, hbW, hΛ, hG, Gb⁻¹, ?_, hGP⟩
  intro l j
  set y : S.V := ∑ l', L.cj (Gb⁻¹ l' j) • b l' with hy
  have hyb : ∀ i, hf L S.Hm (b i) y = if i = j then 1 else 0 := by
    intro i
    rw [hy, hf_sum_right S]
    have := congrFun (congrFun hGP i) j
    simp only [Matrix.mul_apply, Matrix.one_apply, hGb, Matrix.of_apply] at this
    rw [← this]
    exact Finset.sum_congr rfl fun l' _ => by rw [L.cj_cj]
  have hyW : y ∈ S.W0 := S.W0.sum_mem fun l' _ => S.W0.smul_mem _ (hbW l')
  have hyΛ : y ∈ Λ := by
    refine (hSD.2 y).1 fun x hx => ?_
    have hx' : x ∈ S.M d Λ ⊔ Submodule.span L.O (Set.range b) := by rw [← hΛ]; exact hx
    obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hx'
    obtain ⟨o, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hw
    have e1 : hf L S.Hm m y = 0 := by
      rw [FrameBasic.hf_conj L S.herm.1 m y, hyW m (hMME m hm), map_zero]
    have e2 : ∑ i, o i • b i = ∑ i, (o i : E) • b i := rfl
    rw [hf_add_left, e1, zero_add, e2, UnimodTerm.hf_sum_left S]
    simp only [hyb, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact (o j).2
  obtain ⟨Q, hQ⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 ((hspan y hyW).1 hyΛ)
  have hQ' : ∑ i, (Q i : E) • b i = y := hQ
  have hcoef : L.cj (Gb⁻¹ l j) = (Q l : E) := by
    have h0 := Fintype.linearIndependent_iff.1 hbli (fun l' => L.cj (Gb⁻¹ l' j) - (Q l' : E)) (by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [← hy, hQ', sub_self])
    exact sub_eq_zero.1 (h0 l)
  have h1 := cj_mem L (Q l).2
  rw [← hcoef, L.cj_cj] at h1
  exact h1

end GlobalTheory.HL.UnimodSplit
end
end

