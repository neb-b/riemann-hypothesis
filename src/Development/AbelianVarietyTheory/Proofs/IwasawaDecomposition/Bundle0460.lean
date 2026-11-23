module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundColumns
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0455
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0302
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsPrescribedUnitaryFormsStandIns
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
public import Lean
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteFormsAllTuplesCoordinateLaws
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.Mats

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]


omit [NumberField K] in
theorem isConjAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) :
    Formalism.DivisionValues.IsConjAt (InfinitePlace.mk σ) := fun a => by
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rw [e]
    exact hσ a
  · rw [e, ComplexEmbedding.conjugate_coe_eq, ComplexEmbedding.conjugate_coe_eq, hσ a]


omit [NumberField K] [StarRing K] in
theorem posDef_of_mk {n : ℕ} {σ : K →+* ℂ} {H : Matrix (Fin n) (Fin n) K}
    (h : (H.map (InfinitePlace.mk σ).embedding).PosDef) : (H.map σ).PosDef := by
  rcases InfinitePlace.embedding_mk_eq σ with e | e
  · rwa [e] at h
  · rw [e] at h
    have h1 := h.isHermitian
    have e2 : H.map σ = (H.map (ComplexEmbedding.conjugate σ))ᵀ := by
      ext i j
      have := h1.apply j i
      simp only [Matrix.map_apply, ComplexEmbedding.conjugate_coe_eq, Matrix.transpose_apply] at this ⊢
      rw [← this]
      simp
    rw [e2]
    exact h.transpose


omit [NumberField K] in
theorem hform_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H x y = star x ⬝ᵥ H.mulVec y := by
  unfold Formalism.DivisionValues.hform
  rw [Matrix.toLinearMapₛₗ₂'_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply, RingHom.id_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring


omit [NumberField K] in
theorem hform_sa {n : ℕ} {H A : Matrix (Fin n) (Fin n) K} (h : Aᴴ * H = H * A) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H (A.mulVec x) y = Formalism.DivisionValues.hform H x (A.mulVec y) := by
  rw [hform_eq_dot, hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]


omit [NumberField K] [StarRing K] [Fintype G] in
theorem zero_laws [NumberField K] [StarRing K] (σ : K →+* ℂ) {e : MonoidAlgebra K G}
    (hc : e ∈ Subalgebra.center K (MonoidAlgebra K G)) (hi : IsIdempotentElem e) : (Mat1.zero K G).Laws σ e := by
  refine
    { pos := ?_
      lat := ?_
      add := fun _ _ => Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
      smul := fun _ _ => Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
      one := Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
      mul := fun _ _ _ _ => Subsingleton.elim (α := Matrix (Fin 0) (Fin 0) K) _ _
      E_eq := rfl
      cen := hc
      idem := hi
      sa := ?_ }
  · show ((0 : Matrix (Fin 0) (Fin 0) K).map σ).PosDef
    rw [Subsingleton.elim ((0 : Matrix (Fin 0) (Fin 0) K).map σ) 1]
    exact Matrix.PosDef.one
  · change Submodule.IsFullLattice K (⊤ : Submodule (𝓞 K) (Fin 0 → K))
    refine { toIsLattice := Submodule.IsLattice.of_fg K ?_, span_eq_top := Subsingleton.elim _ _ }
    rw [Subsingleton.elim (⊤ : Submodule (𝓞 K) (Fin 0 → K)) ⊥]
    exact Submodule.fg_bot
  · intro x y
    rw [hform_eq_dot, hform_eq_dot]
    rfl

def lvlMat (S : CSD K) (r : Representation K G S.Forms) (P : Subgroup G) (ψ : P →* Kˣ) (e : MonoidAlgebra K G) : Mat1 K G :=
  ⟨S.lvlDim r P ψ, S.lvlH r P ψ, S.lvlOp r P ψ e, S.lvlNab r P ψ, fun a => S.lvlOp r P ψ a⟩

theorem lvlMat_laws {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) (S : CSD K) {s : ℕ} (hS : S.Good s)
    (hpos : ∀ v : InfinitePlace K, (S.H.map v.embedding).PosDef) (r : Representation K G S.Forms) (hr : S.ActGood r)
    (hrat : S.ActRat r) (P : Subgroup G) (ψ : P →* Kˣ) (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) :
    (lvlMat S r P ψ (idemOf X)).Laws σ (idemOf X) := by
  have h0 := isConjAt_mk hσ
  have hP := (level_idempotent_spec K _ h0 G P ψ).1
  have hI := idempotent_spec K _ h0 G X hX
  have hinj : Function.Injective (S.lvlE r P ψ).mulVec := (image_idempotent_spec K _ _).1
  have hE : ∀ i j, S.lvlE r P ψ i j ∈ Formalism.DivisionValues.cmMax K :=
    image_idempotent_rational K S.dim (S.gaMat r (lvlIdem P ψ)) (gaMat_rat S r hrat _ hP.rat)
  have hproj := (orthogonal_projection_spec K _ h0 S (hpos _) G r hr _ hP.idem hP.selfAdj).1.1
  have hop := level_operator_spec K _ h0 S (hpos _) G r hr P ψ
  refine ⟨posDef_of_mk (cut_posDef S.H (S.lvlE r P ψ) hinj hE (Nat.card P) Nat.card_pos _ (hpos _)),
    (Formalism.DivisionValues.exponent_index_lattice.cut_isFullLattice (S.lvlE r P ψ) hinj _
      (Formalism.DivisionValues.ValuationLatticeField.valLatF_isFullLattice S.I S.I_injective S.Nab hS.nab_isFullLattice)),
    fun a b => ?_, fun c a => ?_, ?_,
    fun a _ b hb => (hop b (Subalgebra.mem_center_iff.1 hb _).symm).2 a, rfl, Subalgebra.mem_center_iff.2 hI.2, hI.1.idem,
    hform_sa ?_⟩
  · show S.lvlOp r P ψ (a + b) = S.lvlOp r P ψ a + S.lvlOp r P ψ b
    unfold CSD.lvlOp
    rw [CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, map_add (f := _), Matrix.mul_add, Matrix.add_mul]
  · show S.lvlOp r P ψ (c • a) = c • S.lvlOp r P ψ a
    unfold CSD.lvlOp
    rw [CSD.gaMat_eq_lift, CSD.gaMat_eq_lift, map_smul, Matrix.mul_smul, Matrix.smul_mul]
  · show S.lvlOp r P ψ 1 = 1
    unfold CSD.lvlOp
    rw [(group_action_matrix_hom K S G r).1, Matrix.mul_one]
    exact hproj
  · have h1 := (hop (idemOf X) (hI.2 _).symm).1
    have h2 := group_action_matrix_adjoint K S G r hr (idemOf X)
    rw [hI.1.selfAdj] at h2
    show (S.lvlOp r P ψ (idemOf X))ᴴ * ((Nat.card P : K)⁻¹ • ((S.lvlE r P ψ)ᴴ * S.H * S.lvlE r P ψ)) =
      ((Nat.card P : K)⁻¹ • ((S.lvlE r P ψ)ᴴ * S.H * S.lvlE r P ψ)) * S.lvlOp r P ψ (idemOf X)
    rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1,
      Matrix.conjTranspose_mul, Matrix.mul_assoc (S.lvlE r P ψ)ᴴ, h2, Matrix.mul_assoc _ (S.lvlE r P ψ), h1]
    simp only [Matrix.mul_assoc]

end Gen

section Col

variable {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (W : Formalism.L2.Col.Wts X Pr.Word R) (Ch : Formalism.L2.Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok) (v0 : InfinitePlace X.K)
  (TU : Finset (Tup X.F X.E X.K S)) (Xg : Finset (Formalism.L2.Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {σ : X.K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a))
  (hirr : ∀ χ ∈ Xg, IsAbsIrrChar χ) (P : Subgroup (Formalism.L2.Col.G0 X.E Pr.vGs R.r)) (ψ : P →* X.Kˣ)

include hσ hirr

theorem rows_laws (τ : TupF TU) :
    (lvlMat ((colIn W Ch sel hX v0 TU Xg S0 xiVal).MtildeCSD τ) ((colIn W Ch sel hX v0 TU Xg S0 xiVal).leftGroupActionRight τ) P ψ
      (idemOf Xg)).Laws σ (idemOf Xg) :=
  lvlMat_laws hσ _ (Formalism.L2.Col.MtildeKCSD_good W Ch sel τ.1 hX _) (fun v => (Formalism.L2.Col.mtildeK_rat W Ch sel τ.1 hX).posH _ v) _
    (Formalism.L2.Col.unipotentActionForms_good W Ch sel τ.1 hX _) (Formalism.L2.Col.unipotentActionForms_rational W Ch sel τ.1 hX _) P ψ Xg hirr

theorem lifts_laws (j : Fin R.m) (τ : TupF TU) :
    (lvlMat ((colIn W Ch sel hX v0 TU Xg S0 xiVal).MtCSD j τ) ((colIn W Ch sel hX v0 TU Xg S0 xiVal).leftGroupActionLift j τ) P ψ
      (idemOf Xg)).Laws σ (idemOf Xg) :=
  lvlMat_laws hσ _ (Formalism.L2.Col.MtKCSD_good W Ch sel τ.1 hX (j.1 + 1) _)
    (fun v => (Formalism.L2.Col.mtK_rat W Ch sel τ.1 hX (j.1 + 1)).posH _ v) _
    (Formalism.L2.Col.unipotentActionClassSum_good W Ch sel τ.1 hX (j.1 + 1) _) (Formalism.L2.Col.unipotentActionClassSum_rational W Ch sel τ.1 hX (j.1 + 1) _) P ψ Xg hirr

end Col

section Fam

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m)
  (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)

theorem rMat_eq (t : T) : rMat A P ψ t = lvlMat (A.MtildeCSD t) (A.leftGroupActionRight t) P ψ (idemOf A.X) := rfl

theorem lMat_eq (i : Fin D.R.m) (t : T) : lMat A P ψ i t = lvlMat (A.MtCSD i t) (A.leftGroupActionLift i t) P ψ⁻¹ (idemOf A.X) := rfl

end Fam

theorem mats_laws : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px), I.Ok → (∀ χ ∈ Xg, IsAbsIrrChar χ) → (∀ b a, (mAU X I hX Xg tr b a).Laws X.toD7.what₂.embLL (idemOf Xg)) ∧ ∀ a j, (mLU X I hX Xg tr a j).Laws X.toD7.what₂.embLL (idemOf Xg) := by
  intro X px I hX Xg tr _ hirr
  refine ⟨fun b a => ?_, fun a j => ?_⟩
  · unfold mAU
    rw [rMat_eq]
    exact rows_laws (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I Set.univ) Xg ∅
      (xiValOf I) (σ := X.B.embLL) X.B.starLL_cx hirr _ _ (tAll I a)
  · unfold mLU
    split_ifs with h
    · rw [lMat_eq]
      exact lifts_laws (X := X.B.fields) (Pr := X.B.primes px) X.B.wts I.Ch I.sel hX (InfinitePlace.mk X.B.embLL) (tuOf I Set.univ) Xg ∅
        (xiValOf I) (σ := X.B.embLL) X.B.starLL_cx hirr _ _ _ (tAll I a)
    · have hI := idempotent_central X.B.LL (Gc X.B px) Xg hirr
      exact zero_laws _ (Subalgebra.mem_center_iff.2 hI.2) hI.1

end GlobalTheory.Mem.R3.Rw.Mats

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElementSameCharacterNearBadStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelElement_same_character_near_bad : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl), ChiFin I l Z (K (chOf c)).lev → ∀ κ : (K (chOf c)).lev.U, ∃ x : (K (chOf c)).lev.U, (K (chOf c)).lev.chi x = (K (chOf c)).lev.chi κ ∧ (∃ q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, PtOf ((show GA B (B.R.N i) from ((K (chOf c)).y ⟨c, rfl⟩).1) * (show GA B (B.R.N i) from x.1) * k (chOf c)) q) ∧ ∀ P : SBof I a, GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (κ.1⁻¹ * x.1) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.LevelElt.exists_level_elt | exact GlobalTheory.Mem.Col2.AdT.LevelElt.exists_level_elt | (intros; apply GlobalTheory.Mem.Col2.AdT.LevelElt.exists_level_elt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberChartMatchingAwayFromTwistStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_memberChart_matching_awayFromTwist : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (K0 : ∀ β : Ch0, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf0 c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.ReadsK l Z u I.mu0 i hi chOf0 K0 → ∃ (g : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → Ch0) (k : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i)), GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i k ∧ ∀ (K : ∀ β : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.Reads u a i (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i) (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1) (fun c s => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).stabI ⟨c, rfl⟩ s).1) k → ∀ β, (∀ κ : (K β).lev.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → ∃ h' : κ.1 ∈ (K0 (g β)).lev.U, (K β).lev.chi κ = (K0 (g β)).lev.chi ⟨κ.1, h'⟩) ∧ ∀ κ' : (K0 (g β)).lev.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ'.1 = 1) → κ'.1 ∈ (K β).lev.U := by
  intro B X I hI pins l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hK
  exact GlobalTheory.Mem.Col2.TC.ChTw.charts_match I hI pins l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPeriodMapFormsEquivRowLiftFormsUpperLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.PerId
attribute [local instance] GlobalTheory.Mem.Col2.starE

theorem exists_crd_equiv (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) {O : Type} [CommRing O] {φ : O →+* ℂ}
    {s : Sp1 O φ (Gc X.B px)} (t : Tie1 X.toD7.what₂.embLL (mAU X I hX Xg tr true a) s) :
    ∃ e : Df.MtCx I a ≃ₗ[ℂ] s.A.T, ∀ y, IsCrd I hX a e
      (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) (t.j y) := by
  obtain ⟨e, he⟩ := ColTie.exists_equiv_of_bases (σ := ColTie.sig X.B)
    (n := ColTie.dimP (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX)
    (ColTie.jP (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX (ColTie.sig X.B)) t.j
    (ColTie.linearIndependent_jP_single (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX (ColTie.sig X.B))
    (ColTie.span_range_jP_single_eq_top (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX (ColTie.sig X.B))
    t.forms.li t.forms.span
  refine ⟨e, fun y => ⟨ColTie.zOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y, ?_, (he y).symm⟩⟩
  exact ⟨(ColTie.resK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX).symm
      (ColTie.formK (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y),
    ColTie.zOf_mem (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I) hX y,
    heq_of_eq (LinearEquiv.apply_symm_apply _ _), rfl⟩


set_option maxHeartbeats 400000 in
theorem exists_perT : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (hX : B.fields.Ok) (Xg : Finset (Gc B w.px → B.LL)) (tr : TrI B w.px) (p : PkB B w.C (Gc B w.px)) (tA : ∀ a : w.I.ι, Tie1 (w.st Z).toD7.what₂.embLL (mAU (w.st Z) w.I hX Xg tr true a) (p.sA true a)), ∃ d : PerD p, Nonempty (PerT w Z hX Xg tr p (fun a x => (tA a).j x) d) := by
  intro B f T w Z hX Xg tr p tA
  have hE := fun a : w.I.ι => exists_crd_equiv (w.st Z) w.I hX Xg tr a (tA a)
  choose e he using hE
  have hG : ∀ u a, ∃ g : Df.MtCx w.I a ≃ₗ[ℂ] (TC.per w.I w.l u a).Mt, ∀ F, Df.SameForm w.I w.l u a F (g F) := fun u a =>
    Df.mtCx_equiv_per w.I w.ok w.pins w.l hX u a
  choose g hg using hG
  refine ⟨⟨fun u => (g u w.I.mu0).symm.trans (e w.I.mu0), fun u a => (g u a).symm.trans (e a)⟩, ⟨⟨e, ?_, ?_, he⟩⟩⟩
  · intro u F
    have h1 : ((g u w.I.mu0).symm.trans (e w.I.mu0)).symm (e w.I.mu0 F) = g u w.I.mu0 F := by
      rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm]
    exact h1 ▸ hg u w.I.mu0 F
  · intro u a F
    have h1 : ((g u a).symm.trans (e a)).symm (e a F) = g u a F := by
      rw [LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_symm]
    exact h1 ▸ hg u a F

end GlobalTheory.Mem.R3.Rw.PerId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowsDatumPrescribedTuplesDefinedWeights
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Ex

@[reducible] def reset {B : Base} {C : Cols B} (W : RowsRest B C) (mt ma : B.places.Pl → C.Tup)
    (hmt : ∀ v, mt (B.places.conj v) = mt v) (hma : ∀ v, ma (B.places.conj v) = ma v)
    (hor : ∀ v, ma v = C.mu0 ∨ ma v = mt v) : RowsRest B C :=
  { W with
    muAt := ma
    muAt_conj := hma
    muTw := mt
    muTw_conj := hmt
    muAt_or := hor
    kaBig := GlobalTheory.Mem.DfGen.kaBigB B
    kaSmall := GlobalTheory.Mem.DfGen.kaSmallB B
    shaLen := GaloisStage.shaTrue B.host
    shaLen_nonneg := GaloisStage.shaTrue_nonneg B.host }

theorem kapDef_of_ka {B : Base} {C : Cols B} (W' : RowsRest B C) (hb : W'.kaBig = GlobalTheory.Mem.DfGen.kaBigB B)
    (hs : W'.kaSmall = GlobalTheory.Mem.DfGen.kaSmallB B) : ∀ V S N G, DV.KapDef (assemble B C W' V S N G) := by
  intro V S N G j _ _ τ
  refine ⟨fun i => ?_, fun c => ?_⟩
  · show ((W'.kaBig j τ i : ℤ) : ℚ) = _
    rw [hb]
    exact (GlobalTheory.Mem.DfGen.aPlusB_int B j τ i).choose_spec.symm
  · show ((W'.kaSmall j τ c : ℤ) : ℚ) = _
    rw [hs]
    show ((-(GlobalTheory.Mem.DfGen.aMinusB_int B j τ c).choose : ℤ) : ℚ) = -GlobalTheory.Mem.DfGen.aMinusB B j τ c
    push_cast
    rw [← (GlobalTheory.Mem.DfGen.aMinusB_int B j τ c).choose_spec]

end GlobalTheory.Mem.R3.Rw.Ex

end

open GlobalTheory.Mem.R3.Rw.Ex in
theorem GlobalTheory.Mem.R3.Rw.exists_rowsRest_muW : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (hX : B.fields.Ok) (Wt : Set B.places.Pl), (∀ v, B.places.conj v ∈ Wt ↔ v ∈ Wt) → ∃ W₀ : RowsRest B w.C, MuW w Wt W₀ ∧ (∀ W' : RowsRest B w.C, W'.kaBig = W₀.kaBig → W'.kaSmall = W₀.kaSmall → ∀ V S N G, DV.KapDef (assemble B w.C W' V S N G)) ∧ GlobalTheory.MemN.ShaOK B.toPre W₀.shaLen := by
  intro B f T w hX Wt hWt
  classical
  obtain ⟨R⟩ := GlobalTheory.Mem.Df.rowsDef_nonempty w.I w.ok w.pins w.l hX
  have hmem : ∀ v, ∃ a, w.I.xi a = T.xiTw f v := fun v => by
    have h : T.xiTw f v ∈ Set.range w.I.xi := by
      rw [w.xi_range]; exact Or.inr ⟨v, rfl⟩
    exact h
  have hconj : ∀ v, T.xiTw f (B.places.conj v) = T.xiTw f v := fun v => by
    unfold TwDat.xiTw
    rw [GlobalTheory.Mem.Top.TwFin.resChar_conj, (T.conj v).1]
  let mt : B.places.Pl → w.C.Tup := fun v => Classical.choose (hmem v)
  have hmt : ∀ v, mt (B.places.conj v) = mt v := fun v => by
    show Classical.choose (hmem (B.places.conj v)) = Classical.choose (hmem v)
    have : ∀ x y (hx : ∃ a, w.I.xi a = x) (hy : ∃ a, w.I.xi a = y), x = y →
        Classical.choose hx = Classical.choose hy := by
      rintro x y hx hy rfl; rfl
    exact this _ _ _ _ (hconj v)
  let ma : B.places.Pl → w.C.Tup := fun v => if v ∈ Wt then mt v else w.C.mu0
  have hma : ∀ v, ma (B.places.conj v) = ma v := fun v => by
    simp only [ma, hWt v, hmt v]
  have hor : ∀ v, ma v = w.C.mu0 ∨ ma v = mt v := fun v => by
    by_cases h : v ∈ Wt
    · exact Or.inr (if_pos h)
    · exact Or.inl (if_neg h)
  refine ⟨reset R.W mt ma hmt hma hor, ⟨fun v => Classical.choose_spec (hmem v), fun v h => if_pos h, fun v h => if_neg h⟩,
    fun W' hb hs => kapDef_of_ka W' hb hs, GlobalTheory.MemN.shaOK_shaTrue B.toPre⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsCoordinatesIndexOfFamilyTupleEq
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (Xg : Finset (Gc X.B px → X.B.LL))
  (tr : TrI X.B px)


set_option maxHeartbeats 2000000 in
theorem rMat_famR_eq (U U' : Set I.ι) (P : Subgroup (Gc X.B px)) (ψ : P →* X.toD7.what₂.LLˣ) (t : TupU I U) (t' : TupU I U')
    (h : t.1 = t'.1) :
    rMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ t = rMat (D := X.toD7) (famR X I hX U' Xg tr).A P ψ t' := by
  obtain ⟨τ, hτ⟩ := t
  obtain ⟨τ', hτ'⟩ := t'
  obtain rfl : τ = τ' := h
  exact (by with_unfolding_all exact ((Eq.refl (rMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ ⟨τ, hτ⟩)) :))


set_option maxHeartbeats 2000000 in
theorem lMat_famR_eq (U U' : Set I.ι) (P : Subgroup (Gc X.B px)) (ψ : P →* X.toD7.what₂.LLˣ) (i : Fin X.toD7.R.m)
    (t : TupU I U) (t' : TupU I U') (h : t.1 = t'.1) :
    lMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ i t = lMat (D := X.toD7) (famR X I hX U' Xg tr).A P ψ i t' := by
  obtain ⟨τ, hτ⟩ := t
  obtain ⟨τ', hτ'⟩ := t'
  obtain rfl : τ = τ' := h
  exact (by with_unfolding_all exact ((Eq.refl (lMat (D := X.toD7) (famR X I hX U Xg tr).A P ψ i ⟨τ, hτ⟩)) :))


set_option maxHeartbeats 2000000 in
theorem mAU_mLU_ixOf : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (t : TupU I U), (∀ b, mAU X I hX Xg tr b (ixOf I U t) = rMat (D := X.toD7) (famR X I hX U Xg tr).A (levP (face0 X I hX U Xg tr).lv2 b).1 (levP (face0 X I hX U Xg tr).lv2 b).2 t) ∧ ∀ i : Fin X.toD7.R.m, mLU X I hX Xg tr (ixOf I U t) ((i : ℕ) + 1) = lMat (D := X.toD7) (famR X I hX U Xg tr).A (face0 X I hX U Xg tr).lv2.P0 (face0 X I hX U Xg tr).lv2.ψ0 i t := by
  intro X px I hX U Xg tr t
  refine ⟨fun b => ?_, fun i => ?_⟩
  · cases b
    · exact rMat_famR_eq X I hX Xg tr Set.univ U (lev0 I) (chr0 I) (tAll I (ixOf I U t)) t (tup_ixOf I t)
    · exact rMat_famR_eq X I hX Xg tr Set.univ U (lev1 I) (chr1 I) (tAll I (ixOf I U t)) t (tup_ixOf I t)
  · have hi : 1 ≤ (i : ℕ) + 1 ∧ (i : ℕ) + 1 ≤ X.toD7.R.m := ⟨by omega, i.2⟩
    unfold mLU
    rw [dite_eq_left hi]
    exact lMat_famR_eq X I hX Xg tr Set.univ U (lev0 I) (chr0 I) i (tAll I (ixOf I U t)) t (tup_ixOf I t)

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HdTr
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

theorem hd_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (y : Hd R), ∃ y' : HdB b R, Same b y y' := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R y
  letI := alg b iK
  let y' : HdB b R :=
    { tup := (by with_unfolding_all exact (y.tup :))
      tupT := (by with_unfolding_all exact (y.tupT :))
      tupT_tup := (by with_unfolding_all exact (y.tupT_tup :))
      tup0 := (by with_unfolding_all exact (y.tup0 :))
      hm := (by with_unfolding_all exact (y.hm :))
      hTop := topMult_tr b y.hTop
      hinj := inj_tr b y.hinj
      PY := (by with_unfolding_all exact ((rowPsi b y.PY) :))
      PW := fun i => (by with_unfolding_all exact ((rowPsi b (y.PW i)) :))
      ιW := (by with_unfolding_all exact (y.ιW :))
      isomFin := fun i => ⟨(by with_unfolding_all exact ((y.isomFin i).bij :)), (by with_unfolding_all exact ((y.isomFin i).conj :)), (by with_unfolding_all exact ((y.isomFin i).lat :))⟩
      frameMatch := (by with_unfolding_all exact (y.frameMatch :))
      hF := (by with_unfolding_all exact (y.hF :))
      stdPsi := (by with_unfolding_all exact (y.stdPsi :)) }
  exact ⟨y', ⟨(by with_unfolding_all exact ((HEq.refl y.tup) :)), (by with_unfolding_all exact ((HEq.refl y.tupT) :)), (by with_unfolding_all exact ((HEq.refl y.PY.ψ) :)), (by with_unfolding_all exact ((HEq.refl fun i => (y.PW i).ψ) :))⟩⟩

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftIdentificationsOfLiftsComparison
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.LiftRd

theorem liftTie_of_lfT : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (y : Hd R), Inputs D → R.BaseW F → (∀ μ, Used0 D μ ↔ y.Us μ) → DV.LamDef D → ∀ (rep : D.what₂.FT → Formalism.L2.NG.FinTyp D.host.E D.R.r) (jL : ∀ (i : Fin D.R.m) t, (Fin (lDim D A F.P0 F.ψ0 i t) → D.what₂.LL) → D.what₂.Mt (y.tup t) ((i : ℕ) + 1)) (t : LfT y F rep (Mt := fun μ j => ⟨D.what₂.Mt μ j⟩) jL ⟨fun j => ⟨D.what₂.Mj j⟩, D.what₂.MjLat, D.what₂.thetaP, D.what₂.isot⟩), ∃ (I : LiftIds (y.L F)) (mj : GlobalTheory.RealGeo.MjTie R F), LiftTie (y.L F) I ∧ (∀ i π, I.prtW i π = y.prtW F i (rep π)) ∧ (∀ i x, (I.jMj i x).1 = t.jMj i x) ∧ (∀ μ h i x, (I.jMt μ h i x).1 = t.jMt μ i x) ∧ ∀ i x, mj.eW i x = t.eW i x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F y hI hB hU hLam rep jL t
  let I : LiftIds (y.L F) :=
    { jMj := fun i =>
        (LinearEquiv.ofInjective (t.jMj i) (t.jMj_inj i)).trans (LinearEquiv.ofEq _ _ (t.jMj_range i))
      jMt := fun μ hμ i =>
        (LinearEquiv.ofInjective (t.jMt μ i) (t.jMt_inj μ ((hU μ).1 hμ) i)).trans
          (LinearEquiv.ofEq _ _ (t.jMt_range μ ((hU μ).1 hμ) i))
      prtW := fun i π => y.prtW F i (rep π) }
  refine ⟨I, ⟨t.eW, t.eW_range, t.eW_norm, t.eW_lat⟩, ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ => rfl⟩
  refine ⟨fun i => GlobalTheory.HilbertLevels.holW R F y.tupT y.hm y.hTop y.hinj i, fun i x x' => t.jMj_ip i x x',
    fun μ hμ i x x' => t.jMt_ip μ ((hU μ).1 hμ) i x x', ?_, fun i π v => t.isot i π v,
    fun i π π' h => t.disj i π π' h, ?_⟩
  · intro μ hμ i x w _ hw hthC hgood
    exact t.theta μ ((hU μ).1 hμ) i x _ w hw hthC hgood
  · intro μ _ i π c h0 hc
    rw [hLam μ ((i : ℕ) + 1) (by omega) i.2 π h0]
    exact DV.lamTr_of_scalar D μ _ π c h0 hc

end GlobalTheory.Mem.R3.Rw.LiftRd

end
end

