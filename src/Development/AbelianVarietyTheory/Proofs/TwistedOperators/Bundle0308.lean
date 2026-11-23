module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapInfFinEquivEqProd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeIdempotentUnipotentIntegralVanishSplitPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0294
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedZetaSumGLCosets
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicAndConstantTerm
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.parabolic_and_constant_term

section Star

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem starFn_tensor (fa : ∀ w, GArch σ J w → ℂ) (ff : ∀ v, GLoc σ J v → ℂ) :
    starFn (tensor σ J fa ff) = tensor σ J (fun w => starFn (fa w)) (fun v => starFn (ff v)) := by
  funext g
  simp only [starFn, tensor, map_mul, map_prod, map_inv]
  congr 1
  exact MonoidHom.map_finprod_of_injective (starRingEnd ℂ).toMonoidHom (starRingEnd ℂ).injective _

theorem starFn_unitLoc (L : Submodule (𝓞 E) (Fin n → E)) (v : HeightOneSpectrum (𝓞 F)) :
    starFn (unitLoc σ J L v) = unitLoc σ J L v := by
  funext g
  by_cases hg : g ∈ stabLoc σ J L v
  · simp [starFn, unitLoc, hg, Set.indicator_of_mem, inv_mem hg]
  · have : g⁻¹ ∉ stabLoc σ J L v := fun h => hg (by simpa using inv_mem h)
    simp [starFn, unitLoc, hg, this]

theorem isFinFamily_starFn {L : Submodule (𝓞 E) (Fin n → E)} {ff : ∀ v, GLoc σ J v → ℂ}
    (h : IsFinFamily σ J L ff) : IsFinFamily σ J L (fun v => starFn (ff v)) :=
  ⟨fun v => starFn_mem_SB (h.1 v), h.2.mono fun v hv => by simp only [hv, starFn_unitLoc]⟩

end Star

theorem inConjParabolic_mono {k : Type} [Field k] {r : ℕ} {H H' : Subgroup (GL (Fin r) k)} (h : H ≤ H') {a : ℕ}
    (h' : InConjParabolic H' a) : InConjParabolic H a :=
  let ⟨g, hg⟩ := h'; ⟨g, fun p hp => hg p (h hp)⟩

theorem parabolicAtSplitPlaces : ParabolicAtSplitPlaces := by
  intro D V hodd T 𝔉 hP
  let i : Fin (𝔉.k + 1) := ⟨1, Nat.succ_lt_succ hP⟩
  have hi : i ≠ 0 := Fin.ne_of_val_ne one_ne_zero
  have hW := 𝔉.isIsotropic hi
  obtain ⟨h0, h2⟩ := _root_.GlobalTheory.IsoDim.isotropic_dim_bounds D V hodd _ hW
  refine ⟨_, h0, h2, fun v => ?_⟩
  have hle : parAt 𝔉 (T.frame v) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (Fv D.host.F v.1) (𝔉.X i)).map
      ((T.frame v).equiv : GLoc D.sp.cm.sig V.gram v.1 →* GL (Fin V.rank) (Fv D.host.F v.1)) :=
    Subgroup.map_mono (𝔉.par_le_parab _ _ i)
  obtain ⟨h3, h4⟩ := _root_.GlobalTheory.SplitStab.splitStab D V v.1 (T.frame v) _ hW
  exact ⟨inConjParabolic_mono hle h3, inConjParabolic_mono hle h4⟩

end GlobalTheory.Proof.parabolic_and_constant_term

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.PolMatchLin

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Ext
variable {ι : Type} (P : ι → Type) [∀ v, AddCommGroup (P v)] [∀ v, Module ℂ (P v)]


open Classical in
def extFam {S T : Finset ι} (w : ∀ v, P v) (g : ∀ v : S, P v) : ∀ v : T, P v :=
  fun v => if h : v.1 ∈ S then g ⟨v.1, h⟩ else w v.1

theorem extFam_update {S T : Finset ι} (hST : S ⊆ T) (w : ∀ v, P v) [DecidableEq S] [DecidableEq T]
    (g : ∀ v : S, P v) (i : S) (z : P i) :
    extFam P (T := T) w (Function.update g i z) = Function.update (extFam P w g) ⟨i.1, hST i.2⟩ z := by
  funext v
  by_cases hv : v = ⟨i.1, hST i.2⟩
  · subst hv
    simp [extFam, i.2]
  · rw [Function.update_of_ne hv]
    unfold extFam
    split_ifs with h
    · rw [Function.update_of_ne]
      intro e
      apply hv
      apply Subtype.ext
      simp [← e]
    · rfl

def extML {S T : Finset ι} (hST : S ⊆ T) (w : ∀ v, P v) :
    MultilinearMap (RingHom.id ℂ) (fun v : S => P v) (PiTensorProduct ℂ fun v : T => P v) where
  toFun g := PiTensorProduct.tprod ℂ (extFam P w g)
  map_update_add' g i x y := by
    classical
    simp only [extFam_update P hST]
    exact MultilinearMap.map_update_add _ _ _ _ _
  map_update_smul' g i c x := by
    classical
    simp only [extFam_update P hST]
    exact MultilinearMap.map_update_smul _ _ _ _ _

def extL {S T : Finset ι} (hST : S ⊆ T) (w : ∀ v, P v) :
    (PiTensorProduct ℂ fun v : S => P v) →ₗ[ℂ] PiTensorProduct ℂ fun v : T => P v :=
  PiTensorProduct.lift (extML P hST w)

theorem extL_tprod {S T : Finset ι} (hST : S ⊆ T) (w : ∀ v, P v) (g : ∀ v : S, P v) (g' : ∀ v : T, P v)
    (h1 : ∀ (v : T) (h : v.1 ∈ S), g' v = g ⟨v.1, h⟩) (h2 : ∀ v : T, v.1 ∉ S → g' v = w v.1) :
    extL P hST w (PiTensorProduct.tprod ℂ g) = PiTensorProduct.tprod ℂ g' := by
  unfold extL
  rw [PiTensorProduct.lift.tprod]
  show PiTensorProduct.tprod ℂ (extFam P w g) = _
  congr 1
  funext v
  unfold extFam
  split_ifs with h
  · exact (h1 v h).symm
  · exact (h2 v h).symm

end Ext

section Main

theorem pure_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, smul_eq_mul, mul_assoc]

theorem transport {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {a a' : ℕ} (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a') (hF : IsFinMaps B G X om om' Rf)
    {T₁ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))} (hX : X.T ⊆ T₁) (hST : T₁ ⊆ T) {m m' : ℕ} (f : Fin m → SInf F (Fin a × Fin (a + a')))
    (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a × Fin (a + a') → Fv F v) → ℂ) (f' : Fin m' → SInf F (Fin a' × Fin (a + a')))
    (φ' : Fin m' → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ)
    (hφ : ∀ i, ∀ v ∉ T₁, φ i v = G.M.vac v) (hφ' : ∀ j, ∀ v ∉ T₁, φ' j v = G.M'.vac v)
    (he : ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T₁ => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T₁ => Rf.p' v (φ' j v))) :
    ∑ i, R.p (f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v)) =
      ∑ j, R.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v)) := by
  set w : ∀ v, Rf.Pi v := fun v => Rf.p v (G.M.vac v)
  have k1 : ∀ i, extL Rf.Pi hST w (PiTensorProduct.tprod ℂ fun v : T₁ => Rf.p v (φ i v)) =
      PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φ i v) := fun i =>
    extL_tprod _ _ _ _ _ (fun v h => rfl) (fun v h => by simp only [w]; rw [hφ i v h])
  have k2 : ∀ j, extL Rf.Pi hST w (PiTensorProduct.tprod ℂ fun v : T₁ => Rf.p' v (φ' j v)) =
      PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φ' j v) := fun j =>
    extL_tprod _ _ _ _ _ (fun v h => rfl) (fun v h => by
      simp only [w]; rw [hφ' j v h, (hF.sph v.1 (fun hv => h (hX hv))).1])
  have := congrArg (LinearMap.lTensor R.Pi (extL Rf.Pi hST w)) he
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.lTensor_tmul, k1, k2] at this
  exact this

theorem polMatch_linear : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsFinMaps B G X om om' Rf → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf 0 0 ∧ ∀ (Φ Ψ : (Fin a × Fin (a + a') → AF F) → ℂ) (Φ' Ψ' : (Fin a' × Fin (a + a') → AF F) → ℂ) (c : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Ψ Ψ' → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf (Φ + c • Ψ) (Φ' + c • Ψ') := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf hF
  refine ⟨?_, ?_⟩
  · refine ⟨X.T, subset_rfl, 0, 0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  · rintro Φ Ψ Φ' Ψ' c ⟨T₁, hX₁, m₁, m₁', f₁, φ₁, f₁', φ₁', h1, h1', rfl, rfl, e1⟩
      ⟨T₂, hX₂, m₂, m₂', f₂, φ₂, f₂', φ₂', h2, h2', rfl, rfl, e2⟩
    classical
    have s1 : T₁ ⊆ T₁ ∪ T₂ := Finset.subset_union_left
    have s2 : T₂ ⊆ T₁ ∪ T₂ := Finset.subset_union_right
    refine ⟨T₁ ∪ T₂, hX₁.trans s1, m₁ + m₂, m₁' + m₂', Fin.append f₁ (fun j => c • f₂ j), Fin.append φ₁ φ₂,
      Fin.append f₁' (fun j => c • f₂' j), Fin.append φ₁' φ₂', ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]
        exact ⟨(h1 i).1, (h1 i).2.1, fun v hv => (h1 i).2.2 v (fun h => hv (s1 h))⟩
      · simp only [Fin.append_right]
        exact ⟨Submodule.smul_mem _ c (h2 j).1, (h2 j).2.1, fun v hv => (h2 j).2.2 v (fun h => hv (s2 h))⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]
        exact ⟨(h1' i).1, (h1' i).2.1, fun v hv => (h1' i).2.2 v (fun h => hv (s1 h))⟩
      · simp only [Fin.append_right]
        exact ⟨Submodule.smul_mem _ c (h2' j).1, (h2' j).2.1, fun v hv => (h2' j).2.2 v (fun h => hv (s2 h))⟩
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, pure_smul, Finset.smul_sum]
    · rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, pure_smul, Finset.smul_sum]
    · rw [Fin.sum_univ_add, Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, map_smul, ← TensorProduct.smul_tmul', ← Finset.smul_sum]
      rw [transport B G X om om' R Rf hF hX₁ s1 f₁ φ₁ f₁' φ₁' (fun i v hv => (h1 i).2.2 v hv)
          (fun j v hv => (h1' j).2.2 v hv) e1,
        transport B G X om om' R Rf hF hX₂ s2 f₂ φ₂ f₂' φ₂' (fun i v hv => (h2 i).2.2 v hv)
          (fun j v hv => (h2' j).2.2 v hv) e2]

end Main

end GlobalTheory.PolMatchLin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchOnto
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree

theorem polMatch_onto : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ} (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Φ ∈ algD G.M B.ψ B.emb, ∃ Φ' ∈ algD G.M' B.ψ B.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf Φ Φ' := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf hM Φ hΦ
  classical
  obtain ⟨n, c, g, rfl⟩ := (Submodule.mem_span_set').1 hΦ
  choose f φ hf hφ hfin hg using fun i => (g i).2
  have hfin' : ∀ i, {v | ¬ φ i v = G.M.vac v}.Finite := fun i => Filter.eventually_cofinite.1 (hfin i)
  set T : Finset (Pl F) := X.T ∪ Finset.univ.biUnion (fun i => (hfin' i).toFinset) with hT
  have hout : ∀ i, ∀ v ∉ T, φ i v = G.M.vac v := by
    intro i v hv
    by_contra h
    exact hv (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, (hfin' i).mem_toFinset.2 h⟩))
  have hreal : ∀ i, ∃ f' ∈ G.M'.Pol B.ψ B.emb, R.p' f' = R.p (c i • f i) := by
    intro i
    have : R.p (c i • f i) ∈ (G.M'.Pol B.ψ B.emb).map R.p' := by rw [hM.real.quot'.onto]; trivial
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 this
    exact ⟨y, hy, e⟩
  choose f' hf' hf'eq using hreal
  have hloc : ∀ i v, ∃ y ∈ GlobalTheory.WeilM.SB _, Rf.p' v y = Rf.p v (φ i v) := by
    intro i v
    have : Rf.p v (φ i v) ∈ (GlobalTheory.WeilM.SB _).map (Rf.p' v) := by rw [hM.fin.onto' v]; trivial
    obtain ⟨y, hy, e⟩ := Submodule.mem_map.1 this
    exact ⟨y, hy, e⟩
  choose φ₀ hφ₀ hφ₀eq using hloc
  let φ' : Fin n → ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ :=
    fun i v => if v ∈ T then φ₀ i v else G.M'.vac v
  have hvac' : ∀ v, G.M'.vac v ∈ GlobalTheory.WeilM.SB _ := fun v => (hM.triple.geo.hM'.vac v).1
  have hφ'SB : ∀ i v, φ' i v ∈ GlobalTheory.WeilM.SB _ := by
    intro i v
    by_cases hv : v ∈ T
    · simpa only [φ', ite_eq_left hv] using hφ₀ i v
    · simpa only [φ', ite_eq_right hv] using hvac' v
  have hφ'out : ∀ i, ∀ v ∉ T, φ' i v = G.M'.vac v := by
    intro i v hv; simp only [φ', ite_eq_right hv]
  have hpure : ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c i • f i) (φ i) = c i • (g i : (Fin a × Fin (a + a') → AF F) → ℂ) := by
    intro i
    rw [hg i]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
  refine ⟨∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f' i) (φ' i), ?_, T, Finset.subset_union_left, n, n, fun i => c i • f i, φ, f', φ', ?_, ?_, ?_, rfl, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f' i, φ' i, hf' i, hφ'SB i, ?_, rfl⟩
    exact Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by
      by_contra h; exact hv (hφ'out i v h))
  · exact fun i => ⟨Submodule.smul_mem _ _ (hf i), hφ i, hout i⟩
  · exact fun i => ⟨hf' i, hφ'SB i, hφ'out i⟩
  · exact Finset.sum_congr rfl fun i _ => (hpure i).symm
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf'eq i]
    apply congrArg (fun z => R.p (c i • f i) ⊗ₜ[ℂ] z)
    apply congrArg (PiTensorProduct.tprod ℂ)
    funext v
    simp only [φ', ite_eq_left v.property]
    exact (hφ₀eq i v).symm

end GlobalTheory.SquareAgree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorInnerProductEqFinprodLocalInnerProduct
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.PlaceTensor.PureScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem wAt_zero {m n : ℕ} (p : Place D) : wAt p (0 : Mx D m n) = 0 := by
  rw [wAt_eq_smul, smul_zero]

theorem wAt_neg_wAt_self {m n : ℕ} (q : Place D) (w : Mx D m n) : wAt q (-(wAt q w)) = -(wAt q w) := by
  have hq : idem D q * idem D q = idem D q := (_root_.GlobalTheory.PlaceTensor.idem_spec D).1 q
  rw [wAt_eq_smul, wAt_eq_smul, smul_neg, smul_smul, hq]

theorem wAt_neg_wAt_ne {m n : ℕ} {p q : Place D} (hpq : p ≠ q) (w : Mx D m n) : wAt p (-(wAt q w)) = 0 := by
  have hpq' : idem D p * idem D q = 0 := (_root_.GlobalTheory.PlaceTensor.idem_spec D).2.1 p q hpq
  rw [wAt_eq_smul, wAt_eq_smul, smul_neg, smul_smul, hpq', zero_smul, neg_zero]

section

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f₀ : WO S T → ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem ip_base (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) : ipO μ 𝓕 f₀ f₀ = 1 := by
  have hself : ipO μ 𝓕 f₀ f₀ = (nrm2 μ 𝓕 f₀ : ℂ) :=
    (_root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 (base_std hb) hμ f₀ f₀ (base_theta hb) (base_theta hb)).2.2.2.2.1
  rw [hself, restrictedTensorBasePoint_norm_sq hb hμ, Complex.ofReal_one]

theorem finite_mulSupport_ip (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕)
    {x₁ x₂ : Place D → WO S T → ℂ} (h₁ : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x₁)
    (h₂ : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ x₂) :
    (Function.mulSupport fun p => ipO μ 𝓕 (x₁ p) (x₂ p)).Finite := by

  refine (h₁.2.union h₂.2).subset fun p hp => ?_
  rw [Function.mem_mulSupport] at hp
  by_contra hout
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hout
  exact hp (by rw [hout.1, hout.2]; exact ip_base hb hμ)

private theorem heisO_zero_twisted_operators (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext u
  simp [heisO, symplOH, symplO, hO]

theorem pureTensor_innerProduct_eq_finprod_local_of_finset (hb : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (s : Finset (Place D)) :
    ∀ (x₁ x₂ : Place D → WO S T → ℂ) (f₁ f₂ : WO S T → ℂ), (∀ p, p ∉ s → x₁ p = f₀) →
      IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ →
      ipO μ 𝓕 f₁ f₂ = ∏ᶠ p, ipO μ 𝓕 (x₁ p) (x₂ p) := by
  classical
  have hθ₀ : IsThetaFunO ψ S T f₀ := base_theta hb

  have hsymm : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ipO μ 𝓕 g f = (starRingEnd ℂ) (ipO μ 𝓕 f g) :=
    fun f g hf hg => (_root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 (base_std hb) hμ f g hf hg).2.1
  have hadj : ∀ f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → ∀ w,
      ipO μ 𝓕 (heisO ψ S T w f) g = ipO μ 𝓕 f (heisO ψ S T (-w) g) :=
    fun f g hf hg w => ((_root_.GlobalTheory.ThetaPairingLaws.ipO_laws D ψ S T μ 𝓕 (base_std hb) hμ f g hf hg).2.2.2.2.2.2.1 w).2
  induction s using Finset.induction_on with
  | empty =>

    intro x₁ x₂ f₁ f₂ hx h₁ h₂
    have hx₁ : x₁ = fun _ => f₀ := funext fun p => hx p (by simp)
    subst hx₁
    have hf₁ : f₁ = f₀ :=
      (_root_.GlobalTheory.PureTensorExists.existsUnique_isPure D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ h₁.1).unique h₁
        (_root_.GlobalTheory.LocalPure.isPure_base_and_local D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ).1
    subst hf₁
    obtain ⟨hfin, hprod⟩ := h₂.2.2 0
    simp only [wAt_zero, heisO_zero_twisted_operators] at hfin hprod
    rw [hsymm f₂ f₁ h₂.2.1 hθ₀, hprod, map_finprod _ hfin]
    exact finprod_congr fun p => (hsymm (x₂ p) f₁ (h₂.1.1 p).1 hθ₀).symm
  | insert q s hq ih =>
    intro x₁ x₂ f₁ f₂ hx h₁ h₂

    have hres : IsRestricted ψ θ S T sS sT ΛS ΛT f₀ (Function.update x₁ q f₀) := by
      refine ⟨fun p => ?_, h₁.1.2.subset fun p hp => ?_⟩
      · by_cases hpq : p = q
        · subst hpq
          rw [Function.update_self]
          exact base_isLocal hb p
        · rw [Function.update_of_ne hpq]
          exact h₁.1.1 p
      · by_cases hpq : p = q
        · subst hpq
          simp at hp
        · simpa [Function.update_of_ne hpq] using hp
    have hoff : ∀ p, p ∉ s → Function.update x₁ q f₀ p = f₀ := by
      intro p hp
      by_cases hpq : p = q
      · subst hpq
        exact Function.update_self _ _ _
      · rw [Function.update_of_ne hpq]
        exact hx p (by simp [hpq, hp])
    obtain ⟨g₁, hg₁, -⟩ := _root_.GlobalTheory.PureTensorExists.existsUnique_isPure D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ hres

    obtain ⟨f', hf', hc⟩ := _root_.GlobalTheory.PlaceTensorStep.change_factor D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ (Function.update x₁ q f₀) x₁ g₁ q hg₁
      (Function.update_self _ _ _) (fun p hp => (Function.update_of_ne hp _ _).symm) (h₁.1.1 q)
    have hf'₁ : f' = f₁ := (_root_.GlobalTheory.PureTensorExists.existsUnique_isPure D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ _ h₁.1).unique hf' h₁
    subst hf'₁
    have hθq : IsThetaFunO ψ S T (x₂ q) := (h₂.1.1 q).1
    have key := hc f₂ (x₂ q) (∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x₁ p) (x₂ p)) h₂.2.1 hθq (fun w => by
      rw [hadj g₁ f₂ hg₁.2.1 h₂.2.1]
      have hpw := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ x₂ f₂ h₂ (-(wAt q w))
      rw [ih _ _ _ _ hoff hg₁ hpw, ← mul_finprod_cond_ne q (finite_mulSupport_ip hb hμ hres hpw.1),
        Function.update_self, wAt_neg_wAt_self, ← hadj f₀ (x₂ q) hθ₀ hθq, mul_comm]
      congr 1
      refine finprod_congr fun p => finprod_congr fun hp => ?_
      rw [Function.update_of_ne hp, wAt_neg_wAt_ne hp, heisO_zero_twisted_operators])
    rw [key, mul_comm]
    exact mul_finprod_cond_ne q (finite_mulSupport_ip hb hμ h₁.1 h₂.1)

end

theorem ip_pure_eq_finprod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x₁ x₂ : Place D → WO S T → ℂ) (f₁ f₂ : WO S T → ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₁ f₁ → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x₂ f₂ → (Function.mulSupport fun p => ipO μ 𝓕 (x₁ p) (x₂ p)).Finite ∧ ipO μ 𝓕 f₁ f₂ = ∏ᶠ p, ipO μ 𝓕 (x₁ p) (x₂ p) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hb hμ x₁ x₂ f₁ f₂ h₁ h₂
  refine ⟨finite_mulSupport_ip hb hμ h₁.1 h₂.1, ?_⟩

  exact pureTensor_innerProduct_eq_finprod_local_of_finset hb hμ h₁.1.2.toFinset x₁ x₂ f₁ f₂
    (fun p hp => by simpa [Set.Finite.mem_toFinset] using hp) h₁ h₂

end GlobalTheory.PlaceTensor.PureScalar

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevSeminormWeilThetaPolynomialInHeightStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolevSeminorm_weilTheta_polynomial_in_height : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ) (ε : Bool) (M X : HSp D)
    (χ χ' : (AE D)ˣ →* Circle) (ω : WRep M X) (hω : IsWeil ψ ε M X χ χ' ω) (Φ : WO M X → ℂ) (hΦ : IsThetaFunO ψ (sgn ε M) X Φ)
    (C₁ : Set (GA D M)) (hC₁ : IsCompact C₁)
    (μ : Measure (WO (sgn ε M) X)) (𝓕 : Set (WO (sgn ε M) X)) (hμ : IsCovolOne (ratL X (sgn ε M)) μ 𝓕) (k : ℕ),
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ y ∈ C₁, ∀ h : GA D X,
      (GlobalTheory.Size.sobO (V := sgn ε M) (W := X) ψ θ μ 𝓕 k (ω (y, h) Φ)).toReal ≤
        C * (GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies.height θ X h : ℝ) ^ N := by
  first | exact @GlobalTheory.WeilSobolev.sobO_weil_le_height | exact GlobalTheory.WeilSobolev.sobO_weil_le_height | (intros; apply GlobalTheory.WeilSobolev.sobO_weil_le_height <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedZetaSumGLCosetsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_zeta_sum_GL_cosets : GlobalTheory.Published.UnramifiedDoublingGL → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (r t : ℕ), r ≤ t → ∀ (z : ℂˣ) (φ : GL (Fin r) (w.adicCompletion E) → ℂ), ‖(z : ℂ)‖ = 1 → KerGL w (r + t) z φ → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin r) (w.adicCompletion E)) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B → (∀ β ∈ B, ‖(β : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2) ∧ ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV E w : ℝ) ^ (((r : ℝ) - 1) / 2)) → ∀ ℓ : V →ₗ[ℂ] ℂ, (∃ C : ℝ, ∀ g, ‖ℓ (ρ g x)‖ ≤ C) → HasSum (fun a : GL (Fin r) (w.adicCompletion E) ⧸ KGL w (n := r) => φ a.out * ℓ (ρ a.out x)) (eulerFac (B.map (z * ·)) (npow w (-((1 + (t : ℂ)) / 2))) * eulerFac (B.map fun β => (z * β)⁻¹) (npow w (-((1 + (t : ℂ)) / 2))) * (∏ i ∈ Finset.Ioc t (r + t), (1 - ((qV E w : ℂ) ^ i)⁻¹)) * ℓ x) := by
  first | exact @GlobalTheory.ZetaGL.zeta_sum_GL | exact GlobalTheory.ZetaGL.zeta_sum_GL | (intros; apply GlobalTheory.ZetaGL.zeta_sum_GL <;> assumption)
end

