module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1676
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0178
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0794
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComplEquivSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxPhaseMulBoxEqHeisenbergTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.BoxPhaseW

open GlobalTheory.RouteCoords GlobalTheory.RouteCoordsW GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation


set_option maxHeartbeats 1000000 in
theorem sympW : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (i j : ℕ) (e : Num G i j)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hW : Γ.V.J = (1 : D.host.E) • (spW G i j).gram)
    (hWW : Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e)
    (x x' : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)),
    GlobalTheory.WeilM.symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
                 (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) x x' =
      symplO (negSp (spW G i j)) (spV G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e x)ᵀ)
          (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e x')ᵀ) +
        symplO (spV₁ G i j) (spW G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e x) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e x') := by
  intro D T L sc G i j e Γ hW hWW x x'
  have hJW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J =
      incA D D.host.xi0 • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map (incA D))ᵀ ((spV₁ G i j).gram.map (incA D))ᵀ := by
    have k : incM Γ.W.J = incA D D.host.xi0 •
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (incM (spV G i j).gramᵀ) (incM (spV₁ G i j).gramᵀ) := by
      rw [hWW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, incM_smul]
      congr 1
      exact blk_map _ _ _ (map_zero _)
    exact k
  have hJV : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J = (spW G i j).gram.map (incA D) := by
    have k : incM Γ.V.J = incM (spW G i j).gram := by rw [hW, incM_smul, map_one, one_smul]
    exact k
  have hA : hTens (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) x x' = _ :=
    quadruple_sum_eq_trace_transpose_mul (cA D : AE D → AE D) _ _ _ _
  have hB1 : hO (negSp (spW G i j)) (spV G i j) (mulG (negSp (spW G i j)) (colV e x)ᵀ)
      (mulG (negSp (spW G i j)) (colV e x')ᵀ) = _ :=
    orientedHermitianForm_quadSum_eq_trace (cA D : AE D → AE D) (((negSp (spW G i j)).gram⁻¹).map (incA D)) ((spV G i j).gram.map (incA D)) _ _
  have hB2 : hO (spV₁ G i j) (spW G i j) (adjV₁ e x) (adjV₁ e x') = _ :=
    orientedHermitianForm_quadSum_eq_trace (cA D : AE D → AE D) (((spV₁ G i j).gram⁻¹).map (incA D)) ((spW G i j).gram.map (incA D)) _ _
  unfold symp symplO
  rw [hA, hB1, hB2]
  conv_rhs => arg 2; rw [← GlobalTheory.DualPairCheck.trace_cA]
  rw [← map_add (f := _)]
  congr 1
  have hg : (((-((spW G i j).gram.map (incA D))).map (cA D))ᵀ) = -((spW G i j).gram.map (incA D)) := by
    rw [Matrix.map_neg _ (map_neg _), transpose_neg, gram_conj_transpose]
  have hgi : -(((spW G i j).gram⁻¹).map (incA D)) * -((spW G i j).gram.map (incA D)) = 1 := by
    rw [neg_mul_neg, inv_mul_gram]
  have h1 := trace_first (cA D) (-((spW G i j).gram.map (incA D))) (-(((spW G i j).gram⁻¹).map (incA D)))
    ((spV G i j).gram.map (incA D)) hg hgi (colV e x) (colV e x')
  have h2 := trace_second_pos (cA D) GlobalTheory.DualPairCheck.cA_cA (incA D D.host.xi0) adeleConj_incl_skewElement_eq_neg ((spW G i j).gram.map (incA D))
    ((spV₁ G i j).gram.map (incA D)) (((spV₁ G i j).gram⁻¹).map (incA D)) (gram_conj_transpose _)
    (gram_conj_transpose _) (inv_mul_gram _) (x.submatrix id fun k => e (.inr k)) (x'.submatrix id fun k => e (.inr k))
  rw [negSp_gram_inv, Matrix.map_neg _ (map_neg _)]
  have hm : ∀ (S : HSp D) {n : ℕ} (y : Matrix (Fin n) (Fin S.rank) (AE D)), mulG S y = HMul.hMul y (S.gram.map (incA D)) :=
    fun _ _ _ => rfl
  have hadj : ∀ y : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D),
      adjV₁ e y = -mulG (spV₁ G i j) ((y.submatrix id fun k => e (.inr k)).map (cA D)) :=
    fun _ => rfl
  have hcol : ∀ y : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D),
      colV e y = y.submatrix id fun k => e (.inl k) := fun _ => rfl
  simp only [hadj, hm]
  rw [negSp_gram, Matrix.map_neg _ (map_neg _)]
  simp only [hcol] at h1
  erw [h2, h1]
  rw [hJW, hJV, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
    mul_blk_mul_transpose, trace_smul, Matrix.add_mul, trace_add,
    submatrix_map, submatrix_map, smul_eq_mul]
  simp only [transpose_neg, Matrix.mul_neg, trace_neg]
  ring

theorem mulG_colV_addW {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j)
    (x w : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e (x + w))ᵀ =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e x)ᵀ +
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e w)ᵀ := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV
  rw [← Matrix.add_mul]
  rfl

theorem adjV₁_addW {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j)
    (x w : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e (x + w) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e x + GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e w := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG
  rw [← neg_add, ← Matrix.add_mul]
  congr 2
  ext a b
  simp

theorem invOf_two_eq (F : Type) [Field F] [NumberField F] :
    ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  apply invOf_eq_right_inv
  rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
  norm_num

end GlobalTheory.BoxPhaseW

namespace GlobalTheory.BoxPhase

theorem phase_box_heis : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j), Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e → ∀ (ψ : AddChar (AF D.host.F) ℂ) (F₁ : WO (negSp (spW G i j)) (spV G i j) → ℂ) (F₂ : WO (spV₁ G i j) (spW G i j) → ℂ) (v w : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)), ψ (⅟(2 : AF D.host.F) * ((Γ.M.co.e v).1 ⬝ᵥ (Γ.M.co.e w).2 - (Γ.M.co.e w).1 ⬝ᵥ (Γ.M.co.e v).2)) * (F₁ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e (v + w))ᵀ) * F₂ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e (v + w))) = heisO ψ (negSp (spW G i j)) (spV G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e w)ᵀ) F₁ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mulG (negSp (spW G i j)) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.colV e v)ᵀ) * heisO ψ (spV₁ G i j) (spW G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e w) F₂ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.adjV₁ e v) := by
  intro D T L sc G i j e Γ hW hWW ψ F₁ F₂ v w
  rw [← Γ.M.co.form v w, GlobalTheory.BoxPhaseW.sympW i j e Γ hW hWW v w, GlobalTheory.BoxPhaseW.mulG_colV_addW,
    GlobalTheory.BoxPhaseW.adjV₁_addW, GlobalTheory.BoxPhaseW.invOf_two_eq]
  simp only [heisO, symplOH]
  rw [mul_add, AddChar.map_add_eq_mul]
  ring

end GlobalTheory.BoxPhase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefNodeIsV
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj

theorem defNode_isV {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (μ0 : T) (hL : L.Is μ0)
    (X : Node) (hX : DefNode D.R.m X) : (G.node X).IsV (X.rank D) 0 := by
  rcases X with ⟨i, j⟩ | i | j
  · obtain ⟨hi, rfl⟩ := hX
    rcases i with _ | i
    · have h := colY_isV D T L μ0 hL D.R.m le_rfl
      rw [Nat.sub_self, Nat.zero_div] at h
      exact h
    · have h := G.isV (X := .grid (i + 1) D.R.m) ⟨hi, le_rfl⟩ (fun j h => by cases h)
      simp only [Node.neg, Nat.sub_self, Nat.zero_div] at h
      exact h
  · exact absurd hX id
  · exact G.isV (X := .top j) hX (fun j' h => by cases h)

theorem unrIdem_mul {D : D7} {a b : (AE D)ˣ →* Circle} {e : AE D} (ha : UnrIdem a e) (hb : UnrIdem b e) :
    UnrIdem (a * b) e := fun x h1 h2 h3 => by
  rw [MonoidHom.mul_apply, ha x h1 h2 h3, hb x h1 h2 h3, one_mul]

theorem off_mono {D : D7} {S S' : Finset ℕ} (h : S ⊆ S') {w : Pl D.host.E} (hw : Off S' w) : Off S w :=
  fun q hq => hw q (h hq)


set_option maxHeartbeats 2000000 in
theorem exists_std {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (μ0 : T) (hL : L.Is μ0)
    (U : Set T) (hU : U.Finite) : Nonempty (Std G U) := by
  classical
  obtain ⟨S₁, hS₁p, hS₁⟩ := _root_.GlobalTheory.FunObj.exists_std_primes D T L sc G U hU
  have key : ∀ c : (AE D)ˣ →* Circle, ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧
      (Continuous c → ∀ w : Pl D.host.E, Off S w → ∀ e, Formalism.L2.NTheta.IsIdemAt e w → UnrIdem c e) := fun c => by
    by_cases hc : Continuous c
    · obtain ⟨S, h1, h2⟩ := _root_.GlobalTheory.UnrOff.unr_off D c hc
      exact ⟨S, h1, fun _ => h2⟩
    · exact ⟨∅, by simp, fun h => absurd h hc⟩
  choose Sc hScp hSc using key
  set S : Finset ℕ := S₁ ∪ (Finset.range (D.R.m + 1)).biUnion (fun j => Sc (L.mu0 j)) ∪
    hU.toFinset.biUnion (fun t => Sc (L.xi t)) with hSdef
  have hSp : ∀ q ∈ S, q.Prime := by
    intro q hq
    simp only [hSdef, Finset.mem_union, Finset.mem_biUnion] at hq
    rcases hq with (hq | ⟨j, -, hq⟩) | ⟨t, -, hq⟩
    · exact hS₁p q hq
    · exact hScp _ q hq
    · exact hScp _ q hq
  have hsub1 : S₁ ⊆ S := fun q hq => by simp [hSdef, hq]
  have hsubμ : ∀ j, j ≤ D.R.m → Sc (L.mu0 j) ⊆ S := fun j hj q hq => by
    simp only [hSdef, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
    exact Or.inl (Or.inr ⟨j, by omega, hq⟩)
  have hsubξ : ∀ t ∈ U, Sc (L.xi t) ⊆ S := fun t ht q hq => by
    simp only [hSdef, Finset.mem_union, Finset.mem_biUnion, Set.Finite.mem_toFinset]
    exact Or.inr ⟨t, ht, hq⟩
  have hcμ : ∀ j, 1 ≤ j → j ≤ D.R.m → Continuous (L.mu0 j) := fun j h1 h2 => by
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact (hL.mu0 ⟨k, by omega⟩).1.1
  have hV : ∀ X, DefNode D.R.m X → ∃ (fr : GL (Fin (G.V X).rank) D.host.E) (u : FinPt G X),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * (G.V X).gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e _ u.1 ∧ ∀ w ∈ P, Off S w) ∧
      ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE (G.V X) u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ X) := by
    intro X hX
    have h := defNode_isV G μ0 hL X hX
    exact GlobalTheory.T.exists_orthonormalBasis_splitSupported_adelicPoint D (G.V X) (G.Λ X) h.sigOK (fun τ => by rw [h.sig τ, h.rank, Nat.sub_zero]) h.sd S hSp
  choose fr0 u0 h0 using hV
  have hmm : DefNode D.R.m (.grid D.R.m D.R.m) := ⟨le_rfl, rfl⟩
  obtain ⟨frT, uT, hT1, hT2, hT3, hT4, hT5, hT6, hT7⟩ :=
    GlobalTheory.T.gridTopVertex_frame_point_transport_lattice D T L sc G S (fr0 _ hmm) (u0 _ hmm) (h0 _ hmm).1 (h0 _ hmm).2.1 (h0 _ hmm).2.2
  have hne : (Node.grid D.R.m D.R.m) ≠ Node.top D.R.m := fun h => by cases h
  obtain ⟨fr, frt, hfr⟩ : ∃ fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E, fr (.top D.R.m) = frT ∧
      ∀ X (hX : DefNode D.R.m X), X ≠ .top D.R.m → fr X = fr0 X hX :=
    ⟨Function.update (fun X => if h : DefNode D.R.m X then fr0 X h else 1) (.top D.R.m) frT,
      Function.update_self _ _ _, fun X hX hXt => by rw [Function.update_of_ne hXt, dite_eq_left hX]⟩
  obtain ⟨u, ut, hu⟩ : ∃ u : ∀ X : Node, FinPt G X, u (.top D.R.m) = uT ∧
      ∀ X (hX : DefNode D.R.m X), X ≠ .top D.R.m → u X = u0 X hX :=
    ⟨Function.update (fun X => if h : DefNode D.R.m X then u0 X h else 1) (.top D.R.m) uT,
      Function.update_self _ _ _, fun X hX hXt => by rw [Function.update_of_ne hXt, dite_eq_left hX]⟩
  have frmm := hfr _ hmm hne
  have hu_mm := hu _ hmm hne
  refine ⟨⟨S, hSp, ?_, ?_, fr, ?_, u, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun w hw => hS₁ w (off_mono hsub1 hw)
  · intro w hw e he t ht j h1 h2
    exact unrIdem_mul (hSc _ (hcμ j h1 h2) w (off_mono (hsubμ j h2) hw) e he)
      (hSc _ (hL.xi t).1.1 w (off_mono (hsubξ t ht) hw) e he)
  · intro X hX
    by_cases hXt : X = .top D.R.m
    · subst hXt; rw [frt]; exact hT1
    · have := hfr X hX hXt
      rw [this]; exact (h0 X hX).1
  · intro X hX
    by_cases hXt : X = .top D.R.m
    · subst hXt; rw [ut]; exact hT2
    · have := hu X hX hXt
      rw [this]; exact (h0 X hX).2.1
  · intro X hX
    by_cases hXt : X = .top D.R.m
    · subst hXt; rw [frt, ut]; exact hT3
    · have e1 := hfr X hX hXt
      have e2 := hu X hX hXt
      rw [e1, e2]; exact (h0 X hX).2.2
  · intro i k; rw [frt, frmm]; exact hT4 i k
  · intro i; rw [frt]; exact hT5 i
  · rw [ut, hu_mm]; exact hT6
  · rw [ut]; exact hT7

end GlobalTheory.FunObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleBasisChangeFactorMemField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFrames

open Formalism.L2.JoinChr


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem chr_mem_of_idemSum {K : Type} [Field K] {σ : K →+* ℂ} {D : D7} {c : (AE D)ˣ →* Circle}
    {χ : Formalism.L2.Host.HChar D.host.E} (hc : ChrEq c χ) (hχ : LocIn σ χ) {e : AE D}
    {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S) (x : (AE D)ˣ) (d : AE D)
    (hx : (x : AE D) = e * d + (1 - e)) : ((c x : Circle) : ℂ) ∈ σ.fieldRange := by
  classical
  obtain ⟨ι, h1, h2, h3⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨N, hN, hprod⟩ := GlobalTheory.CharLocProd.char_eq_prod_locK D ι h1 h2
    (GlobalTheory.PlaceIdem.exists_isPlIdem D ι h1 h2 h3) c χ hc
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have heT : ∀ P, ι (finPart D (∑ PP ∈ S, es PP)) P = if P ∈ S then 1 else 0 := by
    intro P
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, GlobalTheory.FlipCharFormula.fa_sum,
      Finset.sum_congr rfl (fun PP hPP => GlobalTheory.FlipCharFormula.comp_of_isIdemAt ι h1 h2 (hes PP hPP) P)]
    exact Finset.sum_ite_eq S P (fun _ => (1 : HeightOneSpectrum.adicCompletion D.host.E P))
  have hinfT : infPart D (∑ PP ∈ S, es PP) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero (fun PP hPP => GlobalTheory.FlipCharFormula.infPart_of_isIdemAt (hes PP hPP))
  have hinf : infPart D (x : AE D) = 1 := by
    rw [hx, map_add (f := _), map_mul, map_sub, hinfT, map_one, zero_mul, zero_add, sub_zero]
  have hout : ∀ P, P ∉ S → ι (finPart D (x : AE D)) P = 1 := by
    intro P hP
    rw [hx, map_add (f := _), map_mul, map_sub, map_one, map_add (f := _), map_mul, map_sub, map_one, GlobalTheory.FlipCharFormula.fa_add,
      GlobalTheory.FlipCharFormula.fa_mul, GlobalTheory.FlipCharFormula.fa_sub, GlobalTheory.FlipCharFormula.fa_one, heT, if_neg hP]
    simp
  have hne : ∀ P, ι (finPart D (x : AE D)) P ≠ 0 := by
    intro P h0
    have h := congrArg (fun z => ι (finPart D z) P) (Units.mul_inv x)
    simp only [map_mul, map_one, GlobalTheory.FlipCharFormula.fa_mul, GlobalTheory.FlipCharFormula.fa_one, h0, zero_mul] at h
    exact zero_ne_one h
  have hk : ∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ k : D.host.Eˣ,
      Valued.v (ι (finPart D (x : AE D)) P) = P.valuation D.host.E (k : D.host.E) ∧
      Valued.v (ι (finPart D (x : AE D)) P - algebraMap D.host.E _ (k : D.host.E)) ≤
        P.valuation D.host.E (N : D.host.E) * P.valuation D.host.E (k : D.host.E) := fun P => by
    obtain ⟨k, a, b, -⟩ := GlobalTheory.adicCompletion_exists_unit_approx D.host.E N hN P _ (hne P)
    exact ⟨k, a, b⟩
  choose k hk1 hk2 using hk
  have hI : Ideal.span {((N : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  have key := hprod x hinf (S ∪ (Ideal.finite_factors hI).toFinset) k (fun P _ => ⟨hk1 P, hk2 P⟩)
    (fun P hP => by
      have hPS : P ∉ S := fun h => hP (Finset.mem_union_left _ h)
      refine ⟨by rw [hout P hPS, map_one], fun hNP => hP (Finset.mem_union_right _ ?_)⟩
      rw [Set.Finite.mem_toFinset]
      exact Ideal.dvd_span_singleton.mpr hNP)
  rw [key]
  refine Subfield.prod_mem _ fun P _ => ?_
  rw [← SetLike.mem_coe, RingHom.coe_fieldRange]
  exact hχ P _


set_option maxHeartbeats 800000 in
theorem factor_mem_field : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (S : GridChoice W Set.univ)
    (μ₀ : T), L.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (A A' WW : HSp D) (Y : Tri T A A' WW),
    IsBottomTri W i j Y → ∀ (t : T) (g : GA D A) (g' : GA D A') (h : GA D WW) (x x' y : (AE D)ˣ),
    Formalism.L2.Theta.SuppAt (Y.e t) A g → Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β → Formalism.L2.Theta.IsDetAt (Y.e t) A g x →
    Formalism.L2.Theta.SuppAt (Y.e t) A' g' → Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β →
    Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x' →
    Formalism.L2.Theta.SuppAt (Y.e t) WW h → Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β → Formalism.L2.Theta.IsDetAt (Y.e t) WW h y →
    ∃ z : D.what₂.LLˣ, D.what₂.embLL z =
      ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) := by
  intro D T L sc G W S μ₀ hL hN i j A A' WW Y hY t g g' h x x' y _ _ hx _ _ hx' _ _ hy
  have he := hY.is.idem t
  have hm : 1 ≤ D.R.m - (i : ℕ) ∧ D.R.m - (i : ℕ) ≤ D.R.m := ⟨by omega, by omega⟩
  have mem : ∀ (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E), ChrEq c χ → LocIn D.what₂.embLL χ →
      ∀ (u : (AE D)ˣ) (d : AE D), (u : AE D) = Y.e t * d + (1 - Y.e t) → ((c u : Circle) : ℂ) ∈ D.what₂.embLL.fieldRange :=
    fun c χ hc hχ u d hu => chr_mem_of_idemSum hc hχ he u d hu
  have m1 := mem _ _ (hL.mu0 j) (hN.chars.mu0 j)
  have m2 := mem _ _ (hL.xi t) (hN.chars.xi t)
  have m3 := mem _ _ (G.ch.chi_eq _ hm.1 hm.2) (hN.chars.chi _ hm.1 hm.2)
  set a := L.mu0 ((j : ℕ) + 1)
  set b := L.xi t
  set c := G.ch.chi (D.R.m - (i : ℕ))
  set η := L.eta ^ (rankV D i j % 2)
  have hv : ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) =
      ((a x' : ℂ) * b x')⁻¹ * c x' * (((a x : ℂ) * b x)⁻¹ * c x) * ((a y : ℂ) * b y * (c y : ℂ)⁻¹) := by
    have e1 : GlobalTheory.BotFrames.botAlpha L i j t = a * b * η := rfl
    have e2 : GlobalTheory.BotFrames.botBeta G i j = c * η := rfl
    rw [e1, e2]
    simp only [splitFacO, MonoidHom.div_apply, MonoidHom.mul_apply, Circle.coe_mul, Circle.coe_inv, Circle.coe_div]
    have n1 := Circle.coe_ne_zero (a x'); have n2 := Circle.coe_ne_zero (b x'); have n3 := Circle.coe_ne_zero (c x')
    have n4 := Circle.coe_ne_zero (η x'); have n5 := Circle.coe_ne_zero (a x); have n6 := Circle.coe_ne_zero (b x)
    have n7 := Circle.coe_ne_zero (c x); have n8 := Circle.coe_ne_zero (η x); have n9 := Circle.coe_ne_zero (a y)
    have n10 := Circle.coe_ne_zero (b y); have n11 := Circle.coe_ne_zero (c y); have n12 := Circle.coe_ne_zero (η y)
    field_simp
  have hmem : (((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ)) ∈
      D.what₂.embLL.fieldRange := by
    rw [hv]
    refine mul_mem (mul_mem (mul_mem (inv_mem (mul_mem (m1 _ _ hx') (m2 _ _ hx'))) (m3 _ _ hx'))
      (mul_mem (inv_mem (mul_mem (m1 _ _ hx) (m2 _ _ hx))) (m3 _ _ hx)))
      (mul_mem (mul_mem (m1 _ _ hy) (m2 _ _ hy)) (inv_mem (m3 _ _ hy)))
  obtain ⟨z, hz⟩ := hmem
  have hne : ((splitFacO (GlobalTheory.BotFrames.botAlpha L i j t) (GlobalTheory.BotFrames.botAlpha L i j t / GlobalTheory.BotFrames.botBeta G i j) x' y : Circle)
        : ℂ) /
      ((splitFacO (GlobalTheory.BotFrames.botBeta G i j) (GlobalTheory.BotFrames.botBeta G i j / GlobalTheory.BotFrames.botAlpha L i j t) x y : Circle) : ℂ) ≠ 0 :=
    div_ne_zero (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at hz
    exact hne hz.symm
  exact ⟨Units.mk0 z hz0, hz⟩

end GlobalTheory.BotFrames

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
                       (∀ p, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ, om p φ ∈ GlobalTheory.WeilM.schA D.host.F κ) ∧
                       ∀ p w, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
                         om p (co.rho ψ w φ) = co.rho ψ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) p w) (om p φ) := by
  first | exact @GlobalTheory.WeilSchrodinger.PresImpl.pres_impl | exact GlobalTheory.WeilSchrodinger.PresImpl.pres_impl | (intros; apply GlobalTheory.WeilSchrodinger.PresImpl.pres_impl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeCorrespondingLattices
section
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitFlip GlobalTheory.FlipMatch GlobalTheory.FlipMatch.FieldTransport GlobalTheory.PureMatch.Transport

namespace GlobalTheory.PureMatch.Transport

theorem dualLat_latCorr {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {j : k ≃+* k'}
    {D D₂ : Type} [Fintype D] [Fintype D₂] (hj : IsLocIso j) (cD : D₂ ≃ D) {Λ : Submodule 𝒪[k] (D → k)}
    {Λ₂ : Submodule 𝒪[k'] (D₂ → k')} (h : LatCorr j cD Λ Λ₂) : LatCorr j cD (dualLat Λ) (dualLat Λ₂) := by
  have key : ∀ y x : D → k, (fun c => j (y (cD c))) ⬝ᵥ (fun c => j (x (cD c))) = j (y ⬝ᵥ x) := by
    intro y x
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [dotProduct, map_sum, map_mul]
    exact Fintype.sum_equiv cD _ _ fun c => rfl
  intro y
  rw [mem_dualLat, mem_dualLat]
  constructor
  · intro H x hx
    have := H _ ((h x).2 hx)
    rw [key] at this
    exact (hj.2.2 _).1 this
  · intro H x₂ hx₂
    set x : D → k := fun d => j.symm (x₂ (cD.symm d)) with hxdef
    have hx : (fun c => j (x (cD c))) = x₂ := by
      funext c; simp [x]
    rw [← hx] at hx₂ ⊢
    rw [key]
    exact (hj.2.2 _).2 (H x ((h x).1 hx₂))

end GlobalTheory.PureMatch.Transport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypeVectorOfGoodLevelRepresentationStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_typeVector_of_good_level_representation : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC (Yc D 0)) W), IsAdmissible σ → GlobalTheory.CuspMult.IsGoodRep (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) σ → ∃ T : TypeDataG (Yc D 0), NoFixed T ∧ HasTypeVec T σ := by
  first | exact @GlobalTheory.TypeVec.hasTypeVec_of_goodRep | exact GlobalTheory.TypeVec.hasTypeVec_of_goodRep | (intros; apply GlobalTheory.TypeVec.hasTypeVec_of_goodRep <;> assumption)
end

