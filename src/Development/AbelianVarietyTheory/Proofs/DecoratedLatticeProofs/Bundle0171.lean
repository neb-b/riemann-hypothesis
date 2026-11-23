module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0158

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemWittStabilizerOfKeepsIsotropicRealPlaces
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG

noncomputable section

namespace GlobalTheory.Core.Rk.IwGlob

open GlobalTheory.MixModel
open scoped TensorProduct

theorem tens_prod_ext {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] {z z' : (A × B) ⊗[F] E}
    (a : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z')
    (b : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z') : z = z' := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [hz z, hz z', a, b]

theorem adTens_ext {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {z z' : AF F ⊗[F] E}
    (h1 : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.compInf F E w z = GlobalTheory.AdelicU.compInf F E w z')
    (h2 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z') : z = z' := by
  refine tens_prod_ext (A := Ainf F) (B := Af F) (GlobalTheory.AutFunCompare.infTens_ext fun w => ?_) h2
  have e : ∀ y : AF F ⊗[F] E, Algebra.TensorProduct.map (GlobalTheory.AutFunCompare.evW w) (AlgHom.id F E)
      (Algebra.TensorProduct.map (AlgHom.fst F (Ainf F) (Af F)) (AlgHom.id F E) y) =
      GlobalTheory.AdelicU.compInf F E w y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => erw [map_zero]
    | tmul a x => rfl
    | add x y hx hy => erw [map_add, map_add, map_add, hx, hy]
  rw [e, e]
  exact h1 w

theorem map_mul_eq_of_keeps {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R) {n r : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (X : Matrix (Fin n) (Fin r) A) (P : Matrix (Fin r) (Fin n) A)
    (hPX : P * X = 1) (β : Matrix (Fin r) (Fin r) R) (h : M.map φ * X.map φ = X.map φ * β) :
    (M * X).map φ = (X * (P * M * X)).map φ := by
  have hPX' : P.map φ * X.map φ = 1 := by
    rw [← Matrix.map_mul, hPX, Matrix.map_one _ (map_zero φ) (map_one φ)]
  simp only [Matrix.map_mul]
  rw [h, Matrix.mul_assoc (P.map φ), h, ← Matrix.mul_assoc (P.map φ), hPX', Matrix.one_mul]

theorem mat_projArch {D : D7} {T : HSp D} (q : GA D T) (w : InfinitePlace D.host.F) :
    (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig T.gram (GlobalTheory.AdelicU.projArch D.sp.cm.sig T.gram w q)).1 =
                 (Formalism.L2.Theta.mt T q).map (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) :=
  Matrix.ext fun _ _ => rfl

theorem mt_inv_mul_self {D : D7} {T : HSp D} (q : GA D T) :
    Formalism.L2.Theta.mt T q⁻¹ * Formalism.L2.Theta.mt T q = 1 := by
  show (Formalism.L2.Theta.matHom T q⁻¹).1 * (Formalism.L2.Theta.matHom T q).1 = 1
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

theorem keeps_map {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (w : InfinitePlace D.host.F)
    (β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E))
    (h : (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) :
    (Formalism.L2.Theta.mt T q).map (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) * Matrix.map d.jX (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) =
      Matrix.map d.jX (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) * β := by
  rw [← mat_projArch q w]
  exact h

theorem arch_comp {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (w : InfinitePlace D.host.F)
    (β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E))
    (h : (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β)
    (i : Fin T.rank) (j : Fin r) :
    GlobalTheory.AdelicU.compInf D.host.F D.host.E w ((Formalism.L2.Theta.mt T q ⬝ d.jX) i j) =
      GlobalTheory.AdelicU.compInf D.host.F D.host.E w ((d.jX ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX)) i j) := by
  have h2 := keeps_map d q w β h
  have h3 := map_mul_eq_of_keeps (GlobalTheory.AdelicU.compInf D.host.F D.host.E w) (Formalism.L2.Theta.mt T q) d.jX d.pX
    d.pX_jX β h2
  rw [← Matrix.map_apply (f := GlobalTheory.AdelicU.compInf D.host.F D.host.E w), h3]
  rfl

theorem mul_jX_eq {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T) (hq : q ∈ GinfC T)
    (hw : ∀ w : InfinitePlace D.host.F, ∃ β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E), (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) :
    Formalism.L2.Theta.mt T q ⬝ d.jX = d.jX ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX) := by
  let φf : AE D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
    (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom
  have hf : (Formalism.L2.Theta.mt T q).map φf = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hq)
  have hfin := map_mul_eq_of_keeps φf (Formalism.L2.Theta.mt T q) d.jX d.pX d.pX_jX 1
    (by rw [hf, Matrix.one_mul, Matrix.mul_one])
  funext i j
  exact adTens_ext (F := D.host.F) (E := D.host.E) (fun w => Exists.elim (hw w) fun β hβ => arch_comp d q w β hβ i j)
    (congrFun (congrFun hfin i) j)

theorem mem_stab_of_keeps : ∀ {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (q : GA D T), q ∈ GinfC T → (∀ w : InfinitePlace D.host.F, ∃ β : Matrix (Fin r) (Fin r) (TensorProduct D.host.F w.Completion D.host.E), (matHom _ D.sp.cm.sig T.gram (projArch D.sp.cm.sig T.gram w q)).1 * Matrix.map d.jX (compInf D.host.F D.host.E w) = Matrix.map d.jX (compInf D.host.F D.host.E w) * β) → q ∈ stab d := by
  intro D T T₀ r d q hq hw
  have hPX : d.pX ⬝ d.jX = 1 := d.pX_jX
  have key := mul_jX_eq d q hq hw
  have hinv : Formalism.L2.Theta.mt T q⁻¹ ⬝ Formalism.L2.Theta.mt T q = 1 := mt_inv_mul_self q
  have h1 : (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹ ⬝ d.jX) ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX) = 1 := by
    calc (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹ ⬝ d.jX) ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX)
        = (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹) ⬝ (d.jX ⬝ (d.pX ⬝ Formalism.L2.Theta.mt T q ⬝ d.jX)) := by
          rw [Matrix.mul_assoc]
      _ = (d.pX ⬝ Formalism.L2.Theta.mt T q⁻¹) ⬝ (Formalism.L2.Theta.mt T q ⬝ d.jX) := by rw [← key]
      _ = d.pX ⬝ ((Formalism.L2.Theta.mt T q⁻¹ ⬝ Formalism.L2.Theta.mt T q) ⬝ d.jX) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hinv, Matrix.one_mul, hPX]
  exact ⟨⟨_, _, mul_eq_one_comm.mp h1, h1⟩, key⟩

end GlobalTheory.Core.Rk.IwGlob
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceEquivariantRealPointsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicitySpace_equivariant_real_points : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ (v : M.Vec) (b : GinfC V), ∃ w : M.Vec, (∀ τ, (w τ : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) (b : GA D V)) (v τ : M.H τ)) ∧ ∀ U ∈ Mult θ M J χ, U w = rTr V (b : GA D V) (U v) := by
  intro D θ V Sp M J χ hθ v b
  classical
  let g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ :=
    fun τ => infMat D.sp.cm.sig V.gram (θ τ) (b : GA D V)
  have hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun τ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V (b : GA D V) τ
  let w : M.Vec := fun τ => ⟨M.rep τ (g τ) (v τ : M.H τ),
    GlobalTheory.SmoothStable.rep_mem_sm D V Sp M τ (g τ) (hg τ) _ (v τ).2⟩
  have hb : GlobalTheory.AdelicScalar.realElt θ V g = (b : GA D V) := by
    have hR := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
    refine hR.2.2.1 _ (GlobalTheory.RealLift.prodAt_mem θ V _ g) _ b.2 fun τ => ?_
    have h := GlobalTheory.RealLift.infMat_prodAt hθ V (u := g) hg τ _
      (Finset.nodup_toList Finset.univ)
    rw [if_pos (Finset.mem_toList.2 (Finset.mem_univ _))] at h
    exact h
  refine ⟨w, fun τ => rfl, fun U hU => ?_⟩
  rw [← hb]
  induction hU using Submodule.span_induction with
  | mem U hU =>
    have equivOnList (l : List D.what₂.Tau) (hl : l.Nodup) :
        U (fun τ => if τ ∈ l then w τ else v τ) =
          rTr V (l.map fun τ => atTau θ V τ (g τ)).prod (U v) := by
      induction l with
      | nil =>
        funext x
        simp [rTr]
      | cons τ l ih =>
        rw [List.nodup_cons] at hl
        have h := hU.equiv τ (g τ) (hg τ) (fun ρ => if ρ ∈ l then w ρ else v ρ) (w τ) (by
          simp only [if_neg hl.1]
          rfl)
        rw [ih hl.2] at h
        have hprod : rTr V ((τ :: l).map fun ρ => atTau θ V ρ (g ρ)).prod (U v) =
            rTr V (atTau θ V τ (g τ)) (rTr V (l.map fun ρ => atTau θ V ρ (g ρ)).prod (U v)) := by
          funext x
          simp only [rTr, List.map_cons, List.prod_cons, mul_assoc]
        rw [hprod, ← h]
        congr 1
        funext ρ
        by_cases hρ : ρ = τ
        · subst ρ
          simp
        · rw [Function.update_of_ne hρ]
          simp [hρ]
    have h := equivOnList (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _)
    rw [GlobalTheory.AdelicScalar.realElt, ← h]
    congr 1
    funext τ
    simp
  | zero =>
    funext x
    simp [rTr]
  | add U U' _ _ h1 h2 =>
    funext x
    have h1x := congrFun h1 x
    have h2x := congrFun h2 x
    simp only [rTr, MultilinearMap.add_apply, Pi.add_apply] at h1x h2x ⊢
    rw [h1x, h2x]
  | smul c U _ h =>
    funext x
    have hx := congrFun h x
    simp only [rTr, MultilinearMap.smul_apply, Pi.smul_apply] at hx ⊢
    rw [hx]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceSpanFullSphericalHeckeEigenpart
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OntoDecomp

theorem iSup_jointEigenspace_eq_top {E I : Type} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (ip : E → E → ℂ) (hlin : ∀ x y z (c : ℂ), ip x (y + c • z) = ip x y + c * ip x z)
    (hherm : ∀ x y, ip y x = star (ip x y)) (hpos : ∀ x, x ≠ 0 → 0 < (ip x x).re)
    (op : I → Module.End ℂ E) (hc : ∀ i j, Commute (op i) (op j))
    (hadj : ∀ i, ∃ i', ∀ x y, ip (op i x) y = ip x (op i' y)) :
    (⨆ x : I → ℂ, ⨅ i, (op i).eigenspace (x i)) = ⊤ := by
  have hzero : ∀ x, ip x 0 = 0 := fun x => by
    have := hlin x 0 0 1
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination (-1 : ℂ) * this
  have hadd : ∀ x y z, ip (x + y) z = ip x z + ip y z := fun x y z => by
    rw [hherm z (x + y), hherm z x, hherm z y]
    have := hlin z x y 1
    simp only [one_smul, one_mul] at this
    rw [this, star_add]
  have hsmul : ∀ x y (r : ℂ), ip (r • x) y = conj r * ip x y := fun x y r => by
    rw [hherm y (r • x), hherm y x]
    have := hlin y 0 x r
    simp only [zero_add, hzero, zero_add] at this
    rw [this, star_mul, mul_comm]
    rfl
  let core : InnerProductSpace.Core ℂ E :=
    { inner := ip
      conj_inner_symm := fun x y => by rw [hherm y x]; rfl
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · subst h
          have := hzero 0
          simp [this]
        · exact (hpos x h).le
      add_left := hadd
      smul_left := hsmul
      definite := fun x hx => by
        by_contra h
        have := hpos x h
        rw [hx] at this
        simp at this }
  letI : NormedAddCommGroup E := InnerProductSpace.Core.toNormedAddCommGroup (cd := core)
  letI : InnerProductSpace ℂ E := InnerProductSpace.ofCore core.toCore
  have hin : ∀ x y : E, inner ℂ x y = ip x y := fun _ _ => rfl
  have h := GlobalTheory.normalFamily_orthogonal_decomposition op (fun i j => hc i j) (fun i => by
    obtain ⟨i', hi'⟩ := hadj i
    refine ⟨i', (LinearMap.eq_adjoint_iff _ _).2 fun x y => ?_⟩
    rw [hin, hin, hherm, ← hi' y x, hherm (op i y)])
  rw [← h.2.1]
  exact iSup_congr fun x => (h.1 x).symm

end GlobalTheory.OntoDecomp

namespace GlobalTheory.OntoDecomp

theorem multT_span_partFull : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → LevFacts D → ForStage D fun c _ s =>
    Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
        partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e} = ⊤ := by
  classical
  intro hP D hfd hlev c hc j hj s hs
  obtain ⟨-, -, hsplit, -, hunif⟩ := _root_.GlobalTheory.ChainOntoSph.level_spherical_off_S D c hc j hj s hs
  have hmul := (hlev c hc j hj s hs).2.2.2.2.1
  have hops := GlobalTheory.SphericalOps.spherical_ops s.V c.θ s.M (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S
    hunif hc.inf hmul hsplit
  have hJ : levS s.V s.β s.L = ((Lev.levG s.V s.β s.L : Subgroup (GA D s.V)) : Set (GA D s.V)) := rfl
  rw [← hJ] at hops
  obtain ⟨hLU, -, hH⟩ := hops
  by_cases hsm : ∀ τ, s.M.sm τ ≠ ⊥
  swap
  · push_neg at hsm
    obtain ⟨τ, hτ⟩ := hsm
    refine Submodule.eq_top_iff'.2 fun u => ?_
    have h0 : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = 0 := by
      refine MultilinearMap.ext fun v => ?_
      rw [MultilinearMap.zero_apply]
      have hv : ((v τ : s.M.sm τ) : s.M.H τ) = 0 := (Submodule.eq_bot_iff _).1 hτ _ (v τ).2
      exact MultilinearMap.map_coord_zero (PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))) τ
        (Subtype.ext hv)
    have h1 := LinearEquiv.apply_symm_apply PiTensorProduct.lift (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))
    rw [h0, map_zero] at h1
    have : u = 0 := Subtype.ext h1.symm
    rw [this]
    exact zero_mem _
  have hschur := GlobalTheory.MultFinite.schurMult (θ := c.θ) (M := s.M) (J := levS s.V s.β s.L)
    (χ := Lev.levChi s.V s.β s.L) hP s.ν s.fd
  haveI := hs.haar
  have hright : s.ν.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds s.V s.ν hs.haar
  obtain ⟨hlin, hpos⟩ := GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M (levS s.V s.β s.L)
    (Lev.levChi s.V s.β s.L) s.ν s.fd hc.inf hs.haar hs.fund hschur hsm
  obtain ⟨v0, hv0⟩ := GlobalTheory.SchurConst.exists_vec s.M hsm
  have hspec : ∀ T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
      ∀ T' ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
      IsMultIP s.M s.ν s.fd T T' (ipM s.M s.ν s.fd T T') := fun T hT T' hT' =>
    ipM_spec _ _ _ _ _ (hschur hc.inf hs.haar hs.fund T hT T' hT')
  let φ := Submodule.equivMapOfInjective (PiTensorProduct.lift : MMap s.M ≃ₗ[ℂ] _).toLinearMap
    (LinearEquiv.injective _) (Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L))
  haveI : FiniteDimensional ℂ ((Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L)).map
      (PiTensorProduct.lift : MMap s.M ≃ₗ[ℂ] _).toLinearMap) := hfd c hc j hj s hs
  haveI : FiniteDimensional ℂ (Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L)) :=
    LinearEquiv.finiteDimensional φ.symm
  let I := {t : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D s.V) //
    Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S t.1 t.2.1 t.2.2}
  let op : I → Module.End ℂ (Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L)) := fun t =>
    (heckeOn s.M t.1.2.2).restrict fun T hT => (hH _ _ _ t.2).1 T hT
  have hcomm : ∀ i j, Commute (op i) (op j) := fun i j => by
    refine LinearMap.ext fun T => Subtype.ext ?_
    exact (hH _ _ _ i.2).2.1 _ _ _ j.2 T T.2
  have hadj : ∀ i, ∃ i', ∀ x y : Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L),
      ipM s.M s.ν s.fd (op i x : MMap s.M) y = ipM s.M s.ν s.fd x (op i' y : MMap s.M) := fun i => by
    obtain ⟨R', h', hip⟩ := (hH _ _ _ i.2).2.2
    refine ⟨⟨(i.1.1, dualLab i.1.2.1, R'), h'⟩, fun x y => ?_⟩
    have h1 := hspec _ ((hH _ _ _ i.2).1 x x.2) y y.2
    have h2 := (hip s.ν s.fd hs.haar hright hs.fund hschur x x.2 y y.2 _).1 h1
    have h3 := hspec x x.2 _ ((hH _ _ _ h').1 y y.2)
    exact hasPeterssonInner_unique s.M s.ν s.fd _ _ v0 hv0 h2 h3
  have htop := iSup_jointEigenspace_eq_top
    (fun x y : Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) => ipM s.M s.ν s.fd x y)
    (fun x y z a => (hlin x x.2 y y.2 z z.2 a).1) (fun x y => (hlin x x.2 y y.2 y y.2 0).2)
    (fun x hx => hpos x x.2 fun h => hx (Subtype.ext h)) op hcomm hadj
  have hsub : ∀ x : I → ℂ, ∀ T ∈ ⨅ i, (op i).eigenspace (x i), ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      (T : MMap s.M) ∈ partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e := by
    classical
    intro x T hT
    refine ⟨fun P d => if h : ∃ R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R
      then x ⟨(P, d, h.choose), h.choose_spec⟩ else 0, ?_⟩
    rw [mem_partFull]
    refine ⟨T.2, fun P d R hR v => ?_⟩
    have hex : ∃ R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R := ⟨R, hR⟩
    rw [dite_eq_left hex]
    have hlevT := ((GlobalTheory.MultMem.mem_mult_iff ..).1 T.2).lev v
    rw [hLU P d R hex.choose hR hex.choose_spec _ hlevT]
    have h1 := (Submodule.mem_iInf _).1 hT ⟨(P, d, hex.choose), hex.choose_spec⟩
    rw [Module.End.mem_eigenspace_iff] at h1
    exact congrArg (fun U : Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) => (U : MMap s.M) v) h1
  rw [eq_top_iff]
  rintro u -
  obtain ⟨T, rfl⟩ := φ.surjective u
  have hT : T ∈ (⊤ : Submodule ℂ (Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L))) := trivial
  rw [← htop] at hT
  refine Submodule.iSup_induction (fun x : I → ℂ => ⨅ i, (op i).eigenspace (x i))
    (motive := fun T => φ T ∈ Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
        partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e}) hT ?_ ?_ ?_
  · intro x T hT
    obtain ⟨e, he⟩ := hsub x T hT
    refine Submodule.subset_span ⟨e, ?_⟩
    have : ((φ T : s.CC c) : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = PiTensorProduct.lift (T : MMap s.M) := rfl
    rw [this, LinearEquiv.symm_apply_apply]
    exact he
  · rw [φ.map_zero]; exact zero_mem _
  · intro a b ha hb; rw [φ.map_add]; exact add_mem ha hb

end GlobalTheory.OntoDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalIsometryKeepsIsotropicFrameOfSiegel
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

namespace GlobalTheory.Core.Rk.Dich

theorem matHom_conj_io (D : D7) (V : HSp D) (γ : GA D (dblSp V)) (δ : GA D V) (g : GL (Fin (V.rank + V.rank)) D.host.E)
    (γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E) (δ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (hg1 : (matHom (dblSp V) γ).1 = g.1.map (incA D)) (hγi : (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D))
    (hδ₀ : (matHom V δ).1 = δ₀.map (incA D)) :
    (matHom (dblSp V) (γ * io V (δ, 1) * γ⁻¹)).1 = (g.1 * blkMat finSumFinEquiv δ₀ 1 * γi).map (incA D) := by
  have h1 : (matHom (dblSp V) (io V (δ, 1))).1 = blkMat finSumFinEquiv (matHom V δ).1 1 := by
    rw [matHom_io, val_blkGL]
    simp
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, h1, hg1, hγi, hδ₀, Matrix.map_mul, Matrix.map_mul,
    blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem isoFrame_keep : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → ∀ (r : ℕ) (K : Matrix (Fin V.rank) (Fin r) D.host.E), diagSnd γi * K = 0 → (∀ x : Fin V.rank → D.host.E, diagSnd γi *ᵥ x = 0 → ∃ y, x = K *ᵥ y) → IsIsoFrame V (leviMat finSumFinEquiv γi * K) → ∀ δ ∈ GQ V, ∀ δ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, (matHom V δ).1 = δ₀.map (incA D) → γ * io V (δ, 1) * γ⁻¹ ∈ siegel V → ∃ G : Matrix (Fin r) (Fin r) D.host.E, IsUnit G ∧ δ₀ * (leviMat finSumFinEquiv γi * K) = leviMat finSumFinEquiv γi * K * G := by
  intro D V γ hγ γi hγi r K hK hKsurj hC δ hδ δ₀ hδ₀ hsieg
  have inj : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  obtain ⟨g, -, hg1, hg2⟩ := exists_rat (dblSp V) hγ
  obtain ⟨d, -, hd1, -⟩ := exists_rat V hδ
  have hγi' : γi = (g⁻¹).1 := Matrix.map_injective inj (hγi.symm.trans hg2)
  have hδ₀' : δ₀ = d.1 := Matrix.map_injective inj (hδ₀.symm.trans hd1)
  have hgi0 : γi * g.1 = 1 := by rw [hγi']; exact g.inv_mul
  obtain ⟨X, hX⟩ : ∃ X, X = g.1 * blkMat finSumFinEquiv δ₀ 1 * γi := ⟨_, rfl⟩
  have hXmap := matHom_conj_io D V γ δ g γi δ₀ hg1 hγi hδ₀
  rw [← hX] at hXmap
  have hKX : KeepsDiag finSumFinEquiv X := by
    have h : KeepsDiag finSumFinEquiv (matHom (dblSp V) (γ * io V (δ, 1) * γ⁻¹)).1 := mem_siegelOf.1 hsieg
    rw [hXmap] at h
    refine (keepsDiag_iff finSumFinEquiv).2 fun i j => inj ?_
    simpa using (keepsDiag_iff finSumFinEquiv).1 h i j
  obtain ⟨C, hCdef⟩ : ∃ C, C = leviMat finSumFinEquiv γi * K := ⟨_, rfl⟩
  rw [← hCdef] at hC ⊢
  have key : ∀ v : Fin r → D.host.E, ∃ w, δ₀ *ᵥ (C *ᵥ v) = C *ᵥ w := by
    intro v
    have h1 : γi *ᵥ pairVec finSumFinEquiv (K *ᵥ v) (K *ᵥ v) = pairVec finSumFinEquiv (C *ᵥ v) 0 := by
      rw [mulVec_pairVec_diag, mulVec_mulVec (M := diagSnd γi), hK, zero_mulVec, mulVec_mulVec, hCdef]
    have h2 : X *ᵥ pairVec finSumFinEquiv (K *ᵥ v) (K *ᵥ v) =
        g.1 *ᵥ pairVec finSumFinEquiv (δ₀ *ᵥ (C *ᵥ v)) 0 := by
      rw [hX, ← mulVec_mulVec, ← mulVec_mulVec, h1, blkMat_mulVec, mulVec_zero]
    have h3 : pairVec finSumFinEquiv (δ₀ *ᵥ (C *ᵥ v)) 0 =
        γi *ᵥ pairVec finSumFinEquiv (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) := by
      rw [← hKX.mulVec_diag, h2, mulVec_mulVec (M := γi), hgi0, one_mulVec]
    rw [mulVec_pairVec_diag] at h3
    have h4a : δ₀ *ᵥ (C *ᵥ v) = leviMat finSumFinEquiv γi *ᵥ (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) := by
      funext i
      have := congrFun h3 (finSumFinEquiv (.inl i))
      rw [pairVec_inl, pairVec_inl] at this
      exact this
    have h4b : diagSnd γi *ᵥ (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) = 0 := by
      funext i
      have := congrFun h3 (finSumFinEquiv (.inr i))
      rw [pairVec_inr, pairVec_inr] at this
      exact this.symm
    obtain ⟨w, hw⟩ := hKsurj _ h4b
    exact ⟨w, by rw [h4a, hw, mulVec_mulVec, hCdef]⟩
  choose w hw using fun j => key (Pi.single j 1)
  have hCG : δ₀ * C = C * Matrix.of fun i j => w j i := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hw j) i
    rw [mulVec_mulVec, mulVec_single_one] at this
    simpa [Matrix.mul_apply, mulVec, dotProduct, transpose_apply] using this
  refine ⟨Matrix.of fun i j => w j i, ?_, hCG⟩
  rw [← mulVec_injective_iff_isUnit]
  intro a b hab
  have h0 : (Matrix.of fun i j => w j i) *ᵥ (a - b) = 0 := by rw [mulVec_sub, hab, sub_self]
  have h5 : C *ᵥ (a - b) = 0 := by
    have h6 : δ₀ *ᵥ (C *ᵥ (a - b)) = 0 := by rw [mulVec_mulVec, hCG, ← mulVec_mulVec, h0, mulVec_zero]
    have h7 := congrArg (fun x => (d⁻¹).1 *ᵥ x) h6
    simp only [hδ₀', mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, mulVec_zero] at h7
    exact h7
  obtain ⟨-, hli, -⟩ := hC
  have h8 := Fintype.linearIndependent_iff.1 hli (a - b) (by
    funext i
    simpa [Finset.sum_apply, mulVec, dotProduct, mul_comm] using congrFun h5 i)
  exact sub_eq_zero.1 (funext h8)

end GlobalTheory.Core.Rk.Dich
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCharQuotientLFunctionEntireNeZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_char_quotient_LFunction_entire_ne_zero : ∀ (D : D7) (c : Com D), c.Is → ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ D.R.m → ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w}) z) ∧ ∀ n : ℕ, 1 ≤ n → n ≤ D.R.t → Λ n ≠ 0 := by
  first | exact @GlobalTheory.ChainOnto.QuotL.quotL_entire_ne_zero | exact GlobalTheory.ChainOnto.QuotL.quotL_entire_ne_zero | (intros; apply GlobalTheory.ChainOnto.QuotL.quotL_entire_ne_zero <;> assumption)
end

