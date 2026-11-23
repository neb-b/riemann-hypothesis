module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0072
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.SeeSaw GlobalTheory.ChiGrid GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BiTransfer

variable {D : D7}

def sumDec (A B : HSp D) : OrthDec (GlobalTheory.Doubling.hsum A B) A B where
  iA := (fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (0 : Matrix (Fin B.rank) (Fin A.rank) D.host.E)).submatrix
    finSumFinEquiv.symm id
  iB := (fromRows (0 : Matrix (Fin A.rank) (Fin B.rank) D.host.E) (1 : Matrix (Fin B.rank) (Fin B.rank) D.host.E)).submatrix
    finSumFinEquiv.symm id
  isoA := by
    rw [GlobalTheory.Doubling.gram_hsum, conjTranspose_submatrix]
    unfold GlobalTheory.Doubling.blkMat
    simp [submatrix_mul_equiv, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  isoB := by
    rw [GlobalTheory.Doubling.gram_hsum, conjTranspose_submatrix]
    unfold GlobalTheory.Doubling.blkMat
    simp [submatrix_mul_equiv, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  orth := by
    rw [GlobalTheory.Doubling.gram_hsum, conjTranspose_submatrix]
    unfold GlobalTheory.Doubling.blkMat
    simp [submatrix_mul_equiv, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  rank_add := rfl

theorem finPart_conj (z : AE D) : finPart D (cA D z) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem infPart_conj (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem fin_dagger (S T : HSp D) {x : WO S T} (hx : x.map (finPart D) = 0) : (dagger S T x).map (finPart D) = 0 := by
  refine map_mul_eq_zero_right _ _ (map_mul_eq_zero_left _ ?_ _)
  funext i j
  have := congrFun (congrFun hx j) i
  change finPart D (x j i) = 0 at this
  change finPart D (cA D (x j i)) = 0
  rw [finPart_conj, this, map_zero]

theorem inf_dagger (S T : HSp D) {x : WO S T} (hx : x.map (infPart D) = 0) : (dagger S T x).map (infPart D) = 0 := by
  refine map_mul_eq_zero_right _ _ (map_mul_eq_zero_left _ ?_ _)
  funext i j
  have := congrFun (congrFun hx j) i
  change infPart D (x j i) = 0 at this
  change infPart D (cA D (x j i)) = 0
  rw [infPart_conj, this, map_zero]

def daggerHom (S T : HSp D) : WO S T →+ WO T S where
  toFun := dagger S T
  map_zero' := by simp [dagger]
  map_add' x y := by simp only [dagger, adj_add, Matrix.add_mul, Matrix.mul_add]

theorem dagger_zero (S T : HSp D) : dagger S T 0 = 0 := (daggerHom S T).map_zero

theorem continuous_dagger (S T : HSp D) : Continuous (dagger S T) :=
  continuous_const.matrix_mul (continuous_adj.matrix_mul continuous_const)

theorem dagger_rat (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    dagger S T (rat γ) = rat (S.gram⁻¹ * (γᴴ * T.gram)) := by
  rw [rat_mul, rat_mul]; rfl

theorem giA_negSp (S : HSp D) : giA (negSp S) = -giA S := by
  have : (negSp S).gram⁻¹ = -S.gram⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [negSp_gram, Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_nonsing_inv _ (gram_isUnit_det S)]
  rw [giA, this, rat_neg]; rfl

theorem symplOH_dagger (S T : HSp D) (x y : WO T S) :
    symplOH S T (dagger T S x) (dagger T S y) = symplOH (negSp T) S x y := by
  have h1 : hO S T (dagger T S x) (dagger T S y) = hO T S y x := by
    simp only [hO_eq_trace, dagger, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_gA_cancel, gA_giA_cancel]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h2 : hO (negSp T) S x y = -hO T S x y := by
    rw [hO_eq_trace, hO_eq_trace, giA_negSp, Matrix.neg_mul, trace_neg]
  rw [symplOH_eq, h1, ← symplOH_eq, symplOH_skew, symplOH_eq, symplOH_eq, h2, map_neg]

variable {W A A' : HSp D} (d : OrthDec W A (negSp A')) (S : HSp D)

def fstH : WO W S →+ WO A S := (AddMonoidHom.fst _ _).comp (d.resS S).toAddMonoidHom

def sndH : WO W S →+ WO S A' := (daggerHom A' S).comp ((AddMonoidHom.snd _ _).comp (d.resS S).toAddMonoidHom)

def inlH : WO A S →+ WO W S := (d.resS S).symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)

def inrH : WO S A' →+ WO W S :=
  (d.resS S).symm.toAddMonoidHom.comp ((AddMonoidHom.inr _ _).comp (daggerHom S A'))

theorem fstH_apply (x : WO W S) : fstH d S x = (d.resS S x).1 := rfl
theorem sndH_apply (x : WO W S) : sndH d S x = dagger A' S (d.resS S x).2 := rfl
theorem inlH_apply (u : WO A S) : inlH d S u = (d.resS S).symm (u, 0) := rfl
theorem inrH_apply (v : WO S A') : inrH d S v = (d.resS S).symm (0, dagger S A' v) := rfl

theorem fst_inl (u : WO A S) : fstH d S (inlH d S u) = u := by
  rw [fstH_apply, inlH_apply, AddEquiv.apply_symm_apply]
theorem fst_inr (v : WO S A') : fstH d S (inrH d S v) = 0 := by
  rw [fstH_apply, inrH_apply, AddEquiv.apply_symm_apply]
theorem snd_inl (u : WO A S) : sndH d S (inlH d S u) = 0 := by
  rw [sndH_apply, inlH_apply, AddEquiv.apply_symm_apply]; exact dagger_zero A' S
theorem snd_inr (v : WO S A') : sndH d S (inrH d S v) = v := by
  rw [sndH_apply, inrH_apply, AddEquiv.apply_symm_apply]; exact dagger_dagger S A' v

theorem continuous_fstH : Continuous (fstH d S) := continuous_fst.comp (d.continuous_resS S)
theorem continuous_sndH : Continuous (sndH d S) :=
  (continuous_dagger A' S).comp (continuous_snd.comp (d.continuous_resS S))
theorem continuous_inlH : Continuous (inlH d S) :=
  (d.continuous_resS_symm S).comp (continuous_id.prodMk continuous_const)
theorem continuous_inrH : Continuous (inrH d S) :=
  (d.continuous_resS_symm S).comp (continuous_const.prodMk (continuous_dagger S A'))

theorem symplOH_split (x y : WO W S) :
    symplOH W S x y = symplOH A S (fstH d S x) (fstH d S y) + symplOH S A' (sndH d S x) (sndH d S y) := by
  rw [d.symplOH_resS, sndH_apply, sndH_apply, symplOH_dagger]; rfl

theorem map_resS_symm {B : Type} [CommRing B] (φ : AE D →+* B) {u : WO A S} {v : WO (negSp A') S}
    (hu : u.map φ = 0) (hv : v.map φ = 0) : ((d.resS S).symm (u, v)).map φ = 0 := by
  rw [d.resS_symm_apply, Matrix.map_add _ (map_add φ), map_mul_eq_zero_left φ hu, map_mul_eq_zero_left φ hv, add_zero]

theorem map_inlH {B : Type} [CommRing B] (φ : AE D →+* B) {u : WO A S} (hu : u.map φ = 0) : (inlH d S u).map φ = 0 :=
  map_resS_symm d S φ hu (Matrix.map_zero _ φ.map_zero)

theorem fin_inrH {v : WO S A'} (hv : v.map (finPart D) = 0) : (inrH d S v).map (finPart D) = 0 :=
  map_resS_symm d S _ (Matrix.map_zero _ (finPart D).map_zero) (fin_dagger S A' hv)

theorem inf_inrH {v : WO S A'} (hv : v.map (infPart D) = 0) : (inrH d S v).map (infPart D) = 0 :=
  map_resS_symm d S _ (Matrix.map_zero _ (infPart D).map_zero) (inf_dagger S A' hv)

def join (C : WO A S → WO S A' → ℂ) : WO W S → ℂ := fun x => C (d.resS S x).1 (dagger A' S (d.resS S x).2)

theorem join_apply (C : WO A S → WO S A' → ℂ) (x : WO W S) : join d S C x = C (fstH d S x) (sndH d S x) := rfl

theorem join_symm (C : WO A S → WO S A' → ℂ) (u : WO A S) (y : WO (negSp A') S) :
    join d S C ((d.resS S).symm (u, y)) = C u (dagger A' S y) := by
  rw [join, AddEquiv.apply_symm_apply]

theorem join_inl_inr (C : WO A S → WO S A' → ℂ) (u : WO A S) (v : WO S A') :
    join d S C (inlH d S u + inrH d S v) = C u v := by
  rw [join_apply, map_add (f := _), map_add (f := _), fst_inl, fst_inr, snd_inl, snd_inr, add_zero, zero_add]

variable {S} {ψ : AddChar (AF D.host.F) ℂ} {C : WO A S → WO S A' → ℂ}

theorem isThetaFunO_join (h : IsBiTheta ψ A S A' C) : IsThetaFunO ψ W S (join d S C) := {
  quasi γ w := by
    have e₁ : fstH d S (ratW S W γ) = ratW S A (γ * d.iA) := (rat_mul γ d.iA).symm
    have e₂ : sndH d S (ratW S W γ) = ratW A' S (A'.gram⁻¹ * ((γ * d.iB)ᴴ * S.gram)) := by
      rw [ratW_eq A' S, ← dagger_rat A' S, rat_mul]; rfl
    rw [join_apply, join_apply, map_add (f := _), map_add (f := _), symplOH_split d, e₁, e₂, h.quasiL, h.quasiR, neg_add,
      AddChar.map_add_eq_mul, mul_assoc]
  level := by
    obtain ⟨U₁, hU₁, k₁⟩ := h.levL
    obtain ⟨U₂, hU₂, k₂⟩ := h.levR
    refine ⟨U₁.comap (fstH d S) ⊓ U₂.comap (sndH d S),
      (hU₁.preimage (continuous_fstH d S)).inter (hU₂.preimage (continuous_sndH d S)), fun u hu h0 => ?_⟩
    funext w
    have e₁ := congrFun (k₁ _ hu.1 (map_mul_eq_zero_left _ h0 _) (sndH d S w + sndH d S u)) (fstH d S w)
    have e₂ := congrFun (k₂ _ hu.2 (inf_dagger A' S (map_mul_eq_zero_left _ h0 _)) (fstH d S w)) (sndH d S w)
    simp only [heisO] at e₁ e₂ ⊢
    rw [join_apply, join_apply, ← e₂, ← e₁, symplOH_split d, AddChar.map_add_eq_mul, map_add (f := _), map_add (f := _)]
    ring
  cont := h.cont.comp ((continuous_fstH d S).prodMk (continuous_sndH d S))
  smooth k L hL h0 w := by
    simp only [join_apply, map_add (f := _)]
    exact h.smooth k ((fstH d S).comp L) ((sndH d S).comp L) ((continuous_fstH d S).comp hL)
      ((continuous_sndH d S).comp hL) (fun t => map_mul_eq_zero_left _ (h0 t) _)
      (fun t => fin_dagger A' S (map_mul_eq_zero_left _ (h0 t) _)) _ _ }

theorem cont_of_join (h : IsThetaFunO ψ W S (join d S C)) : Continuous fun p : WO A S × WO S A' => C p.1 p.2 := by
    have := h.cont.comp (((continuous_inlH d S).comp continuous_fst).add ((continuous_inrH d S).comp continuous_snd))
    exact this.congr fun p => join_inl_inr d S C p.1 p.2

theorem smooth_of_join (h : IsThetaFunO ψ W S (join d S C)) : IsBiSmooth C := fun n L L' hL hL' h0 h0' u v => by
    have := h.smooth n ((inlH d S).comp L + (inrH d S).comp L')
      (((continuous_inlH d S).comp hL).add ((continuous_inrH d S).comp hL')) (fun t => by
        change (inlH d S (L t) + inrH d S (L' t)).map _ = 0
        rw [Matrix.map_add (finPart D) (fun _ _ => map_add (finPart D) _ _), map_inlH d S _ (h0 t), fin_inrH d S (h0' t), add_zero])
      (inlH d S u + inrH d S v)
    convert this using 2 with t
    rw [← join_inl_inr d S C, map_add (f := inlH d S), map_add (f := inrH d S), add_add_add_comm]; rfl

theorem quasiL_of_join (h : IsThetaFunO ψ W S (join d S C)) (γ) (u : WO A S) (v : WO S A') :
    C (ratW S A γ + u) v = ψ (-(symplOH A S (ratW S A γ) u)) * C u v := by
    have e : inlH d S (ratW S A γ) = ratW S W (γ * d.qA) := by
      rw [inlH_apply, d.resS_symm_apply, Matrix.zero_mul, add_zero, ratW_eq S W, rat_mul]; rfl
    have := h.quasi (γ * d.qA) (inlH d S u + inrH d S v)
    rw [← e, ← add_assoc, ← map_add (f := inlH d S), join_inl_inr, join_inl_inr, symplOH_split d, map_add (f := fstH d S), fst_inl, fst_inl, fst_inr,
      snd_inl, symplOH_zero_left, add_zero, add_zero] at this
    exact this

theorem quasiR_of_join (h : IsThetaFunO ψ W S (join d S C)) (γ) (u : WO A S) (v : WO S A') :
    C u (ratW A' S γ + v) = ψ (-(symplOH S A' (ratW A' S γ) v)) * C u v := by
    have e : inrH d S (ratW A' S γ) = ratW S W (S.gram⁻¹ * (γᴴ * A'.gram) * d.qB) := by
      rw [inrH_apply, d.resS_symm_apply, Matrix.zero_mul, zero_add, ratW_eq S W, rat_mul, ← dagger_rat S A']; rfl
    have := h.quasi (S.gram⁻¹ * (γᴴ * A'.gram) * d.qB) (inlH d S u + inrH d S v)
    rw [← e, add_left_comm, ← map_add (f := inrH d S), join_inl_inr, join_inl_inr, symplOH_split d, map_add (f := sndH d S), fst_inr, snd_inr,
      snd_inl, snd_inr, symplOH_zero_left, zero_add, zero_add] at this
    exact this

theorem levL_of_join (h : IsThetaFunO ψ W S (join d S C)) : ∃ U : AddSubgroup (WO A S), IsOpen (U : Set (WO A S)) ∧
    ∀ a ∈ U, a.map (infPart D) = 0 → ∀ v, heisO ψ A S a (fun u => C u v) = fun u => C u v := by
    obtain ⟨U, hU, k⟩ := h.level
    refine ⟨U.comap (inlH d S), hU.preimage (continuous_inlH d S), fun a ha h0 v => funext fun u => ?_⟩
    have := congrFun (k _ ha (map_inlH d S _ h0)) (inlH d S u + inrH d S v)
    simp only [heisO] at this ⊢
    rw [add_right_comm, ← map_add (f := inlH d S), join_inl_inr, join_inl_inr, symplOH_split d, map_add (f := fstH d S), fst_inl, fst_inl, fst_inr,
      snd_inl d S a, symplOH_zero_right, add_zero, add_zero] at this
    exact this

theorem levR_of_join (h : IsThetaFunO ψ W S (join d S C)) : ∃ U : AddSubgroup (WO S A'), IsOpen (U : Set (WO S A')) ∧
    ∀ a ∈ U, a.map (infPart D) = 0 → ∀ u, heisO ψ S A' a (C u) = C u := by
    obtain ⟨U, hU, k⟩ := h.level
    refine ⟨U.comap (inrH d S), hU.preimage (continuous_inrH d S), fun a ha h0 u => funext fun v => ?_⟩
    have := congrFun (k _ ha (inf_inrH d S h0))
      (inlH d S u + inrH d S v)
    simp only [heisO] at this ⊢
    rw [add_assoc, ← map_add (f := inrH d S), join_inl_inr, join_inl_inr, symplOH_split d, map_add (f := sndH d S), fst_inr d S a, snd_inl,
      snd_inr, snd_inr, symplOH_zero_right, zero_add, zero_add] at this
    exact this

theorem isBiTheta_of_join (h : IsThetaFunO ψ W S (join d S C)) : IsBiTheta ψ A S A' C :=
  ⟨cont_of_join d h, smooth_of_join d h, quasiL_of_join d h, quasiR_of_join d h, levL_of_join d h, levR_of_join d h⟩

theorem isBiTheta_iff_join : IsBiTheta ψ A S A' C ↔ IsThetaFunO ψ W S (join d S C) :=
  ⟨isThetaFunO_join d, isBiTheta_of_join d⟩

end GlobalTheory.BiTransfer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCommensuratedKO
section
noncomputable section

open MeasureTheory ValuativeRel GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.GLDoubling

namespace GlobalTheory.UnramDoublingProof

section Cells

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_cell {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (g : GL (Fin N) k) :
    ∃ e : {e : Fin N → ℤ // Antitone e}, g ∈ cell k (Fin N) ϖ e := by
  have h := iUnion_cell (k := k) (N := N) hϖ
  exact Set.mem_iUnion.1 (h ▸ Set.mem_univ g)

def cellLen {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (g : GL (Fin N) k) : ℕ :=
  (∑ i, |(exists_cell hϖ g).choose.1 i|).toNat

theorem cellLen_eq {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (e : Fin N → ℤ) (he : Antitone e)
    (g : GL (Fin N) k) (hg : g ∈ cell k (Fin N) ϖ e) : cellLen hϖ g = (∑ i, |e i|).toNat := by
  have h := (exists_cell hϖ g).choose_spec
  have h' : (exists_cell hϖ g).choose = ⟨e, he⟩ := by
    by_contra hne
    exact Set.disjoint_left.1 (pairwise_disjoint_cell hϖ hne) h hg
  simp only [cellLen, h']

theorem sphSection_eq_pow {N : ℕ} {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) (s : ℂ)
    (g : GL (Fin N) k) :
    sphSection k (Fin N) s (io k (Fin N) (g, 1)) =
      ((resCard k : ℂ) ^ (-((N : ℂ) / 2 + s))) ^ cellLen hϖ g := by
  obtain ⟨⟨e, he⟩, hg⟩ := exists_cell hϖ g
  rw [cellLen_eq hϖ e he g hg]
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
  rw [sphSection_io_biinv s _ hx hy, sphSection_torusElt hϖ, Fintype.card_fin, ← Complex.cpow_nat_mul]
  have h0 : 0 ≤ ∑ i, |e i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hc : (((∑ i, |e i|).toNat : ℕ) : ℂ) = ((∑ i, |e i| : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
  rw [hc]
  congr 1
  ring

theorem isCommensurated_KO {N : ℕ} : Formalism.UG.IsCommensurated (KO k (Fin N)) := by
  intro x
  have hmo : IsOpen (((KO k (Fin N)).map (MulAut.conj x).toMonoidHom : Subgroup (GL (Fin N) k)) :
      Set (GL (Fin N) k)) := by
    have hset : (((KO k (Fin N)).map (MulAut.conj x).toMonoidHom : Subgroup (GL (Fin N) k)) :
        Set (GL (Fin N) k)) = (fun y => x⁻¹ * y * x) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k)) := by
      ext y
      simp only [Subgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa [mul_assoc] using hz
      · intro h
        exact ⟨_, h, by group⟩
    rw [hset]
    exact SplitFlip.isOpen_KO.preimage (by fun_prop)
  have : CompactSpace (KO k (Fin N)) := isCompact_iff_compactSpace.mp SplitFlip.isCompact_KO
  have hso : IsOpen ((((KO k (Fin N)).map (MulAut.conj x).toMonoidHom).subgroupOf (KO k (Fin N)) :
      Subgroup (KO k (Fin N))) : Set (KO k (Fin N))) := by
    rw [Subgroup.coe_subgroupOf]
    exact hmo.preimage continuous_subtype_val
  have : Finite ((KO k (Fin N)) ⧸ ((KO k (Fin N)).map (MulAut.conj x).toMonoidHom).subgroupOf (KO k (Fin N))) :=
    Subgroup.quotient_finite_of_isOpen _ hso
  exact Subgroup.index_ne_zero_of_finite

end Cells

section Factors

theorem factor_one {q n : ℕ} (hq : 0 < q) (i : Fin n) (a s : ℂ) :
    (q : ℂ) ^ (n - 1 - (i : ℕ)) * (a * (((q : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ)) *
      (q : ℂ) ^ (-((n : ℂ) / 2 + s)) = a * (q : ℂ) ^ (-(s + 1 / 2)) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have hc : ((n - 1 - (i : ℕ) : ℕ) : ℂ) = (n : ℂ) - 1 - (i : ℕ) := by
    have := i.2
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_natCast, hc,
    mul_left_comm, mul_assoc, ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]
  congr 2
  push_cast
  ring

theorem qpow_mul_inv_mul_qpow_eq {q n : ℕ} (hq : 0 < q) (i : Fin n) (a s : ℂ) :
    (q : ℂ) ^ (i : ℕ) * (a * (((q : ℝ) ^ (((i : ℕ) : ℝ) - ((n : ℝ) - 1) / 2) : ℝ) : ℂ))⁻¹ *
      (q : ℂ) ^ (-((n : ℂ) / 2 + s)) = a⁻¹ * (q : ℂ) ^ (-(s + 1 / 2)) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_natCast, ← Complex.cpow_natCast, mul_inv,
    ← Complex.cpow_neg, mul_left_comm, mul_assoc, ← Complex.cpow_add _ _ hq0, ← Complex.cpow_add _ _ hq0]
  congr 2
  push_cast
  ring

theorem prod_one_sub_eq_invNormFactor {q n : ℕ} (hq : 0 < q) (s : ℂ) :
    ∏ i : Fin n, (1 - (q : ℂ) ^ (i : ℕ) * ((q : ℂ) ^ (-((n : ℂ) / 2 + s))) ^ 2) = invNormFactor q n s := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  unfold invNormFactor
  refine Finset.prod_bij' (fun i _ => n - (i : ℕ))
    (fun j hj => ⟨n - j, by have := Finset.mem_Icc.1 hj; omega⟩) (fun i _ => ?_) (fun _ _ => Finset.mem_univ _)
    (fun i _ => ?_) (fun j hj => ?_) (fun i _ => ?_)
  · have := i.2
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · have := i.2
    exact Fin.ext (by simp only; omega)
  · have := Finset.mem_Icc.1 hj
    simp only
    omega
  · rw [← Complex.cpow_nat_mul, ← Complex.cpow_natCast, ← Complex.cpow_add _ _ hq0, Nat.cast_sub i.2.le]
    congr 2
    push_cast
    ring

end Factors

theorem unramifiedDoublingGL : GlobalTheory.Published.UnramifiedDoublingGL := by
  intro k _ _ _ _ _ n _ _ μ _ hμ V _ _ π α hπ ω hω
  obtain ⟨ϖ, hϖ⟩ : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
    obtain ⟨x, hx⟩ := valuation_surjective (K := k) (uniformizer k)
    have h0 : x ≠ 0 := by
      rintro rfl
      exact uniformizer_ne_zero (R := k) (by simpa using hx.symm)
    exact ⟨Units.mk0 x h0, hx⟩
  have hq1 : 1 < resCard k := one_lt_resCard k
  have hq : 0 < resCard k := zero_lt_one.trans hq1
  have hqR : (1 : ℝ) < resCard k := by exact_mod_cast hq1
  have hqR0 : (0 : ℝ) < resCard k := zero_lt_one.trans hqR
  obtain ⟨φ, hφ, hsum⟩ := _root_.GlobalTheory.ZonalBorel.exists_isBorelSph_hAct_eq k n V π α hπ ω hω
  obtain ⟨δ, hδ, hmain⟩ := GlobalTheory.T.hasSum_sphericalFunction_doublingLength k n _ φ hφ
    (fun i => mul_ne_zero (α i).ne_zero (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hqR0 _).ne'))
    ϖ hϖ (cellLen hϖ) (cellLen_eq hϖ)
  refine ⟨-Real.logb (resCard k) δ - n / 2, fun s hs => ?_⟩
  have hX : ‖(resCard k : ℂ) ^ (-((n : ℂ) / 2 + s))‖ < δ := by
    rw [Complex.norm_natCast_cpow_of_pos hq]
    refine (Real.rpow_lt_rpow_of_exponent_lt hqR (?_ : _ < Real.logb (resCard k) δ)).trans_eq
      (Real.rpow_logb hqR0 hqR.ne' hδ)
    have : (-((n : ℂ) / 2 + s)).re = -((n : ℝ) / 2 + s.re) := by simp
    rw [this]
    linarith
  have h1 := hmain _ hX
  simp only [← sphSection_eq_pow hϖ s, factor_one hq, qpow_mul_inv_mul_qpow_eq hq, prod_one_sub_eq_invNormFactor hq] at h1
  have h2 := GlobalTheory.InertZeta.dosetSwap (GL (Fin n) k) (KO k (Fin n)) isCommensurated_KO
    (fun g => sphSection k (Fin n) s (io k (Fin n) (g, 1))) ω φ _
    (fun a b g => sphSection_io_biinv s g a.2 b.2) (fun a b g => zonal_biinv hω g a.2 b.2) hsum h1
  have h3 := GlobalTheory.InertZeta.cosetIntegral_holds (GL (Fin n) k) μ (KO k (Fin n)) SplitFlip.isOpen_KO hμ
    (fun g => sphSection k (Fin n) s (io k (Fin n) (g, 1)) * ω g) _ (fun g y hy => by
      have e1 := sphSection_io_biinv s g (one_mem (KO k (Fin n))) hy
      have e2 := zonal_biinv hω g (one_mem (KO k (Fin n))) hy
      rw [one_mul] at e1 e2
      simp only [e1, e2]) h2
  refine ⟨h3.1, h3.2.trans ?_⟩
  simp only [lFactor, Pi.inv_apply, Units.val_inv_eq_inv_val]

end GlobalTheory.UnramDoublingProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsCompactRealPointsOfDefiniteHermitianSpaceData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw

open scoped ComplexOrder

theorem sig_eq_of_definite {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef ∨ (-G).PosDef) {p q : ℕ}
    (h : Formalism.UG.HasSignature G p q) : (p, q) = (n, 0) ∨ (p, q) = (0, n) := by
  rcases hG with hG | hG
  · exact Or.inl (GlobalTheory.DefLiftMult.sig_of_posDef hG h)
  · right
    obtain ⟨hn, Q, hQ⟩ := Formalism.UG.P.sig_data G p q h
    have hp : p = 0 := by
      by_contra hp
      have i : Fin p := ⟨0, Nat.pos_of_ne_zero hp⟩
      have h1 := (hG.posSemidef.conjTranspose_mul_mul_same Q).diag_nonneg (i := Sum.inl i)
      rw [Matrix.mul_neg, Matrix.neg_mul, hQ] at h1
      simp [Formalism.UG.Jpq] at h1
      exact absurd h1 (by norm_num)
    subst hp
    simp at hn
    rw [hn]

theorem isDefinite_of_defSp {D : D7} {A : HSp D} (x : DefSp A) (hx : x.Is) : A.IsDefinite := by
  have hτ : ∀ τ, (gramAt D A τ).PosDef ∨ (-(gramAt D A τ)).PosDef := by
    intro τ
    have hp := (hx.cart τ).2.2
    rcases hx.pm τ with h | h
    · left
      rwa [h, Matrix.mul_one] at hp
    · right
      rwa [h, Matrix.mul_neg, Matrix.mul_one] at hp
  intro σ
  have hs := hx.sig σ
  have key : (A.sig σ).1 = A.rank ∧ (A.sig σ).2 = 0 ∨ (A.sig σ).1 = 0 ∧ (A.sig σ).2 = A.rank := by
    obtain ⟨τ, rfl | rfl⟩ := GlobalTheory.DefLiftMult.exists_tauE D σ
    · simpa [Prod.ext_iff] using sig_eq_of_definite (hτ τ) hs
    · have e : A.gram.map ((starRingEnd ℂ).comp (tauE D τ)) = (gramAt D A τ)ᴴᵀ := by
        ext i j
        rfl
      rw [e] at hs
      have hd : ((gramAt D A τ)ᴴᵀ).PosDef ∨ (-(gramAt D A τ)ᴴᵀ).PosDef := by
        rcases hτ τ with h | h
        · exact Or.inl h.conjTranspose.transpose
        · right
          have := h.conjTranspose.transpose
          rwa [Matrix.conjTranspose_neg, Matrix.transpose_neg] at this
      simpa [Prod.ext_iff] using sig_eq_of_definite hd hs
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (Prod.ext h1 h2)
  · exact Or.inr (Prod.ext h1 h2)

theorem isCompact_ginfC_of_defSp : ∀ (D : D7) (A : HSp D) (x : DefSp A), x.Is → IsCompact (GinfC A : Set (GA D A)) :=
  fun _ _ x hx => Formalism.IndefR.Eqv.isCompact_GinfC hx.sig (isDefinite_of_defSp x hx)

end GlobalTheory.SeeSaw

end
end

