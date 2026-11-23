module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0364
public import Lean
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0465
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0006
public import Formalism.LocalToGlobal.HilbertRowConditions.KaTiedIffKapDef
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowCompatibilitiesTransportReplacedStages
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.Mem.R3.Rw.Up


set_option maxHeartbeats 4000000 in
theorem rxs_up : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ) (t' : RowsT K w (SRe.upL Z S' N h) Wt (Tr.baseLevelRowSideTransport (Up.refUp Z S' N h) p0)), RowsSame t t' → Nonempty (RXs t) → Nonempty (RXs t') := by
  intro K B f T w Z Wt p0 t S' N h t' hs ⟨x⟩
  have hstd : t'.r.z.Std := (GlobalTheory.T.standardReading_transport_and_extension_trans).1 B f T w Z (SRe.upL Z S' N h) t.hX Wt t.r.z t'.r.z hs.Xg hs.tr hs.R hs.core x.std
  obtain ⟨hX', r', exAt', inGeo', grpAt', grp', mu'', exact', untw', emt0', emt', etaF', rowInt', idx'⟩ := t'
  obtain ⟨z', holds', Y', Z'', tup_ix'⟩ := r'
  obtain @⟨Xg', tr', core', alg', alg_eq', R', cG', geo', pins', lev', idG', good', mu', le', Ks'⟩ := z'
  have hXg := hs.Xg
  have htr := hs.tr
  have hcore := hs.core
  have hR := hs.R
  have hcG := hs.cG
  have htup := hs.tup
  have hjA := hs.jA
  have hjA0 := hs.jA0
  have heMt := hs.eMt
  clear hs
  dsimp only at hXg htr hcore hR hcG htup hjA hjA0 heMt hstd
  subst hXg htr
  have hc := eq_of_heq hcore
  subst hc
  have ha : @Eq _ alg' t.r.z.alg :=
    Algebra.algebra_ext _ _ fun r => B.embLL.injective ((alg_eq' r).trans (t.r.z.alg_eq r).symm)
  subst ha
  have hr := eq_of_heq hR
  cases hr
  have hg := eq_of_heq hcG
  cases hg
  cases Y' with
  | mk tup' tupT' tupT_tup' tupTie' tup0' muAt' hm' hTop' hinj' Ish' Iz' IL' Kc' PY' PW' eFT' ιW' tied' prtE' prtE0' prtWE' xi'
      isomFin' frameMatch' hF' stdPsi' jA' jA0' eMt' => ?_
  dsimp only at htup hjA hjA0 heMt
  have e1 := eq_of_heq htup
  cases e1
  have e2 := eq_of_heq hjA
  cases e2
  have e3 := eq_of_heq hjA0
  cases e3
  have e4 := eq_of_heq heMt
  cases e4
  exact ⟨{
    all := {
      jA := (by with_unfolding_all exact (x.all.jA :))
      jA0 := (by with_unfolding_all exact (x.all.jA0 :))
      eMt := (by with_unfolding_all exact (x.all.eMt :))
      formsA := (by with_unfolding_all exact (x.all.formsA :))
      latA := (by with_unfolding_all exact (x.all.latA :))
      formsAtBottomLevel := (by with_unfolding_all exact (x.all.formsAtBottomLevel :))
      latA0 := (by with_unfolding_all exact (x.all.latA0 :))
      formsL := (by with_unfolding_all exact (x.all.formsL :))
      latL := (by with_unfolding_all exact (x.all.latL :))
      cen := (by with_unfolding_all exact (x.all.cen :)) }
    jA_use := (by with_unfolding_all exact (x.jA_use :))
    movedReadingSameMaps_baseReading_agrees := (by with_unfolding_all exact (x.movedReadingSameMaps_baseReading_agrees :))
    eMt_use := (by with_unfolding_all exact (x.eMt_use :))
    e := (by with_unfolding_all exact (x.e :))
    eMt0 := (by with_unfolding_all exact (x.eMt0 :))
    eMtTw := (by with_unfolding_all exact (x.eMtTw :))
    crd := (by with_unfolding_all exact (x.crd :))
    io := (by with_unfolding_all exact (x.io :))
    sha := (by with_unfolding_all exact (x.sha :))
    laws := (by with_unfolding_all exact ((Mv.lawsCore_tr (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩)
      ⟨(SRe.upL Z S' N h).W, (SRe.upL Z S' N h).V, (SRe.upL Z S' N h).S, (SRe.upL Z S' N h).N, (SRe.upL Z S' N h).G⟩ (K := t.r.z.core.toCore) x.laws) :))
    canon := (by with_unfolding_all exact (x.canon :))
    rank := (by with_unfolding_all exact (x.rank :))
    pb := (by with_unfolding_all exact (x.pb :))
    std := (by with_unfolding_all exact (hstd :)) }⟩

end GlobalTheory.Mem.R3.Rw.Up
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPolyChernRoots
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BlockSymm

section Split

variable (R : Type) [CommRing R] {ι : Type} (m : ι → ℕ)

def chernRootsOver : MvPolynomial (ι × ℕ) R →ₐ[R] MvPolynomial (Root m) R :=
  aeval fun x => rename (Sigma.mk x.1) (esymm (Fin (m x.1)) R x.2)

variable {m} [DecidableEq ι] (τ₀ : ι)

def rootSplit : Root m ≃ Fin (m τ₀) ⊕ Root (fun τ : {τ // τ ≠ τ₀} => m τ.1) :=
  GlobalTheory.InnerAutomorphism.sigmaSplit (fun τ => Fin (m τ)) τ₀

def splitEquiv : MvPolynomial (Root m) R ≃ₐ[R]
    MvPolynomial (Fin (m τ₀)) (MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) :=
  (renameEquiv R (rootSplit τ₀)).trans (sumAlgEquiv R _ _)

theorem splitEquiv_X_self (i : Fin (m τ₀)) :
    splitEquiv R τ₀ (X (⟨τ₀, i⟩ : Root m)) = X i := by
  have e : rootSplit τ₀ (⟨τ₀, i⟩ : Root m) = Sum.inl i := GlobalTheory.InnerAutomorphism.sigmaSplit_self (fun τ => Fin (m τ)) τ₀ i
  simp [splitEquiv, e]

theorem splitEquiv_X_ne {τ : ι} (h : τ ≠ τ₀) (i : Fin (m τ)) :
    splitEquiv R τ₀ (X (⟨τ, i⟩ : Root m)) = C (X ⟨⟨τ, h⟩, i⟩) := by
  have e : rootSplit τ₀ (⟨τ, i⟩ : Root m) = Sum.inr ⟨⟨τ, h⟩, i⟩ := GlobalTheory.InnerAutomorphism.sigmaSplit_of_ne (fun τ => Fin (m τ)) h i
  simp [splitEquiv, e]

theorem splitEquiv_symm_X (i : Fin (m τ₀)) :
    (splitEquiv R τ₀).symm (X i) = X (⟨τ₀, i⟩ : Root m) := by
  rw [AlgEquiv.symm_apply_eq, splitEquiv_X_self]

theorem splitEquiv_symm_C (c : MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) :
    (splitEquiv R τ₀).symm (C c) = rename (fun y => (⟨y.1.1, y.2⟩ : Root m)) c := by
  rw [AlgEquiv.symm_apply_eq]
  induction c using MvPolynomial.induction_on with
  | C r =>
    simp only [rename_C]
    change _ = splitEquiv R τ₀ (algebraMap R _ r)
    rw [AlgEquiv.commutes]; rfl
  | add p q hp hq => simp [map_add (f := _), ← hp, ← hq]
  | mul_X p y hp =>
    simp only [map_mul, rename_X]
    rw [← hp, splitEquiv_X_ne R τ₀ y.1.2]

theorem splitEquiv_symm_esymm (j : ℕ) :
    (splitEquiv R τ₀).symm (esymm (Fin (m τ₀)) (MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R) j) =
      chernRootsOver R m (X (τ₀, j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [chernRootsOver, esymm, map_sum, map_prod, splitEquiv_symm_X]

theorem splitEquiv_rename_update (σ : Equiv.Perm (Fin (m τ₀))) (S : MvPolynomial (Root m) R) :
    splitEquiv R τ₀ (rename (Equiv.sigmaCongrRight
      (Function.update (1 : ∀ τ, Equiv.Perm (Fin (m τ))) τ₀ σ)) S) = rename σ (splitEquiv R τ₀ S) := by
  have : ((splitEquiv R τ₀).toAlgHom.comp (rename (Equiv.sigmaCongrRight
      (Function.update (1 : ∀ τ, Equiv.Perm (Fin (m τ))) τ₀ σ)))) =
      ((rename σ).restrictScalars R).comp (splitEquiv R τ₀).toAlgHom := by
    ext ⟨τ, i⟩ : 1
    by_cases h : τ = τ₀
    · subst h; simp [splitEquiv_X_self]
    · simp [splitEquiv_X_ne R τ₀ h, Function.update_of_ne h]
  exact congrArg (· S) (congrArg DFunLike.coe this)

theorem splitEquiv_rename_rest (w' : ∀ τ : {τ // τ ≠ τ₀}, Equiv.Perm (Fin (m τ.1))) (S : MvPolynomial (Root m) R) :
    splitEquiv R τ₀ (rename (Equiv.sigmaCongrRight
      (fun τ => if h : τ = τ₀ then (1 : Equiv.Perm (Fin (m τ))) else w' ⟨τ, h⟩)) S) =
      MvPolynomial.map (rename (Equiv.sigmaCongrRight w')).toRingHom (splitEquiv R τ₀ S) := by
  have : ((splitEquiv R τ₀).toAlgHom.comp (rename (Equiv.sigmaCongrRight
      (fun τ => if h : τ = τ₀ then (1 : Equiv.Perm (Fin (m τ))) else w' ⟨τ, h⟩)))) =
      (mapAlgHom (rename (Equiv.sigmaCongrRight w'))).comp (splitEquiv R τ₀).toAlgHom := by
    ext ⟨τ, i⟩ : 1
    by_cases h : τ = τ₀
    · subst h; simp [splitEquiv_X_self]
    · simp [splitEquiv_X_ne R τ₀ h, h]
  exact congrArg (· S) (congrArg DFunLike.coe this)

theorem rename_chernRootsOver (T : MvPolynomial ({τ // τ ≠ τ₀} × ℕ) R) :
    rename (fun y : Root (fun τ : {τ // τ ≠ τ₀} => m τ.1) => (⟨y.1.1, y.2⟩ : Root m))
      (chernRootsOver R (fun τ : {τ // τ ≠ τ₀} => m τ.1) T) =
      chernRootsOver R m (rename (Prod.map Subtype.val id) T) := by
  induction T using MvPolynomial.induction_on with
  | C r => simp [chernRootsOver]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, hp]
    congr 1
    simp [chernRootsOver, rename_rename]
    rfl

end Split

theorem mem_range_chernRootsOver (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ (R : Type) [CommRing R] (m : ι → ℕ) (S : MvPolynomial (Root m) R),
    (∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S) →
    S ∈ (chernRootsOver R m).range := by
  induction n with
  | zero =>
    intro ι _ _ hc R _ m S _
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hc
    rw [eq_C_of_isEmpty S]
    exact Subalgebra.algebraMap_mem _ _
  | succ n ih =>
    intro ι _ _ hc R _ m S hS
    obtain ⟨τ₀⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    have hc' : Fintype.card {τ // τ ≠ τ₀} = n := by
      simp [Fintype.card_subtype_compl, hc]
    let R' := MvPolynomial (Root (fun τ : {τ // τ ≠ τ₀} => m τ.1)) R
    let f : Fin (m τ₀) → MvPolynomial (Fin (m τ₀)) R' := fun i => esymm (Fin (m τ₀)) R' (↑i + 1)
    have hsym : splitEquiv R τ₀ S ∈ symmetricSubalgebra (Fin (m τ₀)) R' := by
      rw [mem_symmetricSubalgebra]
      intro σ
      rw [← splitEquiv_rename_update, hS]
    obtain ⟨T, hT⟩ := esymmAlgHom_fin_surjective R' (m := m τ₀) (n := m τ₀) le_rfl ⟨_, hsym⟩
    have hT' : aeval f T = splitEquiv R τ₀ S := by
      rw [← esymmAlgHom_apply, hT]
    have hcoef : ∀ d, AddMonoidAlgebra.coeff T d ∈ (chernRootsOver R (fun τ : {τ // τ ≠ τ₀} => m τ.1)).range := by
      intro d
      apply ih _ hc' R
      intro w'
      have hinv : MvPolynomial.map (rename (Equiv.sigmaCongrRight w')).toRingHom T = T := by
        apply esymmAlgHom_fin_injective R' (m := m τ₀) (n := m τ₀) le_rfl
        apply Subtype.ext
        rw [esymmAlgHom_apply, esymmAlgHom_apply]
        change aeval f _ = aeval f T
        rw [hT', ← hS (fun τ => if h : τ = τ₀ then 1 else w' ⟨τ, h⟩), splitEquiv_rename_rest, ← hT',
          aeval_def, aeval_def, algebraMap_eq, eval₂_map, eval₂_comp_left, map_comp_C]
        congr 1
        funext i
        exact (map_esymm _ _ _ _).symm
      have := congrArg (AddMonoidAlgebra.coeff · d) hinv
      rwa [coeff_map] at this
    let k : MvPolynomial (Fin (m τ₀)) R' →+* MvPolynomial (Root m) R :=
      (splitEquiv R τ₀).symm.toRingEquiv.toRingHom
    have hSE : S = k (eval₂ C f T) := by
      change S = (splitEquiv R τ₀).symm _
      rw [← algebraMap_eq, ← aeval_def, hT', AlgEquiv.symm_apply_apply]
    have key : k (eval₂ C f T) = eval₂ (k.comp C) (k ∘ f) T := eval₂_comp_left k C f T
    rw [hSE, key, eval₂_eq]
    refine Subalgebra.sum_mem _ fun d _ => Subalgebra.mul_mem _ ?_ (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ ?_ _)
    · obtain ⟨Tc, hTc⟩ := (AlgHom.mem_range _).mp (hcoef d)
      rw [RingHom.comp_apply, ← hTc]
      change (splitEquiv R τ₀).symm (C _) ∈ _
      rw [splitEquiv_symm_C, rename_chernRootsOver]
      exact AlgHom.mem_range_self _ _
    · change (splitEquiv R τ₀).symm (esymm _ _ _) ∈ _
      rw [splitEquiv_symm_esymm]
      exact AlgHom.mem_range_self _ _

theorem exists_chernRoots_eq_of_blockSymmetric : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (S : MvPolynomial (Root m) ℝ),
    (∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S) →
    ∃ R : MvPolynomial (ι × ℕ) ℝ, chernRoots m R = S := by
  intro ι _ m S hS
  classical
  obtain ⟨R, hR⟩ := (AlgHom.mem_range _).mp (mem_range_chernRootsOver _ ι rfl ℝ m S hS)
  exact ⟨R, hR⟩

end GlobalTheory.BlockSymm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKeyRuleTriangularFrameChangeFourthPower
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem det_blocks_lower {S J : Type} [CommRing S] [Fintype J] [DecidableEq J] (m : J → ℕ)
    (g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) S) (hz : ∀ τ i j, i < j → g τ i j = 0) {n : ℕ}
    (e : Fin n ≃ Σ τ : J, Fin (m τ)) :
    ((Matrix.blockDiagonal' g).submatrix e e).det = ∏ x : (Σ τ : J, Fin (m τ)), g x.1 x.2 x.2 := by
  rw [Matrix.det_submatrix_equiv_self, ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal', Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun τ _ => Matrix.det_of_lowerTriangular _ fun i j hij => hz τ i j hij

theorem isCombAt_blocks {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}
    {J : Type} [Fintype J] [DecidableEq J] {m : J → ℕ}
    (u : ∀ τ, Fin (m τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hu : ∀ τ i, IsTanAt x (u τ i))
    (g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) S) {n : ℕ} (e : Fin n ≃ Σ τ : J, Fin (m τ)) (i : Fin n)
    (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (h : IsCombAt x (u (e i).1) (g (e i).1 (e i).2) w) :
    IsCombAt x (fun j => u (e j).1 (e j).2) ((Matrix.blockDiagonal' g).submatrix e e i) w := by
  obtain ⟨N, _, _, v, ρ, -, htan, hcomb, -, -⟩ := GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S x
  choose b hb using fun τ i => (htan (u τ i)).1 (hu τ i)
  obtain rfl : u = fun τ i => v (b τ i) := by funext τ i; exact (hb τ i).symm
  rw [hcomb] at h ⊢
  rw [h]
  congr 1
  simp only [Matrix.submatrix_apply]
  rw [e.sum_comp (fun p : Σ τ : J, Fin (m τ) => Matrix.blockDiagonal' g (e i) p • b p.1 p.2), Fintype.sum_sigma]
  generalize e i = p
  obtain ⟨a, k⟩ := p
  rw [Finset.sum_eq_single a]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro σ _ hσ
    simp only [Matrix.blockDiagonal'_apply_ne _ _ _ hσ.symm, zero_smul, Finset.sum_const_zero]
  · simp

theorem rule_frBor : ∀ κ : GlobalTheory.KeyCl.Rule, GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : Type) [Field K] [CharZero K] [Algebra c.F K] (t : Ix Dw → Kˣ) (y y' : FrPt Xo c K) (Φ : FibKey Xo K y.x) (Φ' : FibKey Xo K y'.x), FrBor t y y' → Tied e y.s y.u Φ → Tied e y'.s y'.u Φ' → κ K Φ'.key = kch t ^ 4 * κ K Φ.key := by
  classical
  intro κ hH hF E _ _ _ H Dw l Xo c g e K _ _ _ t y y' Φ Φ' hb hT hT'
  obtain ⟨M, hz, hd, hx, hc, hs⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 hb
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := y
  obtain ⟨x', xo', u', tan', eig', bas', s', gen'⟩ := y'
  dsimp only at hx hc hs Φ Φ' hT hT'
  subst hx
  obtain ⟨h1, hg, hv⟩ := hT
  obtain ⟨h1', hg', hv'⟩ := hT'
  subst hg'
  have hid : x' = spMap (RingHom.id K) ≫ x' := by rw [GlobalTheory.Frames.SecCalc.spMap_id', Category.id_comp]
  have did : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    have hd : dualMap (RingHom.id K) = RingHom.id _ := RingHom.ext fun x => by ext <;> simp [dualMap]
    rw [hd]
    exact Spec.map_id _
  obtain ⟨th, hth⟩ := (GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ'.T.t Φ'.m).2.1 s
  have hne := ((GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ'.T.t Φ'.m).2.2 th s hth).2.1
    (((GlobalTheory.SecTieEx.secTie_exists_unique E H Dw l Xo K x' Φ.T.t Φ.m).2.2 Φ.th s h1).2.2 Φ.th_ne)
  have hss : GlobalTheory.Frames.SecBC (RingHom.id K) 1 x' x' s s :=
    ((GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo K K K _ _ x' x' x' hid hid).2.1 1 s s).2 fun i => by
      rw [GlobalTheory.Frames.SecCalc.scal_one', _root_.one_mul]
  have fibKey_keyPB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S S' : Type) [CommRing S] [CommRing S'] [Nontrivial S'] (φ : S →+* S') (x : Sp S ⟶ Xo.X) (x' : Sp S' ⟶ Xo.X) (Φ : FibKey Xo S x) (Φ' : FibKey Xo S' x') (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')), x' = spMap φ ≫ x → SecTie Φ.m Φ.th s → SecTie Φ'.m Φ'.th s' → GlobalTheory.Frames.SecBC φ 1 x x' s s' → ∃ (hg : Φ'.T.g = Φ.T.g) (v' : Fin Φ'.T.g → (epsR S' ⟶ Φ'.T.t.G)) (hv' : IsLieBasis v'), KeyPB ({ Φ' with v := v', basis := hv' } : FibKey Xo S' x').key Φ.key φ ∧ ∀ i, (v' i).left ≫ Φ'.m.φ = spMap (dualMap φ) ≫ (Φ.v (i.cast hg)).left ≫ Φ.m.φ := by
    intro E _ _ _ H Dw l Xo S S' _ _ hS φ x x' Φ Φ' s s' hx ht ht' hs
    obtain ⟨n, hn⟩ := (GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ _ _ _ x x' (spMap φ) Φ.m Φ'.m hx).1
    obtain ⟨hg, -, w, hw⟩ := (pat_pullback E H S S' φ Φ.T).2 Φ'.T n hS
    obtain ⟨θ, hθ⟩ := GlobalTheory.ArcQBC.exists_pullSec n.φ Φ.th
    have hm : IsoMaps w Φ'.th θ := ((TieCalc.secTie_calc E H Dw l Xo S x Φ.T.t Φ.m Φ.th s ht).2 S' φ x' Φ'.T.t Φ'.m n s' w θ
      Φ'.th hx hn.symm hs hw hθ).1 ht'
    obtain ⟨u, hu, huv⟩ := exists_isLieBasis_baseChange S S' φ Φ.T.t.G Φ'.T.t.G n.φ n.cart Φ.T.t.semi.smooth Φ.T.g Φ.v Φ.basis
    have hb : ∀ (k : ℕ) (hk : k = Φ.T.g), IsLieBasis fun i : Fin k => u (i.cast hk) := by
      rintro _ rfl
      exact hu
    have hv : ∀ i : Fin Φ'.T.g, (u (i.cast hg)).left ≫ n.φ = spMap (dualMap φ) ≫ (Φ.v (i.cast hg)).left :=
      fun i => huv _
    have he : eSec Φ'.T.t.G ≫ n.φ = spMap φ ≫ eSec Φ.T.t.G := n.cm.e_comm.trans (congrArg (· ≫ eSec Φ.T.t.G) n.base)
    have hr : ∀ (e : Sp S' ⟶ Sp S) (_ : n.cm.e = e) (he : eSec Φ'.T.t.G ≫ n.φ = e ≫ eSec Φ.T.t.G),
        rigPullOf n.φ e he Φ.T.t.PP.L Φ.T.t.PP.rig = n.cm.rigPull Φ.T.t.PP.L Φ.T.t.PP.rig := by
      rintro _ rfl _
      rfl
    refine ⟨hg, fun i => u (i.cast hg), hb _ hg, ⟨n.φ, he, w, hg, dualMap φ, n.cart, hw.1, ?_, fun j i h => ?_,
      fun a => ?_, ?_, hv⟩, fun i => ?_⟩
    · exact (hr _ n.base he).symm ▸ hw.2
    · refine Eq.trans ?_ (hm j i)
      have le : (Φ.T.t.PP.L.pull n.φ).U j ≤ n.φ ⁻¹ᵁ Φ.T.t.PP.L.U (j PUnit.unit) := fun y hy => mem_pull.1 hy
      rw [hθ j le, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    · ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
    · ext <;> simp [dualMap]
    · rw [← hn, ← Category.assoc, hv, Category.assoc]
  obtain ⟨hg2, v, hvb, hpb, hvv⟩ := fibKey_keyPB E H Dw l Xo K K (RingHom.id K) x' x' Φ
    { Φ' with th := th, th_ne := hne } s s hid h1 hth hss
  have hvu : ∀ i : Fin Φ'.T.g, (v i).left ≫ Φ'.m.φ = u (e i).1 (e i).2 := fun i => by
    refine (hvv i).trans ?_
    rw [did, Category.id_comp]
    exact hv _
  have e1 := hF K K (RingHom.id K) _ _ hpb
  have hsc := ((TieCalc.secTie_calc E H Dw l Xo K x' Φ'.T.t Φ'.m th s hth).1 _ x' s' Φ'.th rfl hs).1 h1'
  have hcomb : ∀ i, IsLieComb ((Matrix.blockDiagonal' M).submatrix e e i) v (Φ'.v i) := fun i => by
    have h2 := isCombAt_blocks u tan M e i _ (hc (e i).1 (e i).2)
    rw [← funext hvu] at h2
    obtain ⟨w, hw, hw'⟩ := (GlobalTheory.MetricChange.lift_comb Φ'.m.cart).2 _ _ v _ h2
    have : w = Φ'.v i := Over.OverMorphism.ext
      (Φ'.m.cart.1.hom_ext (hw.trans (hv' i).symm) ((Over.w _).trans (Over.w _).symm))
    exact this ▸ hw'
  have e2 := hH K Φ'.T.pol Φ'.g_pos Φ'.T.t.PP.rig Φ'.T.t.PP.rigGen th hne v hvb Φ'.th Φ'.th_ne Φ'.v Φ'.basis
    (t none : K) _ hsc hcomb
  have e3 := (det_blocks_lower (fun τ => Dw.mult τ) M hz e).trans (Finset.prod_congr rfl fun x _ => hd x.1 x.2)
  have e4 : ((t none : K)) ^ 8 * (κ K Φ'.key : K) =
      (∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), (t (some x) : K)) ^ 4 * (κ K Φ.key : K) := by
    refine e2.trans ?_
    exact congrArg₂ (fun a b : K => a ^ 4 * b) e3 e1
  apply Units.ext
  have h0 : (t none : K) ≠ 0 := Units.ne_zero _
  rw [kch_eq]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.coe_prod]
  field_simp
  linear_combination e4

end GlobalTheory.KeyFourth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToIntBijective
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.Rows Formalism.L2.Geo GlobalTheory.GeoGraft NumberField

namespace GlobalTheory.GeoModel

variable (D : D7)

def fracO : IntermediateField ℚ D.what₂.LL := IntermediateField.adjoin ℚ (Set.range D.what₂.OtoLL)

theorem otoLL_mem (y : D.what₂.O) : D.what₂.OtoLL y ∈ fracO D :=
  IntermediateField.subset_adjoin ℚ _ ⟨y, rfl⟩

variable {D} {T : HostTied D} {C : CharFrame D}

def toInt (h : OTied D T C) : D.what₂.O →+* 𝓞 (fracO D) where
  toFun y := ⟨⟨D.what₂.OtoLL y, otoLL_mem D y⟩, by
    have hq : IsIntegral ℤ (T.jLL (D.what₂.OtoLL y)) := ((h.range _).1 ⟨y, rfl⟩).2
    let f : (fracO D) →ₐ[ℤ] Qb := (T.jLL.comp (fracO D).val.toRingHom).toIntAlgHom
    have hf : Function.Injective f := (T.jLL.comp (fracO D).val.toRingHom).injective
    exact (isIntegral_algHom_iff f hf).1 hq⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; exact map_mul D.what₂.OtoLL a b
  map_zero' := by ext; simp
  map_add' a b := by ext; exact map_add D.what₂.OtoLL a b

theorem toInt_val (h : OTied D T C) (y : D.what₂.O) : ((toInt h y : fracO D) : D.what₂.LL) = D.what₂.OtoLL y := rfl

theorem toInt_bijective (h : OTied D T C) : Function.Bijective (toInt h) := by
  refine ⟨fun a b hab => h.inj ?_, fun z => ?_⟩
  · have := congrArg (fun w : 𝓞 (fracO D) => ((w : fracO D) : D.what₂.LL)) hab
    simpa [toInt_val] using this
  · set x : D.what₂.LL := ((z : fracO D) : D.what₂.LL) with hx
    have hint : IsIntegral ℤ (T.jLL x) := by
      let f : (fracO D) →ₐ[ℤ] Qb := (T.jLL.comp (fracO D).val.toRingHom).toIntAlgHom
      have hf : Function.Injective f := (T.jLL.comp (fracO D).val.toRingHom).injective
      exact (isIntegral_algHom_iff f hf).2 z.2
    have hmem : T.jLL x ∈ KsQ D T C h.pieces := by
      have hx' : x ∈ fracO D := (z : fracO D).2
      have h1 : T.jLL x ∈ (fracO D).map T.jLL.toRatAlgHom := ⟨x, hx', rfl⟩
      rw [fracO, IntermediateField.adjoin_map] at h1
      refine (IntermediateField.adjoin_le_iff.2 ?_) h1
      rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ((h.range _).1 ⟨y, rfl⟩).1
    obtain ⟨y, hy⟩ := (h.range _).2 ⟨hmem, hint⟩
    refine ⟨y, ?_⟩
    ext
    exact T.jLL.injective hy

def eO (h : OTied D T C) : 𝓞 (fracO D) ≃+* D.what₂.O := (RingEquiv.ofBijective _ (toInt_bijective h)).symm

end GlobalTheory.GeoModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalTripleFibresBaseChangeKeyData
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.FrameUnif GlobalTheory.Reg
open scoped Matrix TensorProduct

namespace GlobalTheory.KeyFourth

theorem tied_keyPB : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (S S' : Type) [CommRing S] [Algebra c.F S] [CommRing S'] [Nontrivial S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (y : FrPt Xo c S) (z : FrPt Xo c S') (Φ : FibKey Xo S y.x) (Φ' : FibKey Xo S' z.x), FrMap φ y z → Tied e y.s y.u Φ → Tied e z.s z.u Φ' → KeyPB Φ'.key Φ.key φ.toRingHom := by
  open GlobalTheory GlobalTheory.CM GlobalTheory.Frames MonoidalCategory CartesianMonoidalCategory MonObj IsDedekindDomain MeasureTheory in
  intro E _ _ _ H Dw l Xo c g e S S' _ _ _ _ _ φ y z Φ Φ' hm ⟨ht, hg1, hv1⟩ ⟨ht', hg2, hv2⟩
  obtain ⟨hx, hu, hs⟩ := ((GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c S S' φ y).2.2 z).1 hm
  obtain ⟨hg, v', hv', hk, hv⟩ := GlobalTheory.LamT.fibKey_keyPB E H Dw l Xo S S' φ.toRingHom y.x z.x Φ Φ' y.s z.s hx ht ht' hs
  have hvv : v' = Φ'.v := by
    funext i
    apply Over.OverMorphism.ext
    apply Φ'.m.cart.1.hom_ext
    · rw [hv i, hv1, hv2, hu]
      rfl
    · rw [Over.w, Over.w]
  subst hvv
  exact hk

end GlobalTheory.KeyFourth
end

