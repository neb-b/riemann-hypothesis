module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0014
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSelfDualLatticeNormOneIdealRankOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0188
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0296

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgebraMapEqOtoLLEOOfPin
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo

namespace GlobalTheory.Mem.R3.Rw

theorem algebraMap_eq_OtoLL_eO_of_pin : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
    B'.toPre = B.toPre → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt) (hX' : B'.fields.Ok)
    (Wt' : Set B'.places.Pl) (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
    (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
    (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
    Formalism.L2.Pj.LawsCore core'.toCore →
    letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
      (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F),
      RSideW z Wt' R' → HEq R'.toLevCh.mu0 z.R.toLevCh.mu0 →
      ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) →
      ∀ x : 𝓞 core'.Q.c.F, algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL (x : core'.Q.c.F) = (w'.st Z').toD7.what₂.OtoLL (core'.Q.eO x) := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg _hH hL Xg tr R' _hR _hmu ι _hι x
  apply (w'.st Z').toD7.what₂.embLL.injective
  have h1 : (w'.st Z').toD7.what₂.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' (x : core'.Q.c.F)) = ((x : core'.Q.c.F) : ℂ) := halg _
  have h2 : (w'.st Z').toD7.what₂.embLL ((w'.st Z').toD7.what₂.OtoLL (core'.Q.eO x)) = ((x : core'.Q.c.F) : ℂ) := hL.pins.2.2.1 x
  exact h1.trans h2.symm

end GlobalTheory.Mem.R3.Rw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseChangeEquivCrdOver
section
noncomputable section

namespace GlobalTheory.Mem.R3.Rw.GeoFW

open GlobalTheory.Mem.R3.Rw

variable {LL LL' Ks : Type} [Field LL] [Field LL'] [Field Ks] [Algebra Ks LL] [Algebra Ks LL']

def crdMap (ι : LL →+* LL') {n n' : ℕ} (hn : n = n') (x : Fin n → LL) : Fin n' → LL' := fun k' => ι (x (Fin.cast hn.symm k'))

theorem crdOver_crdMap (ι : LL →+* LL') {n n' : ℕ} (hn : n = n') (x : Fin n → LL) : CrdOver ι x (crdMap ι hn x) :=
  ⟨hn, fun k k' hk => by
    unfold crdMap
    congr 2
    exact Fin.ext (by simp [hk])⟩

theorem crdMap_eq_of_crdOver (ι : LL →+* LL') {n n' : ℕ} (hn : n = n') {x : Fin n → LL} {x' : Fin n' → LL'}
    (h : CrdOver ι x x') : crdMap ι hn x = x' := by
  funext k'
  exact (h.2 (Fin.cast hn.symm k') k' rfl).symm

def crdLin (ι : LL →+* LL') (hι : ∀ y, ι (algebraMap Ks LL y) = algebraMap Ks LL' y) {n n' : ℕ} (hn : n = n') :
    (Fin n → LL) →ₗ[Ks] (Fin n' → LL') where
  toFun := crdMap ι hn
  map_add' x y := by funext k; simp [crdMap]
  map_smul' c x := by funext k; simp [crdMap, Algebra.smul_def, hι]

theorem crdMap_injective (ι : LL →+* LL') {n n' : ℕ} (hn : n = n') : Function.Injective (crdMap ι hn) := by
  intro x y h
  funext k
  have := congrFun h (Fin.cast hn k)
  simp only [crdMap, Fin.cast_cast, Fin.cast_eq_self] at this
  exact ι.injective this

def baseChangeEquiv (ι : LL →+* LL') (hι : ∀ y, ι (algebraMap Ks LL y) = algebraMap Ks LL' y) {n n' : ℕ} (hn : n = n')
    (WK : Submodule Ks (Fin n → LL)) (WK' : Submodule Ks (Fin n' → LL'))
    (hmem : ∀ x x', CrdOver ι x x' → (x' ∈ WK' ↔ x ∈ WK)) (honto : ∀ x' ∈ WK', ∃ x : Fin n → LL, CrdOver ι x x') : WK ≃ₗ[Ks] WK' :=
  LinearEquiv.ofBijective
    (((crdLin ι hι hn).comp WK.subtype).codRestrict WK' fun x => (hmem _ _ (crdOver_crdMap ι hn x.1)).2 x.2)
    ⟨fun x y h => Subtype.ext (crdMap_injective ι hn (congrArg Subtype.val h)), fun x' => by
      obtain ⟨x, hx⟩ := honto x'.1 x'.2
      exact ⟨⟨x, (hmem _ _ hx).1 x'.2⟩, Subtype.ext (crdMap_eq_of_crdOver ι hn hx)⟩⟩

theorem baseChangeEquiv_crdOver (ι : LL →+* LL') (hι : ∀ y, ι (algebraMap Ks LL y) = algebraMap Ks LL' y) {n n' : ℕ}
    (hn : n = n') (WK : Submodule Ks (Fin n → LL)) (WK' : Submodule Ks (Fin n' → LL'))
    (hmem : ∀ x x', CrdOver ι x x' → (x' ∈ WK' ↔ x ∈ WK)) (honto : ∀ x' ∈ WK', ∃ x : Fin n → LL, CrdOver ι x x') (x : WK) :
    CrdOver ι x.1 (baseChangeEquiv ι hι hn WK WK' hmem honto x).1 :=
  crdOver_crdMap ι hn x.1

end GlobalTheory.Mem.R3.Rw.GeoFW

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BetaLowerAndSmul
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ENNReal

namespace GlobalTheory.PoincareLower

open Topology Filter

section General

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end General

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem isOpen_domFlat : IsOpen (DomFlat ι p q) := by
  refine isOpen_iff_mem_nhds.2 fun x0 hx0 => ?_
  refine Filter.eventually_all.2 fun τ => ExhB.posDef_eventually
    (fun v : ι × Fin p × Fin q → ℂ => 1 - (unflat v τ)ᴴ * unflat v τ) (fun i j => ?_)
    (fun v => isHermitian_one.sub (isHermitian_conjTranspose_mul_self _)) x0 (hx0 τ)
  simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, unflat, Matrix.of_apply]
  fun_prop

variable {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (B : BdData ι p q Γ)

end GlobalTheory.PoincareLower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChKerCCongr
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.SelC

section Congr

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  {A A' : Amb X} (hA : ∀ (a b : ℕ) T (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) c x,
    IsSdLat N → IsSdLat N' → A.jetK T N N' c x = A'.jetK T N N' c x)


include hA in
theorem kerOf_congr (u : Pr.Word) (i : ℕ) {b : ℕ} (lam' : X.Tau → DomWeight b) (T cA cB) {N : Submodule (𝓞 X.E) (Sp X.E (R.N i))}
    {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N') (fr fr' Ξ) :
    kerOf (stepC W Ch sel mu cst A u i lam') T cA cB N fr N' fr' Ξ = kerOf (stepC W Ch sel mu cst A' u i lam') T cA cB N fr N' fr' Ξ := by
  unfold kerOf stepC thDistC
  simp only [hA _ _ _ _ _ _ _ hN hN']


include hA in
theorem chKerC_congr (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (P : LevFam X.E X.K R.r Pr.vGs)
    (h : KerEquivC W Ch sel mu cst L A u m2 b hY P) (h' : KerEquivC W Ch sel mu cst L A' u m2 b hY P) :
    chKerC W Ch sel mu cst L A u m2 b hY P h = chKerC W Ch sel mu cst L A' u m2 b hY P h' := by
  classical
  have e1 : matK W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) = matK W Ch sel mu cst L (chTh W Ch sel mu cst A' u m2) := by
    funext i al be p p'
    exact kerOf_congr W Ch sel mu cst hA u i _ _ _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨p'.deco.2.lat, p'.deco.2.uni⟩ _ _ _
  have e2 : cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) = cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A' u m2) := by
    funext al p p' Y
    unfold cp1K
    exact if_congr Iff.rfl
      (kerOf_congr W Ch sel mu cst hA u m2 _ _ _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨p'.deco.2.lat, p'.deco.2.uni⟩ _ _ _) rfl
  have e3 : cp2K W Ch sel mu cst (chTh W Ch sel mu cst A u m2) = cp2K W Ch sel mu cst (chTh W Ch sel mu cst A' u m2) := by
    funext p Y d
    unfold cp2K
    exact if_congr Iff.rfl
      (kerOf_congr W Ch sel mu cst hA u (m2 + 1) _ _ _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩
        ⟨(tilQ sel mu u d).2.lat, (tilQ sel mu u d).2.uni⟩ _ _ _) rfl
  unfold chKerC chKer
  congr 1
  · funext i al be
    split_ifs
    · congr 1
      rw [e1]
    · rfl
  · funext al
    congr 1
    rw [e2]

end Congr

section True

open GlobalTheory.Core.Ht2 GlobalTheory.Mem.Col2.KerRat

variable {B : Base} {X : PreX B.toPre} {I : TC B X} (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
  (ht : I.IsTw) (hJ : ColIn.JetsIn I)
  (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞) (hX : B.fields.Ok)


include hχ in
theorem jetK_chi (a b : ℕ) (T) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E a)) (N' : Submodule (𝓞 B.fields.E) (Sp B.fields.E b)) (c x)
    (hN : IsSdLat N) (hN' : IsSdLat N') : (I.J.amb B χ).jetK T N N' c x = I.A.jetK T N N' c x := by
  have hf : Th.chiFac B.host χ a b N N' = Th.chiFac B.host I.chi a b N N' := by
    unfold Th.chiFac
    rw [hχ (Th.detId B.host (Th.stdL B.host _) N) (RcHyp.n1_detStd I l Z hN),
      hχ (Th.detId B.host (Th.stdL B.host _) N') (RcHyp.n1_detStd I l Z hN')]
  have e3 : (I.J.amb B χ).e a b N N' = I.A.e a b N N' := by
    show I.J.V.eNat χ _ _ N N' = I.J.V.eNat I.chi _ _ N N'
    unfold Th.VacIn.eNat
    rw [hf]
  have e4 : (I.J.amb B χ).thInd T N N' c x = I.A.thInd T N N' c x := by
    funext z
    unfold Amb.thInd
    rw [e3]
    rfl
  funext m
  unfold Amb.jetK
  rw [e4, show (I.J.amb B χ).chiF a b N N' = I.A.chiF a b N N' from hf]
  rfl


include hp ht hJ hχ in
theorem exists_cpl (u : B.Word) (a : I.ι) (cst : LocCst B.fields (rowSG (B.primes X) I.sel (I.tup a)))
    (L : ChIdx B.fields (B.primes X) B.R (I.Q a)) (e1 : cst = I.cst a) (e2 : L = I.idx a) (b : L.β (B.R.m - 2 + 1))
    (hY : YbHyp (Pr := B.primes X) (R := B.R) I.sel (I.tup a) cst L u (B.R.m - 2) b)
    (hK : KerEquivC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) cst L (I.J.amb B χ) u (B.R.m - 2) b hY I.Ps)
    (hF : ∀ j, (chF (Pr := B.primes X) B.wts I.sel (I.tup a) L u j).Ok) (hL : L.Ok I.Ch I.sel (I.tup a) cst I.glob (B.R.m - 2)) :
    ∃ c : CplData I u a, ∀ (φ : ColsK I u) (z : RowsK I a),
      PtilFF (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (mtildeOk (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) hX I.Ps) u
        (colC (chKerC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) cst L (I.J.amb B χ) u (B.R.m - 2) b hY I.Ps hK) hF hL φ).1 z.1 =
        c.per h hX φ z := by
  subst e1 e2
  have hK' := (RcHyp.hyps_of_isTw I h hp l Z ht hJ I.chi (fun _ _ => rfl) a u).2.2.2 b hY
  refine ⟨⟨b, hY, hK', hF⟩, fun φ z => ?_⟩
  rw [chKerC_congr (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (jetK_chi l Z χ hχ) u _ b hY I.Ps hK hK']
  rfl

theorem exists_eNu (l0 : I.Law0 l) (u : B.Word) :
    ∃ e : (Fin (ramDim (Pr := B.primes X) B.wts I.Ch hX u) → B.LL) ≃ₗ[B.LL] (Z.V.div.Nu u).V,
      (∀ v x y, Formalism.HermitianLatticesTheory.majAt (Z.V.div.Nu u).b (Z.V.div.Nu u).X v (e x) (e y) =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL _) (MramH (Pr := B.primes X) B.wts I.Ch hX u).X v x y) ∧
      ∀ x, Z.V.nuIn u (e x) = colForm I l h u I.mu0 (colOfCoord (Pr := B.primes X) B.wts I.Ch hX u x) := by
  obtain ⟨eM, hs, -, hn, -⟩ := GlobalTheory.AtG.ramCols_true I h l Z l0 u
  let eL : (Z.V.div.Nu u).V ≃ₗ[B.LL] MramV (Pr := B.primes X) B.wts I.Ch u := { eM with map_smul' := hs }
  let bs := ramBas (Pr := B.primes X) B.wts I.Ch hX u
  have hin : ∀ x, Z.V.nuIn u ((bs.equivFun.symm.trans eL.symm) x) =
      colForm I l h u I.mu0 (colOfCoord (Pr := B.primes X) B.wts I.Ch hX u x) := fun x =>
    (hn _).trans (congrArg (fun φ : MramV (Pr := B.primes X) B.wts I.Ch u => colForm I l h u I.mu0 φ.1) (eL.apply_symm_apply _))
  refine ⟨bs.equivFun.symm.trans eL.symm, fun v x y => ?_, hin⟩
  haveI : IsTotallyComplex B.LL := hX.cplxK
  refine GlobalTheory.Mem.RowSides.majAt_eq_of_normAt _ _ _ _ v (bs.equivFun.symm.trans eL.symm).toLinearMap (fun x => congrArg (· ^ 2) ?_) x y
  refine (Z.V.nuIn_norm u v _).trans ?_
  rw [LinearEquiv.coe_coe, hin]
  refine (GlobalTheory.Core.ColNorm.nrm_stepZero_eq I h hX l u I.mu0 _ (colOfCoord (Pr := B.primes X) B.wts I.Ch hX u x) (fun _ => rfl) v).trans ?_
  refine (ramInclH_norm (Pr := B.primes X) B.wts I.Ch hX u v (bs.equivFun.symm x)).symm.trans ?_
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  congr 2
  funext i
  exact congrArg v.embedding (congrFun (bs.equivFun.apply_symm_apply x) i)


include hJ in
theorem perCol_eq (l0 : I.Law0 l) (e : ∀ a : (I.cols l).Tup, Df.MtCx I a ≃ₗ[ℂ] Z.W.Amb a)
    (h0 : ∀ u F, Df.SameForm I l u I.mu0 F ((Z.W.eMt0 u).symm (e (I.cols l).mu0 F)))
    (h1 : ∀ u (a : (I.cols l).Tup) F, Df.SameForm I l u a F ((Z.W.eMtTw u a).symm (e a F)))
    (u : B.Word) (a : I.ι) (c : CplData I u a) (n : (Z.V.div.Nu u).V) (φ : ColsK I u) (hn : Z.V.nuIn u n = colForm I l h u I.mu0 φ)
    (z : RowsK I a) : Z.W.perCol u a (Z.V.jN u n) (e a (Df.toCx I hX a z)) = B.embLL (c.per h hX φ z) := by
  obtain ⟨-, -, -, -, hT⟩ := GlobalTheory.AtG.ramCols_true I h l Z l0 u
  have hM := (colMatchAll I h hX l Z hJ u a).2 c (colForm I l h u a φ) φ
  have hj := (Z.V.nuIn_jN u n).trans (congrArg ((I.fm l u I.mu0).emb 0) hn)
  by_cases ha : a = I.mu0
  · subst ha
    refine (Z.W.perCol_base_eq_PtilCol u _ _).trans ?_
    rw [hj]
    exact hM _ z (fun _ => rfl) fun p => h0 u _ p
  · refine (Z.W.perCol_tie u a ha _ _).trans ?_
    rw [hj, ← hT a φ]
    exact hM _ z (fun _ => rfl) fun p => h1 u a _ p


set_option maxHeartbeats 1000000 in
theorem face_pt (l0 : I.Law0 l) (e : ∀ a : (I.cols l).Tup, Df.MtCx I a ≃ₗ[ℂ] Z.W.Amb a)
    (h0 : ∀ u F, Df.SameForm I l u I.mu0 F ((Z.W.eMt0 u).symm (e (I.cols l).mu0 F)))
    (h1 : ∀ u (a : (I.cols l).Tup) F, Df.SameForm I l u a F ((Z.W.eMtTw u a).symm (e a F)))
    (U : Set I.ι) (Xg : Finset (Gc B X → B.LL)) (tr : TrI B X)
    (Zs : DefSub (famC I hX U Xg tr).fam3.amb3) (u : B.Word) (a : I.ι) (ha) (x : Fin (ramDim (Pr := B.primes X) B.wts I.Ch hX u) → B.LL)
    (n : (Z.V.div.Nu u).V) (hn : Z.V.nuIn u n = colForm I l h u I.mu0 (colOfCoord (Pr := B.primes X) B.wts I.Ch hX u x))
    (f : Fin (((famC I hX U Xg tr).side3 (lev1 I) (chr1 I) Zs).nV ⟨I.tup a, ha⟩) → B.LL) (z : RowsK I a)
    (hz : z.1 = ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).ev Zs ⟨I.tup a, ha⟩ f).1.1) :
    B.embLL (((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).face Zs).Pt u ⟨I.tup a, ha⟩ x f) =
      Z.W.perCol u a (Z.V.jN u n) (e a (Df.toCx I hX a z)) := by
  obtain ⟨c, hc⟩ := exists_cpl h hp l Z ht hJ χ hχ hX u a _ _ (cstT_tup ht a) (idxT_tup ht a)
    ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).b ⟨I.tup a, ha⟩ u) ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).hY ⟨I.tup a, ha⟩ u)
    ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).hK ⟨I.tup a, ha⟩ u) ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).hF ⟨I.tup a, ha⟩ u)
    ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).hL ⟨I.tup a, ha⟩)
  rw [perCol_eq h l Z hJ hX l0 e h0 h1 u a c n _ hn z, ← hc, hz]
  rfl

end True

end GlobalTheory.Mem.R3.SelC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernTopDensityModelMetricOrigin
section
set_option autoImplicit false

open Formalism.DegreeFormula MvPolynomial GlobalTheory.GoodMetric GlobalTheory.DomainDens

noncomputable section

namespace GlobalTheory.DomainDens

theorem coeff_charpolyRev_card {R : Type} [CommRing R] [Nontrivial R] {p : ℕ} (M : Matrix (Fin p) (Fin p) R) :
    M.charpolyRev.coeff p = (-1) ^ p * M.det := by
  rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
    Polynomial.revAt_le le_rfl, Nat.sub_self, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin, ← mul_assoc,
    ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

theorem chernTop_model_origin : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n), GlobalTheory.GoodMetric.chernTop (m := fun _ : ι => p) (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) (fun u τ => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 = GlobalTheory.TrueCx.grassConst p q ^ Fintype.card ι := by
  intro ι _ p q n h
  have hc : ∀ τ : ι, chernPoly (fun u => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 p =
      C ((-1 : ℂ) ^ p) * (blockSym h τ).det := by
    intro τ
    rw [chernPoly, _root_.GlobalTheory.DomainDens.curvPoly_model_zero ι p q n h τ, neg_neg, coeff_charpolyRev_card, map_pow, map_neg, map_one]
  have hs : (algebraMap ℝ ℂ ((-1 : ℝ) ^ p)) * (-1 : ℂ) ^ p = 1 := by
    rw [map_pow, map_neg, map_one, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have ha : aeval (fun x : ι × ℕ => chernPoly (fun u => Matrix.transpose (hP (unflat (GlobalTheory.UnifDens.flatL h u) x.1))⁻¹) 0 x.2)
      (∏ τ : ι, (MvPolynomial.C ((-1 : ℝ) ^ p) * MvPolynomial.X (τ, p)) ^ q) = ∏ τ, (blockSym h τ).det ^ q := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_pow, map_mul, aeval_X, aeval_C, hc τ, ← mul_assoc, MvPolynomial.algebraMap_apply, ← C_mul, hs, C_1,
      one_mul]
  have hn : n = Fintype.card ι * (p * q) := by
    rw [← h]; simp [Fintype.card_prod, Fintype.card_fin]
  have h1 : Fintype.card (Unit × Fin p × Fin q) = p * q := by simp [Fintype.card_prod, Fintype.card_fin]
  have e : (∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial)) =
      ((∏ i ∈ Finset.range p, (((q + i).factorial : ℝ) / i.factorial) : ℝ) : ℂ) := by push_cast; rfl
  simp only [chernTop]
  rw [ha, _root_.GlobalTheory.DomainDens.topCoeff_prod_blockSym_det_pow ι p q n h h1, _root_.GlobalTheory.topCoeff_blockSym_det_pow p q h1, e, ← Complex.ofReal_pow, Complex.ofReal_re, GlobalTheory.TrueCx.grassConst,
    div_pow, hn, pow_mul', div_eq_inv_mul]

end GlobalTheory.DomainDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChiROfEnlarged
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.R3.Rw.chiR_of_enlarged : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
    B'.toPre = B.toPre → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : Dat (w.st Z) w.I hX T Wt) (Z' : w'.Lt) (hX' : B'.fields.Ok)
    (Wt' : Set B'.places.Pl) (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
    (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
    (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
      HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
      HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
      HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
    Formalism.L2.Pj.LawsCore core'.toCore →
    letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
      (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F),
      RSideW z Wt' R' → HEq R'.toLevCh.mu0 z.R.toLevCh.mu0 →
      ∀ ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) →
      Formalism.IndefR.FWT.ChiR core' R'.toRealDat := by
  intro B B' f f' T T' w w' hP
  obtain ⟨P'⟩ := B'
  dsimp only at hP
  subst hP
  intro Z hX Wt z Z' hX' Wt' core' alg' halg hH hL Xg tr R' hR hmu ι hι
  obtain ⟨⟨⟨H', l', c', Dw', Xo'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := core'
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := hH
  dsimp only at h1 h2 h3 h12
  subst h1
  obtain rfl := eq_of_heq h2
  obtain rfl := eq_of_heq h3
  obtain rfl := eq_of_heq h12
  have hmu' := eq_of_heq hmu
  letI := z.alg
  have halg' : ∀ y : z.core.Q.c.F, ι (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL y) =
      @algebraMap z.core.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y := by
    intro y
    apply (w'.st Z').toD7.what₂.embLL.injective
    rw [hι]
    exact (z.alg_eq y).trans (halg y).symm
  have hE2 : (w'.st Z').toD7.what₂.embLL.comp (@algebraMap z.core.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg') =
      (w.st Z).toD7.what₂.embLL.comp (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL) := by
    ext y
    exact (halg y).trans (z.alg_eq y).symm
  have hE : (w'.st Z').toD7.embE = ι.comp (w.st Z).toD7.embE := by
    ext x
    apply (w'.st Z').toD7.what₂.embLL.injective
    have e1 := congrArg (fun g => g x) (w'.st Z').toD7.embE_φ₀
    have e2 := congrArg (fun g => g x) (w.st Z).toD7.embE_φ₀
    show _ = (w'.st Z').toD7.what₂.embLL (ι ((w.st Z).toD7.embE x))
    rw [hι]
    exact e1.trans e2.symm
  intro i σ' hg
  have hcomp : σ'.comp (@algebraMap z.core.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg') =
      (σ'.comp ι).comp (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL) := by
    ext y
    exact congrArg σ' (halg' y).symm
  have hlabE : labE σ' = labE (σ'.comp ι) := by
    funext τ
    unfold labE labLL
    rw [hE]
    rfl
  have hz := z.geo.fw.chiR i (σ'.comp ι) (hcomp ▸ hg)
  obtain ⟨a1, a2, a3, a4, a5⟩ := hz
  rw [hcomp]
  refine ⟨a1, a2, fun ρ => ?_, fun x hx => ?_, fun hσ => ?_⟩
  · have : lab σ' ρ = lab (σ'.comp ι) ρ := by
      unfold lab
      rw [hlabE]
      try rfl
    rw [this]
    exact a3 ρ
  · obtain ⟨y, hy1, hy2⟩ := a4 x hx
    refine ⟨y, ?_, hy2.trans (congrArg σ' (halg' y))⟩
    have hm : ((R'.toRealDat.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = ((z.R.toRealDat.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) := by
      rw [hmu']
      rfl
    refine hm.trans (hy1.trans ?_)
    rw [← halg', hι]
  · have hσ' : (σ'.comp ι).comp (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL) =
        (w.st Z).toD7.what₂.embLL.comp (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL) := by
      first
        | exact hσ.trans hE2
        | exact (hcomp.symm.trans hσ).trans hE2
    refine (a5 hσ').trans ?_
    rw [hmu']
end

