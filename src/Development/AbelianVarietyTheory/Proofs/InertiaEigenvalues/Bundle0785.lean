module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0770
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0776
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0766
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0771
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0779
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameMatricesIntegralOfMemCompletedLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0781
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameIntegralIffPartsConjHalf
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.ConjHalfSplitInt

theorem frMapAdj_int_iff : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q : Finset (Pl D.host.E)) (eg eQ : AE D), IsIdemSum eg Pg → IsIdemSum eQ Q → Disjoint Pg Q → IsIdemSum (eg + eQ) (Pg ∪ Q) → ∀ x : WO S T, IsHalf (cA D (eg + eQ)) x → (IsIntM (frMapAdj S T βS βT x) ↔ IsIntM (frMapAdj S T βS βT (cA D eg • x)) ∧ IsIntM (frMapAdj S T βS βT (cA D eQ • x))) := by
  intro D S T βS βT Pg Q eg eQ hg hQ _ _ x hx
  have hx' : cA D (eg + eQ) • x = x := (GlobalTheory.ExportSeries.RestrictHalfModel.isHalf_iff' _ _).1 hx
  have hsplit : x = cA D eg • x + cA D eQ • x := by rw [← add_smul, ← map_add (f := _), hx']
  have hA : ∀ e : AE D, frMapAdj S T βS βT (cA D e • x) = toEAf D e • frMapAdj S T βS βT x := fun e => by
    rw [GlobalTheory.RedHalfDrop.frMapAdj_smul_eq, Formalism.L2.Theta.cA_cA]
  have hint : ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P →
      toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun e P h => by
    rw [← GlobalTheory.ExportSeries.idem_eq h]
    unfold GlobalTheory.ExportSeries.idem
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact sum_mem fun PP hPP => GlobalTheory.RedHalfDrop.int_idemAt ⟨e, h⟩ hPP
  constructor
  · intro h
    rw [hA, hA]
    exact ⟨fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem (hint _ _ hg) (h i j),
      fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem (hint _ _ hQ) (h i j)⟩
  · rintro ⟨h1, h2⟩
    rw [hsplit, GlobalTheory.PlaceVec.frMapAdj_add]
    intro i j
    rw [Matrix.add_apply]
    exact add_mem (h1 i j) (h2 i j)

end GlobalTheory.ConjHalfSplitInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormReadingGaloisConjExpansion
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.ConjExpand

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}


set_option maxHeartbeats 1000000 in
theorem read_of_isBC (M : OMDat C R i Tp tup) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c M.lev2)
    (cc : (C.U ((i : ℕ) + 1) M.s0).Comp → ℂ) (L : ℂ) (z : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n m : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) M.c'} (hf : f ∈ sec _ M.c' a n) {as : Fin m → M.c'.F}
    {fs : Fin m → Rul (C.Q.Xo ((i : ℕ) + 1)) C.Q.c} (hfs : ∀ k, fs k ∈ sec _ C.Q.c a n) (h : IsBC M.hle f as fs)
    (g : GA D (Wc D i)) :
    cc (M.dict g).1 * L * M.mu g * rdU (unfBC M.hle (C.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2 =
      ∑ k, (as k : ℂ) * (L * M.phi cc (actLev C.Q.c M.lev2 z (fs k)) g) := by
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ M.hle _ _ hact).2 a n z m as fs f hf hfs h
  have h2 := congrFun (congrFun (rdU_unfBC M.hle (C.U ((i : ℕ) + 1)) (inC M.c') h1) (M.dict g).1) (M.dict g).2
  rw [Finset.sum_apply, Finset.sum_apply] at h2
  refine (congrArg (fun w => cc (M.dict g).1 * L * M.mu g * w) h2).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show cc _ * L * M.mu _ * ((as k : ℂ) * _) = (as k : ℂ) * (L * (cc _ * M.mu _ * _))
  ring

end GlobalTheory.ConjExpand


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.ConjExpand.conjFun_galRul : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (hf : Fixes M.c' ta) (z : G), ∀ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) M.c' (unfBC M.hle (T.U ((i : ℕ) + 1))) (wtA (κ i)) (Vc D i).rank, M.EquivAt (κ i) (T.cE ((i : ℕ) + 1) M.s0) → ConjFun M (κ i) τ 1 (fun g => T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * M.mu g * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z f) (M.dict g).1 (M.dict g).2) (fun g => T.cE ((i : ℕ) + 1) M.s0 (M.dict g).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * M.mu g * rdU (unfBC M.hle (T.U ((i : ℕ) + 1)) (inC M.c')) (actLev M.c' M.lev2 z (galRul hf f)) (M.dict g).1 (M.dict g).2) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT i Tp tup M hP τ ta hta hB hf z f hfc hE
  have hact := hP.act.1
  obtain ⟨ht⟩ := id hT
  have hn : (κ i).n = (Vc D i).rank :=
    (ht.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ M.hle).2 _ (T.U ((i : ℕ) + 1)) _ _ f hfc
  have hsec := ((mem_cusp _ _ _ _ _ _).1 hfc).1
  have hs : ∀ k, fs k ∈ sec _ T.Q.c (wtA (κ i)) (Vc D i).rank := fun k => ((mem_cusp _ _ _ _ _ _).1 (hfs k)).1
  have hgal := GlobalTheory.GalTw.galRul_sec_val_semilinear _ _ (T.Q.Dw ((i : ℕ) + 1)) _ (T.Q.Xo ((i : ℕ) + 1)) M.c' ta hf
  have hFix : ∀ x : T.Q.c.F, ta (incF T.Q.c M.c' M.hle x) = incF T.Q.c M.c' M.hle x := by
    intro x
    apply Subtype.ext
    rw [hta]
    exact hB.core x
  have hgsec := ((hgal.1 _ _ f hsec).1)
  have hgBC := hgal.2.2 T.Q.c M.hle hFix _ _ m as fs f hsec hBC
  have hkeep : ∀ k, actLev T.Q.c M.lev2 z (fs k) ∈ T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := by
    intro k
    obtain ⟨y, hy, -⟩ := hP.lift.lev z
    refine (hE z y hy (fs k) ?_).1
    rw [hn]
    exact hfs k
  obtain ⟨Fk, hFk⟩ : ∃ Fk : Fin m → T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      ∀ k, (Fk k : T.toCore.R ((i : ℕ) + 1)) = actLev T.Q.c M.lev2 z (fs k) := ⟨fun k => ⟨_, hkeep k⟩, fun _ => rfl⟩
  have e1 := fun g => GlobalTheory.ConjExpand.read_of_isBC M hact (T.cE ((i : ℕ) + 1) M.s0) (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) z hsec hs hBC g
  have e2 := fun g => GlobalTheory.ConjExpand.read_of_isBC M hact (T.cE ((i : ℕ) + 1) M.s0) (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) z hgsec hs hgBC g
  simp only [← hFk] at e1 e2
  refine ⟨⟨m, fun k => (as k : ℂ), Fk, fun g => e1 g⟩, ?_⟩
  intro n a h hex g
  have hz : Expands M (κ i) (fun _ => 0) (Fin.append a (fun k => -(as k : ℂ))) (Fin.append h Fk) := by
    intro g
    have h0 := (e1 g).symm.trans (hex g)
    show (0 : ℂ) = _
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, neg_mul, Finset.sum_neg_distrib]
    linear_combination h0
  have hz' : (0 : ℂ) = _ := _root_.GlobalTheory.ConjRelation.expands_zero_conj D G Pl0 T0 A T R F κ v₀ hC hT i Tp tup M hP τ hB.core _ _ _ hz g
  rw [Fin.sum_univ_add] at hz'
  simp only [Fin.append_left, Fin.append_right, map_neg, neg_mul, Finset.sum_neg_distrib] at hz'
  refine (e2 g).trans ?_
  simp only [one_mul, hta]
  linear_combination hz'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DatumFnLevPeriod
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace GlobalTheory.LevPeriod

end GlobalTheory.LevPeriod

namespace GlobalTheory.LevPeriod

theorem exists_split {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} (l : Geo.Tor.Level H) :
    ∃ α ∈ l.Mb, ∃ β ∈ Mfr l, α + β = 1 := by
  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ Mfr l := by
    rw [Mfr, l.coprime]; exact Submodule.mem_top
  exact Submodule.mem_sup.1 h1

end GlobalTheory.LevPeriod

namespace GlobalTheory.LevPeriod

end GlobalTheory.LevPeriod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterProductFormula
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwistDetStab

open Classical

variable {D : D7}

theorem infPart_idemAt (P : Pl D.host.E) (e : AE D) (h : Formalism.L2.NTheta.IsIdemAt e P) : infPart D e = 0 := by
  obtain ⟨⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩, -⟩ := h
  have k1 := congrArg (infPart D) h1
  have k2 := congrArg (infPart D) h2
  have k3 := congrArg (infPart D) h3
  simp only [RingHom.map_mul, RingHom.map_add (f := _), RingHom.map_zero] at k1 k2 k3
  have k4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    simp [infPart, Algebra.TensorProduct.algebraMap_apply]
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  rw [k4] at k3
  linear_combination -k1 + infPart D e * k3 - k2

theorem idemAt_mul_idem {Q : Finset (Pl D.host.E)} (h : SplitSet Q) {P : Pl D.host.E} (hP : P ∈ Q) :
    idemAt P * idem Q = idemAt P :=
  GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (h.isIdemAt ha).1) (fun a ha b hb hab => h.mul_eq_zero ha hb hab) hP

theorem idem_mul_self {Q : Finset (Pl D.host.E)} (h : SplitSet Q) : idem Q * idem Q = idem Q := by
  show (∑ P ∈ Q, idemAt P) * idem Q = idem Q
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun P hP => idemAt_mul_idem h hP

theorem idem_mul_idem_of_disjoint {Q s s' : Finset (Pl D.host.E)} (h : SplitSet Q) (hs : s ⊆ Q) (hs' : s' ⊆ Q)
    (hd : Disjoint s s') : idem s * idem s' = 0 := by
  rw [idem, idem, Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj =>
    h.mul_eq_zero (hs hi) (hs' hj) fun e => Finset.disjoint_left.1 hd hi (e ▸ hj)

theorem idem_mul_conj {Q s s' : Finset (Pl D.host.E)} (h : SplitSet Q) (hs : s ⊆ Q) (hs' : s' ⊆ Q) :
    idem s * cA D (idem s') = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [idem, idem, map_sum, Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => h.mul_conj (hs hi) (hs' hj)

theorem val_mul (d e₁ e₂ : AE D) (h : e₁ * e₂ = 0) :
    (e₁ * d + (1 - e₁)) * (e₂ * d + (1 - e₂)) = (e₁ + e₂) * d + (1 - (e₁ + e₂)) := by
  linear_combination (d * d - 2 * d + 1) * h

theorem prod_val (d : AE D) {Q : Finset (Pl D.host.E)} (h : SplitSet Q) :
    ∀ s ⊆ Q, ∏ P ∈ s, (idemAt P * d + (1 - idemAt P)) = idem s * d + (1 - idem s) := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hs
    rw [Finset.prod_insert ha, ih ((Finset.subset_insert a s).trans hs)]
    have e1 : idem (insert a s) = idemAt a + idem s := Finset.sum_insert ha
    rw [e1]
    refine val_mul d _ _ ?_
    have := idem_mul_idem_of_disjoint h (s := {a}) (s' := s)
      (Finset.singleton_subset_iff.2 (hs (Finset.mem_insert_self a s))) ((Finset.subset_insert a s).trans hs)
      (Finset.disjoint_singleton_left.2 ha)
    rwa [show idem ({a} : Finset (Pl D.host.E)) = idemAt a from Finset.sum_singleton _ _] at this

theorem detChar_eq_prod_res : ∀ {D : D7} {V : HSp D} {A : Type} [CommGroup A] (t : Twist D A), t.Good →
    ∀ (β : GL (Fin V.rank) (Lev.EAf D)) {Q' : Finset (Pl D.host.E)}, SplitSet Q' → t.Q ⊆ Q' → ∀ {κ : GA D V},
    κ ∈ GfC V → Lev.finE V κ ∈ St β → SuppAt (idem Q') V κ →
    detChar V t.chi κ = ∏ PP ∈ t.Q, t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))) := by
  intro D V A _ t ht β Q' hQ' hsub κ _ hst hsupp
  have he : idem Q' * idem Q' = idem Q' := idem_mul_self hQ'
  have hce : idem Q' * cA D (idem Q') = 0 := hQ'.isIdemSum.2
  have hroot : IsDetRoot V κ (GlobalTheory.VecInv.detAt (idem Q') he V κ) := by
    have hx : IsDetAt (idem Q') V κ (GlobalTheory.VecInv.detAt (idem Q') he V κ) := GlobalTheory.VecInv.isDetAt_detAt _ he V κ
    unfold IsDetAt at hx
    unfold IsDetRoot
    rw [hx]
    exact idempotent_det_conj_identity (cA D) (idem Q') he hce (mt V κ) hsupp (det_conj_mul V κ)
  rw [detChar_eq ht.real hroot]
  have hR : Q' \ t.Q ⊆ Q' := Finset.sdiff_subset
  have heR : idem (Q' \ t.Q) * idem (Q' \ t.Q) = idem (Q' \ t.Q) := idem_mul_self (hQ'.mono hR)
  have hPi : ∀ P ∈ t.Q, idemAt P * idemAt P = idemAt P := fun P hP => (hQ'.isIdemAt (hsub hP)).1.1
  have hsum : idem (Q' \ t.Q) + idem t.Q = idem Q' := Finset.sum_sdiff hsub
  have hRQ : idem (Q' \ t.Q) * idem t.Q = 0 := idem_mul_idem_of_disjoint hQ' hR hsub Finset.sdiff_disjoint
  have hsplit : GlobalTheory.VecInv.detAt (idem Q') he V κ = GlobalTheory.VecInv.detAt (idem (Q' \ t.Q)) heR V κ *
      ∏ P ∈ t.Q.attach, GlobalTheory.VecInv.detAt (idemAt P.1) (hPi P.1 P.2) V κ := by
    ext
    rw [Units.val_mul, Units.coe_prod]
    show idem Q' * (mt V κ).det + (1 - idem Q') = (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) *
      ∏ P ∈ t.Q.attach, (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1))
    rw [Finset.prod_attach t.Q (fun P => idemAt P * (mt V κ).det + (1 - idemAt P)),
      prod_val _ ht.split t.Q (Finset.Subset.refl _), val_mul _ _ _ hRQ, hsum]
  have hw : t.chi (GlobalTheory.VecInv.detAt (idem (Q' \ t.Q)) heR V κ) = 1 := by
    refine ht.unram _ ?_ (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.StabDet.toEAf_detAt_mem hst _ heR))
      (GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (GlobalTheory.StabDet.toEAf_detAt_inv_mem hst _ heR)) ?_
    · have hinf : infPart D (idem (Q' \ t.Q)) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [idem, map_sum]
        exact Finset.sum_eq_zero fun P hP => infPart_idemAt P _ (hQ'.isIdemAt (hR hP))
      show infPart D (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) = 1
      rw [map_add (f := _), map_mul, map_sub, map_one, hinf]
      ring
    · have a1 : idem t.Q * idem (Q' \ t.Q) = 0 := idem_mul_idem_of_disjoint hQ' hsub hR Finset.disjoint_sdiff
      have a2 : idem (Q' \ t.Q) * cA D (idem t.Q) = 0 := idem_mul_conj hQ' hR hsub
      show (idem t.Q + cA D (idem t.Q)) * (idem (Q' \ t.Q) * (mt V κ).det + (1 - idem (Q' \ t.Q))) =
        idem t.Q + cA D (idem t.Q)
      linear_combination ((mt V κ).det - 1) * (a1 + a2)
  rw [hsplit, map_mul, hw, one_mul, map_prod,
    ← Finset.prod_attach t.Q (fun PP => t.res PP (Matrix.GeneralLinearGroup.det (redFn β PP (Lev.finE V κ))))]
  refine Finset.prod_congr rfl fun P _ => ?_
  refine ht.res P.1 P.2 _ ?_ (GlobalTheory.StabDet.toEAf_detAt_mem hst _ (hPi P.1 P.2)) _
    (GlobalTheory.StabDet.res_detAt hst _ (hPi P.1 P.2) P.1 (hQ'.isIdemAt (hsub P.2))).symm
  show (1 - idemAt P.1) * (idemAt P.1 * (mt V κ).det + (1 - idemAt P.1)) = 1 - idemAt P.1
  linear_combination (1 - (mt V κ).det) * hPi P.1 P.2

end GlobalTheory.TwistDetStab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftLevelActsByInverseCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.TypeLaw

variable {D : D7}

theorem setIntegral_mul_right_of_fd {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (k : G) (hk : Measure.map (fun g => g * k) μ = μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    ∫ g in 𝓕, f (g * k) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  have hmp : MeasurePreserving (fun g : G => g * k) μ μ := ⟨measurable_mul_const k, hk⟩
  have hemb : MeasurableEmbedding (fun g : G => g * k) := measurableEmbedding_mulRight k
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ (γ : Γ) (g : G), (fun g : G => f (g * k)) (γ • g) = (fun g : G => f (g * k)) g := by
    intro γ g
    simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
    exact hf γ γ.2 _
  rw [h𝓕.setIntegral_eq h2 hinv]
  exact hmp.setIntegral_preimage_emb hemb f 𝓕

theorem flagOneLevel_eq_self_of_trivial {n : ℕ} (L : LevDat D.host.E ℂ n) (hL : L.P = LevelP.triv L.Pg L.r ℂ) : flag1L L = L := by
  cases L
  simp only at hL
  subst hL
  rfl

theorem adForms_right {G Γ W : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (F : G → W)
    (hF : F ∈ Formalism.IndefR.Bridge.AdForms ι ρ J χ) (x : G) (k : J) : F (x * k) = (χ k : ℂ) • F x := by
  have h1 := hF 1 x k
  rw [map_one, one_mul, map_one, Module.End.one_apply] at h1
  exact h1

theorem adForm_type (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (c : CoefA V)
    (F : Formalism.IndefR.Bridge.Gf V → c.W)
    (hF : F ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
    (κ : GA D V) (hκ : κ ∈ levG V β (flag1L L)) (x : Formalism.IndefR.Bridge.Gf V) :
    F (x * (finHom V).rangeRestrict κ) = levChi V β (flag1L L) κ • F x := by
  have hmem : (finHom V).rangeRestrict κ ∈ (levEnv V β L).J := by
    show finE V κ ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L)
    exact hκ.2
  have h1 := adForms_right (W := c.W) (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ F hF x ⟨_, hmem⟩
  have hχ : (((levEnv V β L).χ ⟨_, hmem⟩ : ℂˣ) : ℂ) = levChi V β (flag1L L) κ := rfl
  rw [hχ] at h1
  exact h1

end GlobalTheory.DownLift.TypeLaw

namespace GlobalTheory.DownLift.TypeLaw

theorem datVt_P {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    (R.datVt i t).P = LevelP.triv (R.datVt i t).Pg (R.datVt i t).r ℂ := by
  simp [LevCh.datVt, datY, LevelP.conj, LevelP.triv]
  rfl

end GlobalTheory.DownLift.TypeLaw

namespace GlobalTheory.DownLift.TypeLaw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem extV_type (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (κ : GA D (Vc D i))
    (hκ : κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t)) (h : GA D (Vc D i)) :
    R.extV i t y (h * κ) = levChi (Vc D i) (R.βV i) (R.datVt i t) κ • R.extV i t y h := by
  have hL : flag1L (R.datVt i t) = R.datVt i t := flagOneLevel_eq_self_of_trivial _ (datVt_P R i t)
  have hκ1 : κ ∈ levG (Vc D i) (R.βV i) (flag1L (R.datVt i t)) := by rw [hL]; exact hκ
  have hc0 : levChi (Vc D i) (R.βV i) (R.datVt i t) κ ≠ 0 := levChi_ne_zero _ κ
  have hchi : levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ = levChi (Vc D i) (R.βV i) (R.datVt i t) κ := by rw [hL]
  have hyA : (R.HV i t).e y ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J (levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ :=
    (hM.HV i t).2.1.le ⟨y, rfl⟩
  have hty : ∀ x, (R.HV i t).e y x = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ •
      (R.HV i t).e y (x * (finHom (Vc D i)).rangeRestrict κ) := by
    intro x
    have h1 := adForm_type (Vc D i) (R.βV i) (R.datVt i t) (R.cV i) ((R.HV i t).e y) hyA κ hκ1 x
    have h2 : (R.HV i t).e y (x * (finHom (Vc D i)).rangeRestrict κ) =
        levChi (Vc D i) (R.βV i) (R.datVt i t) κ • (R.HV i t).e y x :=
      h1.trans (congrArg (· • (R.HV i t).e y x) hchi)
    exact (inv_smul_smul₀ hc0 _).symm.trans (congrArg ((levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • ·) h2.symm)
  have e1 := GlobalTheory.ThetaProjEquiv.ext_shift (R.cV i) (hM.cV i) κ hκ.1 _ hc0 ((R.HV i t).e y) ((R.HV i t).e y) hty h
  have hx : ∀ z, R.extV i t y z = (R.cV i).ext ((R.HV i t).e y) z := fun z => rfl
  have e2 : (R.cV i).ext (levChi (Vc D i) (R.βV i) (R.datVt i t) κ • (R.HV i t).e y) h =
      levChi (Vc D i) (R.βV i) (R.datVt i t) κ • (R.cV i).ext ((R.HV i t).e y) h := by
    exact congrFun (LinearMap.map_smul (R.cV i).ext _ ((R.HV i t).e y)) h
  exact (hx (h * κ)).trans (e1.symm.trans (e2.trans (congrArg (levChi (Vc D i) (R.βV i) (R.datVt i t) κ • ·) (hx h).symm)))

end GlobalTheory.DownLift.TypeLaw

namespace GlobalTheory.DownLift.TypeLaw

theorem alg_step {a b c d d' : ℂ} (hc : c ≠ 0) (hab : a = b) (hd : d' = c * d) : a * d = c⁻¹ * (b * d') := by
  rw [hab, hd, mul_left_comm b c d, inv_mul_cancel_left₀ hc]

theorem downInt_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t), ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ωP i t (κ, 1) f) l g = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * downInt R i t y f l g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y f hf κ hκ l g
  have hM := hG.core.models
  have hc0 : levChi (Vc D i) (R.βV i) (R.datVt i t) κ ≠ 0 := levChi_ne_zero _ κ
  have hFn : ∀ h, l (R.extV i t y (h * κ)) = levChi (Vc D i) (R.βV i) (R.datVt i t) κ * l (R.extV i t y h) := by
    intro h
    exact (congrArg l (extV_type R hM i t y κ hκ h)).trans (l.map_smul _ _)

  have hth : ∀ h, thetaKO (R.ωP i t) h g (R.ωP i t (κ, 1) f) = thetaKO (R.ωP i t) (h * κ) g f := by
    intro h
    have hm : ((h, g) : GA D (Vc D i) × GA D (Wc D i)) * (κ, 1) = (h * κ, g) := by
      rw [Prod.mk_mul_mk, mul_one]
    show R.ωP i t (h, g) (R.ωP i t (κ, 1) f) 0 = R.ωP i t (h * κ, g) f 0
    rw [← hm, map_mul, Module.End.mul_apply]

  let Φ : GA D (Vc D i) → ℂ := fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)
  have hΦ : ∀ γ ∈ GQ (Vc D i), ∀ h, Φ (γ * h) = Φ h := by
    intro γ hγ h
    have ht : thetaKO (R.ωP i t) (γ * h) g f = thetaKO (R.ωP i t) h g f := by
      have hm : ((γ, 1) : GA D (Vc D i) × GA D (Wc D i)) * (h, g) = (γ * h, g) := by
        rw [Prod.mk_mul_mk, one_mul]
      show R.ωP i t (γ * h, g) f 0 = R.ωP i t (h, g) f 0
      rw [← hm, map_mul, Module.End.mul_apply]
      exact (hP i t).datum.om_aut γ hγ 1 (GQ (Wc D i)).one_mem _ ((hP i t).datum.om_pres _ _ hf)
    have hl : l (R.extV i t y (γ * h)) = l (R.extV i t y h) :=
      congrArg l (GlobalTheory.ThetaProjEquiv.extV_left R hM.HV i t y γ hγ h)
    exact congrArg₂ (· * ·) ht hl

  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable (Vc D i)
  have : IsTopologicalGroup (GA D (Vc D i)) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Vc D i).gram))
  have hH : (R.νV i t).IsHaarMeasure := (hM.νV i t).1.1
  have hmap := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup (R.νV i t) _
    (GlobalTheory.ParahoricCompact.isCompact_levG (Vc D i) (R.βV i) (R.datVt i t)) κ hκ
  have hint := setIntegral_mul_right_of_fd (GQ (Vc D i)) (R.νV i t) (R.fdV i t) (hM.νV i t).2 κ hmap Φ hΦ
  have hfun : (fun h => thetaKO (R.ωP i t) h g (R.ωP i t (κ, 1) f) * l (R.extV i t y h)) =
      fun h => (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * Φ (h * κ) := by
    funext h
    exact alg_step hc0 (hth h) (hFn h)
  exact (congrArg (fun φ : GA D (Vc D i) → ℂ => ∫ h in R.fdV i t, φ h ∂(R.νV i t)) hfun).trans
    ((integral_const_mul _ _).trans (congrArg ((levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * ·) hint))

end GlobalTheory.DownLift.TypeLaw
end
end

