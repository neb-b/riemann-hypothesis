module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2798
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2715
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0296

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridRowLevelZeroInfUnitaryEqDatumLevel
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.FunObj

variable {D : D7}

def LocCond (w : Pl D.host.E) (inPg inQ : Prop) (r t : ℕ) {m : ℕ} (g : GL (Fin m) (Kw w)) : Prop :=
  g ∈ KO (Kw w) (Fin m) ∧
    (inPg → (∀ a b : Fin m, Formalism.L2.DIV.blkOf r t b < Formalism.L2.DIV.blkOf r t a → valuation (Kw w) (g.1 a b) < 1) ∧
      ∀ a b : Fin m, a.val < r → b.val < r → valuation (Kw w) ((g.1 - 1) a b) < 1) ∧
    (inQ → ∀ a b : Fin m, Formalism.L2.DIV.blk2 r b < Formalism.L2.DIV.blk2 r a → valuation (Kw w) (g.1 a b) < 1)

theorem inBasis_mem_iff {n m : ℕ} (hm : m = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    (K : Subgroup (GL (Fin m) (Kw w))) (p q : Prop) (r t : ℕ) (hK : ∀ g, g ∈ K ↔ LocCond w p q r t g) :
    inBasis hm β w x ∈ K ↔ LocCond w p q r t (inBasis rfl β w x) := by
  subst hm; exact hK _

theorem upperLeftBlock_eq_one_iff_of_mem_blockTri {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (g : GL (Fin n) κ)
    (hg : g ∈ blockTri (blk2 r)) :
    upperLeftBlock hr g = 1 ↔ ∀ a b : Fin n, a.val < r → b.val < r →
      (g : Matrix (Fin n) (Fin n) κ) a b = (1 : Matrix (Fin n) (Fin n) κ) a b := by
  unfold upperLeftBlock
  rw [extendOne_of_mem _ hg]
  constructor
  · intro h a b ha hb
    have e := congrArg (fun u : GL (Fin r) κ => (u : Matrix (Fin r) (Fin r) κ) ⟨a.val, ha⟩ ⟨b.val, hb⟩) h
    have e2 : (g : Matrix (Fin n) (Fin n) κ) a b = (1 : Matrix (Fin r) (Fin r) κ) ⟨a.val, ha⟩ ⟨b.val, hb⟩ := e
    rw [e2, Matrix.one_apply, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab, if_neg (fun h' => hab (Fin.ext (Fin.mk.inj h')))]
  · intro h
    apply Units.ext
    ext i j
    have e := h (Fin.castLE hr i) (Fin.castLE hr j) i.2 j.2
    show (g : Matrix (Fin n) (Fin n) κ) (Fin.castLE hr i) (Fin.castLE hr j) = (1 : Matrix (Fin r) (Fin r) κ) i j
    rw [e, Matrix.one_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, if_neg (fun h' => hij (Fin.castLE_injective hr h'))]

theorem levelChainTypePlaces_subset_chosenPlaces {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) :
    L.Pg ⊆ G.pl.W0 := by
  classical
  intro PP hP
  obtain ⟨k, hk⟩ := (hL.Pg PP).1 hP
  have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := L.C.P.overP hk
  have hv : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ PP.asIdeal
    simpa using hg
  have hS : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ G.pl.S0 := by
    refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((GlobalTheory.ChiGrid.S1_mem_OmF D).2 ?_))
    fin_cases k
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
  have hw : G.pl.w ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ∈ L.Pg := G.pl.w_g _ k hv
  have he : (G.pl.w ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))).under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := G.pl.under_w hS
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq he with e | e
  · rw [← e]; exact Finset.mem_image_of_mem _ hS
  · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 e) ((GlobalTheory.StepLifts.places_apart L hL t).1 PP hP _ (Or.inl hw))

theorem prodLev_inf_UA {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)}
    (hβ : Lev.IsBaseFrame V β Λ 1) (P : Finset (Pl D.host.E)) {n' : P → ℕ} (hn : ∀ w, n' w = V.rank)
    (K : ∀ w : P, Subgroup (GL (Fin (n' w)) (Kw w.1))) (Ld : LevDat D.host.E ℂ V.rank) (hH : Ld.P.H = ⊥)
    (hPg : Ld.Pg ⊆ P) (hQ : Ld.Q ⊆ P)
    (hK : ∀ w : P, ∀ g, g ∈ K w ↔ LocCond w.1 (w.1 ∈ Ld.Pg) (w.1 ∈ Ld.Q) Ld.r Ld.t g) :
    prodLev β P hn K ⊓ UA D.sp.cm V.gram = lev D.sp.cm V.gram β Ld := by
  have hloc : ∀ (w : P) x, inBasis (hn w) β w.1 x ∈ K w ↔
      LocCond w.1 (w.1 ∈ Ld.Pg) (w.1 ∈ Ld.Q) Ld.r Ld.t (inBasis rfl β w.1 x) :=
    fun w x => inBasis_mem_iff (hn w) β x w.1 (K w) _ _ _ _ (hK w)
  have red0 : ∀ x ∈ St β, ∀ PP (i j : Fin V.rank),
      ((redFn β PP x : GL (Fin V.rank) (kP PP)) : Matrix (Fin V.rank) (Fin V.rank) (kP PP)) i j = 0 ↔
        valuation (Kw PP) ((inBasis rfl β PP x).1 i j) < 1 := by
    intro x hx PP i j
    have e := _root_.GlobalTheory.Adopt.latticeStabilizer_reduction_eq_local_reduction β x PP hx i j 0
    simpa using e
  have red1 : ∀ x ∈ St β, ∀ PP (i j : Fin V.rank),
      ((redFn β PP x : GL (Fin V.rank) (kP PP)) : Matrix (Fin V.rank) (Fin V.rank) (kP PP)) i j =
          (1 : Matrix (Fin V.rank) (Fin V.rank) (kP PP)) i j ↔
        valuation (Kw PP) (((inBasis rfl β PP x).1 - 1) i j) < 1 := by
    intro x hx PP i j
    by_cases hij : i = j
    · subst hij
      have e := _root_.GlobalTheory.Adopt.latticeStabilizer_reduction_eq_local_reduction β x PP hx i i 1
      simpa [Matrix.one_apply] using e
    · have e := _root_.GlobalTheory.Adopt.latticeStabilizer_reduction_eq_local_reduction β x PP hx i j 0
      simpa [Matrix.one_apply, hij] using e
  ext x
  constructor
  · rintro ⟨hx, hU⟩
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hx
    have hA : ∀ w : P, LocCond w.1 (w.1 ∈ Ld.Pg) (w.1 ∈ Ld.Q) Ld.r Ld.t (inBasis rfl β w.1 x) :=
      fun w => (hloc w x).1 (Subgroup.mem_iInf.1 h1 w)
    have hSt : x ∈ St β := _root_.GlobalTheory.Adopt.mem_latticeStabilizer_of_local_integral_inBasis β x fun w => by
      by_cases hw : ∃ w0 ∈ P, w.under (𝓞 D.host.F) = w0.under (𝓞 D.host.F)
      · obtain ⟨w0, hw0, e⟩ := hw
        have hK0 := (hA ⟨w0, hw0⟩).1
        rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e with rfl | rfl
        · exact hK0
        · exact _root_.GlobalTheory.ConjPlaceLev.inBasis_conjPl_mem_KO_of_isBaseFrame V β Λ hβ x hU w0 hK0
      · push_neg at hw
        exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 w) hw
    have hgP : ∀ PP ∈ Ld.Pg, redFn β PP x ∈ blockTri (blkOf Ld.r Ld.t) := fun PP hP => by
      rw [mem_blockTri]
      intro a b hab
      exact (red0 x hSt PP a b).2 (((hA ⟨PP, hPg hP⟩).2.1 hP).1 a b hab)
    refine mem_lev.2 ⟨mem_parLev.2 ⟨hU, hSt, hgP, fun PP hP => ?_⟩, ?_⟩
    · rw [mem_blockTri]
      intro a b hab
      exact (red0 x hSt PP a b).2 ((hA ⟨PP, hQ hP⟩).2.2 hP a b hab)
    · rw [hH, Subgroup.mem_bot]
      funext PP
      show upperLeftBlock Ld.hr (redFn β PP.1 x) = 1
      rw [upperLeftBlock_eq_one_iff_of_mem_blockTri _ _ (blockTri_blkOf_le _ _ (hgP PP.1 PP.2))]
      intro a b ha hb
      exact (red1 x hSt PP.1 a b).2 (((hA ⟨PP.1, hPg PP.2⟩).2.1 PP.2).2 a b ha hb)
  · intro hx
    obtain ⟨hpar, hr⟩ := mem_lev.1 hx
    obtain ⟨hU, hSt, hg, hq⟩ := mem_parLev.1 hpar
    refine ⟨Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => (hloc w x).2 ⟨inBasis_mem_KO β x hSt w.1, fun hw => ⟨?_, ?_⟩,
      fun hw a b hab => (red0 x hSt w.1 a b).1 (mem_blockTri.1 (hq w.1 hw) a b hab)⟩,
      Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => inBasis_mem_KO β x hSt w'⟩, hU⟩
    · intro a b hab
      exact (red0 x hSt w.1 a b).1 (mem_blockTri.1 (hg w.1 hw) a b hab)
    · intro a b ha hb
      rw [hH, Subgroup.mem_bot] at hr
      have e : upperLeftBlock Ld.hr (redFn β w.1 x) = 1 := congrFun hr ⟨w.1, hw⟩
      rw [upperLeftBlock_eq_one_iff_of_mem_blockTri _ _ (blockTri_blkOf_le _ _ (hg w.1 hw))] at e
      exact (red1 x hSt w.1 a b).1 (e a b ha hb)

theorem givenLevel_zero_iff {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E) (k : ℕ)
    (hk : 1 ≤ k) (g : GL (Fin ((locGrid G t w).rank (0, k))) (Kw w)) :
    g ∈ givenLevel G t w (0, k) ↔ g ∈ (stepGroup L t w k).map (reGL (ixFin G t w k)).toMonoidHom := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact Iff.rfl

theorem levRow_zero_eq_lev : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (h : 0 ≤ D.R.m),
    HEq (S.levRow t 0 h ⊓ UA D.sp.cm (G.V (.grid 0 D.R.m)).gram) (lev D.sp.cm D.sp.X'.gram L.βX (L.datXt t)) := by
  intro D T L sc G W U S μ₀ hL t h
  classical
  have hr : D.R.r ≤ (G.V (.grid 0 D.R.m)).rank := by rw [← rank_zero_m G]; exact r_le_X
  have hbase : Lev.IsBaseFrame (G.V (.grid 0 D.R.m)) (S.B.β 0 D.R.m) (G.Λ (.grid 0 D.R.m)) 1 := by
    obtain ⟨c, hc⟩ := hL.βX
    rw [one_pow] at hc
    have key : ∀ (X Y : LSp D) (a : GL (Fin X.sp.rank) (Lev.EAf D)) (b : GL (Fin Y.sp.rank) (Lev.EAf D)),
        X = Y → HEq a b → Lev.IsBaseFrame Y.sp b Y.lat 1 → Lev.IsBaseFrame X.sp a X.lat 1 := by
      rintro X _ a b rfl hab h'
      rwa [eq_of_heq hab]
    exact key _ ⟨D.sp.X', L.ΛX⟩ _ _ (colY_m L) (colFrame_m L) hc
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hdis := (GlobalTheory.StepLifts.places_apart L hL t).2
  have core := prodLev_inf_UA hbase (locPl G t) (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨h, le_rfl⟩)
    (fun w => givenLevel G t w (0, D.R.m))
    (Lev.datY (G.V (.grid 0 D.R.m)).rank D.R.r D.R.t D.R.m hr L.Pg (L.Q t) (LevelP.triv _ _ _) L.chi (L.xiR t) Lev.Frm.B) rfl
    (fun PP hP => Finset.mem_union_left _ (levelChainTypePlaces_subset_chosenPlaces G hL t hP)) (fun PP hP => Finset.mem_union_right _ hP)
    (fun w g => by
      rw [givenLevel_zero_iff G t w.1 D.R.m hm]
      by_cases hP : w.1 ∈ L.Pg
      · have hnq : w.1 ∉ L.Q t := Finset.disjoint_left.1 hdis hP
        rw [_root_.GlobalTheory.Adopt.thetaGridBlockCongruence_typePrime_description G t w.1 hP]
        constructor
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, fun _ => ⟨h2, h3⟩, fun hq => absurd hq hnq⟩
        · rintro ⟨h1, h2, -⟩
          exact ⟨h1, (h2 hP).1, (h2 hP).2⟩
      · rw [_root_.GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description G t w.1 hP]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, fun hp => absurd hp hP, h2⟩
        · rintro ⟨h1, -, h2⟩
          exact ⟨h1, h2⟩)
  have e1 : S.levRow t 0 h = prodLev (S.B.β 0 D.R.m) (locPl G t)
      (fun w => rank_vertex G t w (X := (0, D.R.m)) ⟨h, le_rfl⟩) (fun w => givenLevel G t w (0, D.R.m)) := rfl
  rw [e1, core]
  have key2 : ∀ (X : LSp D), X = ⟨D.sp.X', L.ΛX⟩ → ∀ (b : GL (Fin X.sp.rank) (Lev.EAf D)), HEq b L.βX →
      ∀ (hr : D.R.r ≤ X.sp.rank),
      HEq (lev D.sp.cm X.sp.gram b (Lev.datY X.sp.rank D.R.r D.R.t D.R.m hr L.Pg (L.Q t) (LevelP.triv _ _ _) L.chi (L.xiR t) Lev.Frm.B))
        (lev D.sp.cm D.sp.X'.gram L.βX (L.datXt t)) := by
    rintro X rfl b hb hr
    cases eq_of_heq hb
    rfl
  exact key2 (G.node (.grid 0 D.R.m)) (colY_m L) _ (colFrame_m L) hr

end GlobalTheory.FunObj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceVectorValuedEqFiniteKernelSum
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TraceBlocks

section Assembly
variable {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem trOn_eqvM (ι : H →* G) (hι : Function.Injective ι) (ρ : Representation ℂ H V) (K K' : Subgroup G) (F : G → ℂ)
    (hF : ∀ k ∈ K', ∀ x, F (k * x) = F x ∧ F (x * k) = F x) (hsupp : {q : G ⧸ K' | F q.out ≠ 0}.Finite)
    (hdc : Finite (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G)))
    (hst : ∀ x : G, Finite (ι.range ⊓ K'.map (MulAut.conj x).toMonoidHom : Subgroup G)) :
    trOn (eqvM ι ρ K') (levOp (rightReg ℂ G V) K K' F LinearMap.id) =
      ((K'.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ q : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G),
        ((stabCard ι K' (Quotient.out q) : ℂ))⁻¹ *
          ∑ᶠ h : H, F ((Quotient.out q)⁻¹ * ι h * Quotient.out q) * LinearMap.trace ℂ V (ρ h) := by
  classical
  have hR : ∀ k ∈ K', ∀ x, F (x * k) = F x := fun k hk x => (hF k hk x).2
  have hmaps := _root_.GlobalTheory.BCT.TraceBlocks.levOp_rightReg_mem_eqvM G H V ι ρ K K' F hF
  unfold trOn
  rw [dite_eq_left hmaps]
  haveI : Fintype (DoubleCoset.Quotient (ι.range : Set G) (K' : Set G)) := Fintype.ofFinite _
  set T := levOp (rightReg ℂ G V) K K' F LinearMap.id with hT
  set M := eqvM ι ρ K' with hM
  let x : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G) → G := fun q => Quotient.out q
  let e : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G) → (M →ₗ[ℂ] V) :=
    fun q => (LinearMap.proj (R := ℂ) (φ := fun _ : G => V) (x q)).comp M.subtype
  let s : DoubleCoset.Quotient (ι.range : Set G) (K' : Set G) → (V →ₗ[ℂ] M) :=
    fun q => (secM ι ρ K' (x q)).codRestrict M (fun v => _root_.GlobalTheory.BCT.TraceBlocks.secM_mem_eqvM G H V ι ρ K' (x q) v)
  have hid : ∑ q, s q ∘ₗ e q = LinearMap.id := by
    ext φ : 1
    apply Subtype.ext
    have := _root_.GlobalTheory.BCT.TraceBlocks.eqvM_eq_finsum_secM G H V ι hι ρ K' hdc hst φ.1 φ.2
    rw [finsum_eq_sum_of_fintype] at this
    simpa [s, e, x] using this
  have h1 : ∀ φ : M, φ = ∑ q, s q (e q φ) := fun φ => by
    conv_lhs => rw [← LinearMap.id_apply (R := ℂ) φ, ← hid]
    simp
  haveI : Module.Finite ℂ M := by
    refine Module.Finite.of_injective (LinearMap.pi e) fun a b hab => ?_
    rw [h1 a, h1 b]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show e q a = e q b from congrFun hab q]
  have htr : LinearMap.trace ℂ M (T.restrict hmaps) =
      ∑ q, LinearMap.trace ℂ V (e q ∘ₗ T.restrict hmaps ∘ₗ s q) := by
    have hsum : T.restrict hmaps ∘ₗ (∑ q, s q ∘ₗ e q) = ∑ q, (T.restrict hmaps ∘ₗ s q) ∘ₗ e q := by
      ext φ : 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp [LinearMap.sum_apply, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← LinearMap.comp_id (T.restrict hmaps), ← hid, hsum, map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [LinearMap.trace_comp_comm']
  rw [htr, finsum_eq_sum_of_fintype, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hfin := _root_.GlobalTheory.finite_support_conj_points G H ι hι K' F hR hsupp (x q) (hst _)
  have hsub : ∀ {β : Type} [AddCommMonoid β] (g : H → β), (∀ h, F ((x q)⁻¹ * ι h * x q) = 0 → g h = 0) →
      Function.support g ⊆ hfin.toFinset := fun g hg h hh => by
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    exact fun h0 => hh (hg h h0)
  have hA : e q ∘ₗ T.restrict hmaps ∘ₗ s q = ((K'.relIndex K : ℕ) : ℂ)⁻¹ • ((stabCard ι K' (x q) : ℂ))⁻¹ •
      ∑ h ∈ hfin.toFinset, F ((x q)⁻¹ * ι h * x q) • ρ h := by
    ext v
    have := _root_.GlobalTheory.BCT.TraceBlocks.levOp_secM_apply_self G H V ι hι ρ K K' F hR hsupp (x q) (hst _) hfin v
    rw [finsum_eq_sum_of_support_subset _ (hsub _ fun h h0 => by simp [h0])] at this
    simpa [e, s, LinearMap.restrict_apply, LinearMap.sum_apply] using this
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hA, LinearMap.map_smul, LinearMap.map_smul, map_sum, smul_eq_mul, smul_eq_mul,
    finsum_eq_sum_of_support_subset _ (hsub (fun h => F ((x q)⁻¹ * ι h * x q) * LinearMap.trace ℂ V (ρ h))
      fun h h0 => by simp [h0])]
  simp only [map_smul, smul_eq_mul, x]

end Assembly

end GlobalTheory.BCT.TraceBlocks

namespace GlobalTheory.BCT.TraceBlocks

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem finPtHom_injective : Function.Injective (finPtHom (E := E) (n := n)) := by
  intro a b h
  have h1 : finGL E n (ratF E n a.1) = finGL E n (ratF E n b.1) := by
    have := congrArg (fun k : finU (E := E) (n := n) => (k : UA E n).1) h
    simpa only [finPtHom_apply, FinPtLoc.finPt_eq] using this
  have h2 : ratF E n a.1 = ratF E n b.1 := by
    have := congrArg (GeneralLinearGroup.map (pFin E)) h1
    simpa using this
  obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩⟩
  haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact (algebraMap E (Af E)).injective (congrArg (fun g : GL (Fin n) (Af E) => g.val i j) h2)

theorem finPtHom_range : (finPtHom (E := E) (n := n)).range = ratFinU E n := by
  ext k
  constructor
  · rintro ⟨γ, rfl⟩
    refine ⟨γ.1, γ.2, ?_⟩
    have := FinPtLoc.finPt_eq γ
    exact (congrArg Subtype.val this).symm
  · rintro ⟨g, hg, he⟩
    refine ⟨⟨g, hg⟩, Subtype.ext (Subtype.ext ?_)⟩
    rw [finPtHom_apply, FinPtLoc.finPt_eq]
    exact he

end GlobalTheory.BCT.TraceBlocks


open GlobalTheory.BCT.TraceBlocks in
theorem GlobalTheory.BCT.TrKer.trOn_vecM_hopM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (GlobalTheory.BCT.TrKer.vecM S lam K') (GlobalTheory.BCT.TrKer.hopM S lam K' f) = (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ * ∑ᶠ q : DoubleCoset.Quotient (ratFinU E n : Set (finU (E := E) (n := n))) (globLev S K' : Set (finU (E := E) (n := n))), ((Nat.card (ratFinU E n ⊓ (globLev S K').map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup (finU (E := E) (n := n))) : ℂ))⁻¹ * ∑ᶠ γ : UE E n, globFn S f ((Quotient.out q)⁻¹ * finPt γ * Quotient.out q) * LinearMap.trace ℂ _ (GlobalTheory.BCT.TrKer.wAt lam γ⁻¹) := by
  intro E _ _ _ hU n _ S hS lam K' hK f hf
  have hV : GlobalTheory.BCT.TrKer.vecM S lam K' = eqvM finPtHom (wDual lam) (globLev S K') := rfl
  have hT : GlobalTheory.BCT.TrKer.hopM S lam K' f =
      levOp (rightReg ℂ (finU (E := E) (n := n)) (Module.Dual ℂ (GlobalTheory.BCT.TrKer.Wsp lam))) (globLev S (KL n)) (globLev S K')
        (globFn S f) LinearMap.id := rfl
  have hF := globFn_inv S K' f fun w => (hf.1 w).2
  have hdc : Finite (DoubleCoset.Quotient ((finPtHom (E := E) (n := n)).range : Set (finU (E := E) (n := n)))
      (globLev S K' : Set (finU (E := E) (n := n)))) := by
    rw [finPtHom_range]
    exact GlobalTheory.T.finite_doubleCoset_definiteUnitaryRational_of_isOpen E n _ (GlobalTheory.T.isOpen_productOfLocalLevelsUnitary E hU n S K' hK)
  have hst : ∀ x : finU (E := E) (n := n), Finite ((finPtHom (E := E) (n := n)).range ⊓
      (globLev S K').map (MulAut.conj x).toMonoidHom : Subgroup (finU (E := E) (n := n))) := fun x => by
    rw [finPtHom_range]
    exact GlobalTheory.T.finite_definiteUnitary_rational_inf_conj_level E hU n S hS K' hK x
  rw [hV, hT, trOn_eqvM finPtHom finPtHom_injective (wDual lam) _ _ _ hF (GlobalTheory.T.finite_productOfLocalFunctionsUnitary_ne_zero E hU n S K' hK f hf) hdc hst]
  have htr : ∀ γ : UE E n, LinearMap.trace ℂ _ (wDual lam γ) = LinearMap.trace ℂ _ (GlobalTheory.BCT.TrKer.wAt lam γ⁻¹) :=
    fun γ => LinearMap.trace_transpose' _
  simp only [htr, finPtHom_apply, stabCard]
  rw [finPtHom_range]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealDescentThetaModelToComponentTraitOrders
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.PoincDown

theorem exists_assoc_pow {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (f : V →+* V') (hf : Function.Injective f) [IsLocalHom f] {ϖ : V} (hϖ : Irreducible ϖ)
    {ϖ' : V'} (hϖ' : Irreducible ϖ') : ∃ m : ℕ, 1 ≤ m ∧ Associated (f ϖ) (ϖ' ^ m) := by
  have h0 : f ϖ ≠ 0 := fun h => hϖ.ne_zero (hf (by rw [h, map_zero]))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible h0 hϖ'
  refine ⟨m, Nat.one_le_iff_ne_zero.2 fun e => ?_, hm⟩
  subst e
  rw [pow_zero] at hm
  exact hϖ.not_isUnit ((isUnit_map_iff f ϖ).1 (associated_one_iff_isUnit.1 hm))

theorem map_eq_span_pow {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V'] [IsDomain V']
    [IsDiscreteValuationRing V'] (f : V →+* V') {ϖ : V} (hϖ : Irreducible ϖ) {ϖ' : V'} (hϖ' : Irreducible ϖ') {m : ℕ}
    (hm : Associated (f ϖ) (ϖ' ^ m)) {I : Ideal V} {b : ℕ} (h : I.map f = Ideal.span {ϖ' ^ b}) :
    ∃ a : ℕ, b = m * a ∧ I = Ideal.span {ϖ ^ a} := by
  have hI : I ≠ ⊥ := by
    rintro rfl
    rw [Ideal.map_bot, eq_comm, Ideal.span_singleton_eq_bot] at h
    exact pow_ne_zero _ hϖ'.ne_zero h
  obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hI hϖ
  refine ⟨a, ?_, rfl⟩
  rw [Ideal.map_span, Set.image_singleton, map_pow, Ideal.span_singleton_eq_span_singleton] at h
  have h2 : Associated (ϖ' ^ (m * a)) (ϖ' ^ b) := by
    rw [pow_mul]; exact (hm.pow_pow (n := a)).symm.trans h
  have e1 := (pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 h2.dvd
  have e2 := (pow_dvd_pow_iff hϖ'.ne_zero hϖ'.not_isUnit).1 h2.symm.dvd
  omega

theorem idealDescent : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (d : ℕ) (J : Z.IdealSheafData), 1 ≤ d ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ W → ∃ a : ℕ, (a : ℝ) = d * φ.evalZ T.β ∧ idlAlong J ξ = Ideal.span {T.ϖ ^ a} := by
  intro g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord
  obtain ⟨k, J, hk, hJs, hJo⟩ := _root_.GlobalTheory.NormDown.normDescent g n hg hn hodd F Z z i hZ φ hφ W hWc hWi W8 X₁ ι J₁ hι hπ hsupp hord
  refine ⟨k * ι, J, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), hJs, ?_⟩
  intro T ξ hξ hW
  have hc : IsClopen (Set.range X₁.π) := by rw [hπ]; exact hWc
  obtain ⟨T', f, fK, ξ₁, hf, hfl, hfK, hy, hsq, hgen⟩ := _root_.GlobalTheory.Poinc.traitLift_setup g n F Z i W8 X₁ hc T ξ hξ (by rw [hπ]; exact hW)
  obtain ⟨a₁, ha₁, hJ₁⟩ := hord T' ξ₁ hgen
  have hJ := hJo T' ξ₁ hgen
  obtain ⟨m, hm1, hm⟩ := exists_assoc_pow f hf T.irr T'.irr
  have hφ' := GlobalTheory.Poinc.TraitRam.evalZ_eq_mul g n _ _ (by omega) (cycBase (show n ≠ 0 by omega)).ζ.isUnit F T T' f fK hf hfl hfK hy m hm φ hφ
  have e1 : (idlAlong J ξ).map f = Ideal.span {T'.ϖ ^ (a₁ * k)} := by
    rw [← GlobalTheory.TraitOrder.idlAlong_comp, hsq, hJ, hJ₁, Ideal.span_singleton_pow, ← pow_mul]
  obtain ⟨a, hb, ha⟩ := map_eq_span_pow f T.irr T'.irr hm e1
  refine ⟨a, ?_, ha⟩
  have hb' : ((a₁ : ℝ) * k) = m * a := by exact_mod_cast hb
  rw [ha₁, hφ'] at hb'
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  push_cast
  apply mul_left_cancel₀ hm0.ne'
  linarith [hb']

end GlobalTheory.PoincDown
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestRest
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

namespace GlobalTheory.TopFlip.MeasW

theorem nu_eq {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {t t' : T} {M M' : Vol G}
    (hM : M.Is t) (hM' : M'.Is t') (i j : Fin D.R.m) :
    M.ν (.grid (i + 1) (j + 1)) = M'.ν (.grid (i + 1) (j + 1)) :=
  GlobalTheory.FunObjModel.isAt_unique (hM.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩) (hM'.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩)

theorem exists_ratio : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (i j : Fin D.R.m) (m : Measure (GA D (spW G i j))), m.IsHaarMeasure →
      ∃ s₀ : NNReal, s₀ ≠ 0 ∧ ∀ (t : T) (M : Vol G), M.Is t → ∀ s : NNReal, M.ν (.grid (i + 1) (j + 1)) = s • m → s = s₀ := by
  intro D T L sc G μ₀ _ i j m hm
  by_cases h : ∃ (t : T) (M : Vol G) (s : NNReal), M.Is t ∧ M.ν (.grid (i + 1) (j + 1)) = s • m
  · obtain ⟨t₀, M₀, s₀, hM₀, e₀⟩ := h
    have hH := (hM₀.vtx (.grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).haar_fund.1
    obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (spW G i j)
    obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (GA D (spW G i j))) := inferInstance
    have hK0 : m K ≠ 0 :=
      ((isOpen_interior.measure_pos m K.interior_nonempty).trans_le (measure_mono interior_subset)).ne'
    have hK1 : m K ≠ ⊤ := K.isCompact.measure_lt_top.ne
    refine ⟨s₀, ?_, fun t M hM s e => ?_⟩
    · rintro rfl
      rw [e₀, zero_smul] at hH
      exact (isOpen_univ.measure_pos (0 : Measure (GA D (spW G i j))) Set.univ_nonempty).ne' rfl
    · have e1 : s • m = s₀ • m := e.symm.trans ((nu_eq hM hM₀ i j).trans e₀)
      have e2 : (s : ENNReal) * m K = (s₀ : ENNReal) * m K := by
        have e3 := congrArg (fun μ : Measure (GA D (spW G i j)) => μ K) e1
        exact e3
      exact_mod_cast (ENNReal.mul_left_inj hK0 hK1).1 e2
  · exact ⟨1, one_ne_zero, fun t M hM s e => absurd ⟨t, M, s, hM, e⟩ h⟩

end GlobalTheory.TopFlip.MeasW

end
end

