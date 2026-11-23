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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0494
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1673
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorValuedLiftFieldChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0500
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0497
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0489

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseReadingZeroWithoutEvaluationProperty
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.EvZero

open GlobalTheory.Mem.R3.Rw.GeoTies

def NoEvAtOne {D : D7} (T : CoreJ D) (j : ℕ) (w : WeightFamilies.Wt D j) (s : T.Q.c.F →+* ℂ) {W : HSp D} {S : D.what₂.Tau → SPar}
    (M : DSModel W S) (Hm : Links.HMod (MMap M)) (v : M.Vec) {L : Type} [Field L] (σ : L →+* ℂ) {n : ℕ}
    (c : T.cuspA j (wtA w) w.n → Fin n → L) (Z : Prop) : Prop :=
  GoodEmb T.Q.c s → ∀ hV : T.V j s = W,
    (¬ ∃ j' : (Fin n → L) →ₛₗ[σ] Hm.H, ∀ f : T.cuspA j (wtA w) w.n,
      Hm.e (j' (c f)) v = phiC T hV (wtA w) (f : T.R j)) → Z

theorem exists_extend {L L' : Type} [Field L] [Field L'] (ι : L →+* L') (σ' : L' →+* ℂ) {n : ℕ}
    {A : Type} [AddCommGroup A] [Module ℂ A] (j : (Fin n → L) →ₛₗ[σ'.comp ι] A) :
    ∃ j' : (Fin n → L') →ₛₗ[σ'] A, ∀ x x', CrdOver ι x x' → j' x' = j x := by
  refine ⟨{ toFun := fun x' => ∑ k, σ' (x' k) • j (Pi.single k 1), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    simp only [Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]
  · intro a x
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, Finset.smul_sum]
  · intro x x' h
    change ∑ k, σ' (x' k) • j (Pi.single k 1) = j x
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [pi_eq_sum_univ' x, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smulₛₗ, h.2 k k rfl]
    rfl

theorem NoEvAtOne.congr {D : D7} (T T' : CoreJ D) (h1 : HEq T'.Q.H T.Q.H) (h2 : HEq T'.Q.l T.Q.l) (h3 : HEq T'.Q.c T.Q.c)
    (h4 : HEq T'.Q.Dw T.Q.Dw) (h5 : HEq T'.Q.Xo T.Q.Xo) (h6 : HEq T'.U T.U) (h7 : HEq T'.V T.V) (h8 : HEq T'.dict T.dict)
    (h9 : HEq T'.mu T.mu) (h10 : HEq T'.cE T.cE) (j : ℕ) (w w' : WeightFamilies.Wt D j) (hP : HEq w'.aP w.aP) (hM : HEq w'.aM w.aM)
    (hn : w'.n = w.n) (s : T.Q.c.F →+* ℂ) (s' : T'.Q.c.F →+* ℂ)
    (hs : ∀ (y : T.Q.c.F) (y' : T'.Q.c.F), (y' : ℂ) = (y : ℂ) → s' y' = s y)
    {W : HSp D} {S S' : D.what₂.Tau → SPar} (M : DSModel W S) (M' : DSModel W S') (hMM : ModelSame M M')
    (Hm : Links.HMod (MMap M)) (Hm' : Links.HMod (MMap M')) (hH : HEq Hm' Hm) (v : M.Vec) (v' : M'.Vec) (hv : HEq v' v)
    {L L' : Type} [Field L] [Field L'] (ι : L →+* L') (σ' : L' →+* ℂ) {n n' : ℕ} (hnn : n = n')
    (c : T.cuspA j (wtA w) w.n → Fin n → L) (c' : T'.cuspA j (wtA w') w'.n → Fin n' → L')
    (hc : ∀ f f', HEq f' f → CrdOver ι (c f) (c' f')) {Z Z' : Prop} (hZ : Z → Z') :
    NoEvAtOne T j w s M Hm v (σ'.comp ι) c Z → NoEvAtOne T' j w' s' M' Hm' v' σ' c' Z' := by
  obtain ⟨⟨⟨H, l, cc, Dw, Xo, eO⟩, U, V, dict, mu, Kf, pb⟩, cE, chiW, x₀, iota⟩ := T
  obtain ⟨⟨⟨H', l', cc', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := T'
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases h6
  cases h7
  cases h8
  cases h9
  cases h10
  obtain ⟨aP, aM, _, _, m, _⟩ := w
  obtain ⟨aP', aM', _, _, m', _⟩ := w'
  dsimp only at hP hM hn
  cases hP
  cases hM
  cases hn
  have hs' : s' = s := RingHom.ext fun y => hs y y rfl
  subst hs'
  obtain ⟨X, σ, lam, ε, fr, _, _, _, _⟩ := M
  obtain ⟨X', σ'', lam', ε', fr', _, _, _, _⟩ := M'
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := hMM
  dsimp only at m1 m2 m3 m4 m5 m6 m7
  cases m1
  cases m2
  cases m3
  cases m4
  cases m5
  cases m6
  cases m7
  have hH' : Hm' = Hm := eq_of_heq hH
  subst hH'
  have hv' : v' = v := eq_of_heq hv
  subst hv'
  subst hnn
  intro h hg hV hno
  refine hZ (h hg hV ?_)
  rintro ⟨j₀, hj₀⟩
  obtain ⟨j', hj'⟩ := exists_extend ι σ' j₀
  exact hno ⟨j', fun f => by rw [hj' _ _ (hc f f HEq.rfl)]; exact hj₀ f⟩

def intEquivOfEq {F F' : IntermediateField ℚ ℂ} (h : F' = F) : 𝓞 F ≃+* 𝓞 F' := by
  subst h
  exact RingEquiv.refl _

theorem coeff_field_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {l' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H'}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l'}
    (h1 : HEq H' H) (h2 : HEq l' l) (h3 : HEq c' c) : c'.F = c.F := by
  cases h1
  cases h2
  cases h3
  rfl

theorem enlargedBase_reading_zero_without_evaluationProperty : ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
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
      ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
          HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
      ∀ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ σ' : (w'.st Z').toD7.what₂.LL →+* ℂ,
          HEq (v₀' i' σ') (z.geo.v₀ i (σ'.comp ι))) →
      ∀ (e' : ∀ i : Fin (w'.st Z').toD7.R.m, core'.cuspA ((i : ℕ) + 1) (wtA (κ' i)) (κ' i).n ≃ₗ[core'.Q.c.F] (R'.FW i).WK),
        (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
          CrdOver ι (z.geo.fw.e i φ : (z.R.FW i).WK).1 (e' i' φ' : (R'.FW i').WK).1) →
      ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), Formalism.L2.Pj.GoodEmb core'.Q.c (σ.comp (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL)) →
        ∀ hV : core'.V ((i : ℕ) + 1) (σ.comp (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL)) = Wc (w'.st Z').toD7 i,
        (¬ ∃ j' : (Fin (R'.nW i) → (w'.st Z').toD7.what₂.LL) →ₛₗ[σ] (R'.HW i σ).H, ∀ f : core'.cuspA ((i : ℕ) + 1) (wtA (κ' i)) (κ' i).n,
          ((R'.HW i σ).e (j' ((e' i f : (R'.FW i).WK) : Fin (R'.nW i) → (w'.st Z').toD7.what₂.LL))) (v₀' i σ) =
            hV ▸ core'.phiJ ((i : ℕ) + 1) (σ.comp (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL)) (wtA (κ' i)) (f : core'.R ((i : ℕ) + 1))) →
        (R'.FW i).j σ = 0 := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hc _ Xg tr R' hRS _ ι hι κ' hκ v₀' hv e' he i' σ'
  letI := alg'
  letI := z.alg
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := (by with_unfolding_all exact ((congrArg (fun P : Pre => P.R.m) hPre) :))
  let i : Fin (w.st Z).toD7.R.m := ⟨i'.1, hm ▸ i'.2⟩
  have hi : (i : ℕ) = i' := rfl
  have hb : NoEvAtOne z.core ((i : ℕ) + 1) (z.geo.κ i) (res z.core (σ'.comp ι)) (z.R.MW i (σ'.comp ι)) (z.R.HW i (σ'.comp ι))
      (z.geo.v₀ i (σ'.comp ι)) (σ'.comp ι) (fun φ => (z.geo.fw.e i φ : (z.R.FW i).WK).1) ((z.R.FW i).j (σ'.comp ι) = 0) :=
    z.geo.fw.ev0 i (σ'.comp ι)
  have hnW := hRS.2.2.2.2.2.1
  have hcl := ((hRS.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).1 σ'
  have hMM : ModelSame (z.R.MW i (σ'.comp ι)) (R'.MW i' σ') :=
    ⟨hcl.1.1, hcl.1.2.1, hcl.1.2.2.1, hcl.1.2.2.2.1, hcl.1.2.2.2.2.1, hcl.1.2.2.2.2.2.1, hcl.1.2.2.2.2.2.2.1⟩
  have hH := hcl.2.1
  have hjj := hcl.2.2.2
  have hs : ∀ (y : z.core.Q.c.F) (y' : core'.Q.c.F), (y' : ℂ) = (y : ℂ) →
      res core' σ' y' = res z.core (σ'.comp ι) y := fun y y' hy =>
    congrArg σ' ((w'.st Z').toD7.what₂.embLL.injective
      (((by with_unfolding_all exact ((halg y') :)) : (w'.st Z').toD7.what₂.embLL (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y') = (y' : ℂ)).trans
        (hy.trans ((hι _).trans ((by with_unfolding_all exact ((z.alg_eq y) :)) :
          (w.st Z).toD7.what₂.embLL (algebraMap z.core.Q.c.F (w.st Z).toD7.what₂.LL y) = (y : ℂ))).symm)))
  have hgen : ∀ {m m' : ℕ} (_ : m' = m) (a : Fin m → ℕ) (a' : Fin m' → ℕ), HEq a' a → ∀ (k : Fin m) (k' : Fin m'),
      (k : ℕ) = k' → a k = a' k' := by
    intro m m' h a a' ha k k' hk
    subst h
    cases ha
    rw [Fin.ext hk]
  have hn : z.R.nW i = R'.nW i' := hgen hm _ _ hnW i i' hi
  have hZ : (z.R.FW i).j (σ'.comp ι) = 0 → (R'.FW i').j σ' = 0 := reading_eq_zero ι σ' hn _ _ hjj
  have hv1 := hv i i' hi σ'
  have he1 := he i i' hi
  obtain ⟨hP, hM, hnn⟩ := hκ i i' hi
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, -, c10, -⟩ := hc
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  let H₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host (w'.st Z').toD7.host.E := (by with_unfolding_all exact (z.core.Q.H :))
  let l₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₁ := (by with_unfolding_all exact (z.core.Q.l :))
  let c₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₁ := (by with_unfolding_all exact (z.core.Q.c :))
  have hF : core'.Q.c.F = c₁.F := coeff_field_eq (H := H₁) (l := l₁) (c := c₁) ((by with_unfolding_all exact (c1 :))) ((by with_unfolding_all exact (c2 :))) ((by with_unfolding_all exact (c3 :)))
  let Q₀ : Formalism.L2.Pj.Par (w'.st Z').toD7 :=
    { H := H₁, l := l₁, c := c₁, Dw := (by with_unfolding_all exact (z.core.Q.Dw :)), Xo := (by with_unfolding_all exact (z.core.Q.Xo :)),
      eO := (intEquivOfEq hF).trans core'.Q.eO }
  let core₀ : Formalism.L2.Pj.CoreJ (w'.st Z').toD7 :=
    { toCore :=
        { Q := Q₀, U := (by with_unfolding_all exact (z.core.U :)), V := (by with_unfolding_all exact (z.core.V :)), dict := (by with_unfolding_all exact (z.core.dict :)), mu := (by with_unfolding_all exact (z.core.mu :)),
          Kf := (by with_unfolding_all exact (z.core.Kf :)), pb := (by with_unfolding_all exact (z.core.pb :)) }
      cE := (by with_unfolding_all exact (z.core.cE :)), chiW := (by with_unfolding_all exact (z.core.chiW :)), x₀ := (by with_unfolding_all exact (z.core.x₀ :)), iota := (by with_unfolding_all exact (z.core.iota :)) }
  let κ₀ : WeightFamilies.Wt (w'.st Z').toD7 ((i' : ℕ) + 1) :=
    { aP := (by with_unfolding_all exact ((z.geo.κ i).aP :)), aM := (by with_unfolding_all exact ((z.geo.κ i).aM :)), aPlus_antitone := (by with_unfolding_all exact ((z.geo.κ i).aPlus_antitone :)),
      aM_anti := (by with_unfolding_all exact ((z.geo.κ i).aM_anti :)), n := (z.geo.κ i).n, n_even := (z.geo.κ i).n_even }
  let S₀ : (w'.st Z').toD7.what₂.Tau → SPar := (by with_unfolding_all exact ((parAt (Wc (w.st Z).toD7 i) (σ'.comp ι)) :))
  let M₀ : DSModel (Wc (w'.st Z').toD7 i') S₀ :=
    @DSModel.mk _ _ _ ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).H :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).nacg :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ips :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).σ :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).lam :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ε :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).enum :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).ds :)))
      ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr_unit :))) ((by with_unfolding_all exact ((z.R.MW i (σ'.comp ι)).fr_gram :)))
  let H₀ : Links.HMod (MMap M₀) := (by with_unfolding_all exact ((z.R.HW i (σ'.comp ι)) :))
  let u₀ : M₀.Vec := (by with_unfolding_all exact ((z.geo.v₀ i (σ'.comp ι)) :))
  let s₀ : core₀.Q.c.F →+* ℂ := (by with_unfolding_all exact ((res z.core (σ'.comp ι)) :))
  let c₀ : core₀.cuspA ((i' : ℕ) + 1) (wtA κ₀) κ₀.n → Fin (z.R.nW i) → (w.st Z).toD7.what₂.LL :=
    (by with_unfolding_all exact ((fun φ => (z.geo.fw.e i φ : (z.R.FW i).WK).1) :))
  exact (by with_unfolding_all exact ((NoEvAtOne.congr core₀ core' ((c1)) ((c2)) ((c3)) ((c4)) ((c5)) ((c6)) ((c7)) ((c8)) ((c9)) ((c10))
    ((i' : ℕ) + 1) κ₀ (κ' i') ((hP)) ((hM)) ((hnn)) s₀ (res core' σ') ((hs)) M₀ (R'.MW i' σ') ((hMM))
    H₀ (R'.HW i' σ') ((hH)) u₀ (v₀' i' σ') ((hv1)) ι σ' hn c₀ (fun φ => (e' i' φ : (R'.FW i').WK).1) ((he1)) hZ ((hb))) : _))

end GlobalTheory.Mem.R3.Rw.EvZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBcStages
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.Mem GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.RealGeo GlobalTheory.OneMapAll GlobalTheory.FieldBC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmExt

theorem levOver_cast' {D : D7} {G : Type} [Group G] {i : Fin D.R.m} {Pg₁ Pg₂ : Finset (Formalism.L2.DIV.Pl D.host.E)}
    {β₁ β₂ : ∀ i, GL (Fin (Wc D i).rank) (Lev.EAf D)} {e₁ : G ≃* G0 Pg₁ D.R.r} {e₂ : G ≃* G0 Pg₂ D.R.r}
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Dw : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H}
    {ι : ∀ j : ℕ, (Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)} (hP : HEq Pg₂ Pg₁) (hβ : HEq β₂ β₁) (he : HEq e₂ e₁)
    {lev : G → (Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Dw ((i : ℕ) + 1)).La} (h : LevOver D i Pg₁ β₁ e₁ l Dw ι lev) :
    LevOver D i Pg₂ β₂ e₂ l Dw ι lev := by
  cases hP; cases hβ; cases he
  exact h


set_option maxHeartbeats 4000000 in
theorem exists_bc_stages (X X' : Stages) (hP : X'.B.toPre = X.B.toPre) (hLL : Set.range X.B.embLL ⊆ Set.range X'.B.embLL)
    {G : Type} [Group G] [Fintype G] {Pl0 T0 Pl0' T0' : Type} {A : FamIn X.toD7.what₂.LL G Pl0 T0 X.toD7.R.m}
    {A' : FamIn X'.toD7.what₂.LL G Pl0' T0' X'.toD7.R.m} (T : CoreJ X.toD7) [Algebra T.Q.c.F X.toD7.what₂.LL]
    (T' : CoreJ X'.toD7) [alg' : Algebra T'.Q.c.F X'.toD7.what₂.LL] (R : RealDat X.toD7 A T.Q.c.F) (R' : RealDat X'.toD7 A' T'.Q.c.F)
    (eH : HEq T'.Q.H T.Q.H) (el : HEq T'.Q.l T.Q.l) (ec : HEq T'.Q.c T.Q.c) (eD : HEq T'.Q.Dw T.Q.Dw) (eX : HEq T'.Q.Xo T.Q.Xo)
    (ex : HEq T'.x₀ T.x₀) (eι : HEq T'.iota T.iota) (ePg : HEq R'.Pg R.Pg) (eβV : HEq R'.βV R.βV) (eβW : HEq R'.βW R.βW)
    (eG : HEq R'.eG R.eG) (emu : HEq R'.C.mu0 R.C.mu0) (eeta : HEq R'.C.eta R.C.eta)
    {κ : ∀ i : Fin X.toD7.R.m, WeightFamilies.Wt X.toD7 ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin X.toD7.R.m) (σ : X.toD7.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    {κ' : ∀ i : Fin X'.toD7.R.m, WeightFamilies.Wt X'.toD7 ((i : ℕ) + 1)}
    {v₀' : ∀ (i : Fin X'.toD7.R.m) (σ : X'.toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec}
    (hL : R.toLevCh.Is A.μ0) (hV : R.models_HV) (hκ : KapIs κ) (hL' : R'.toLevCh.Is A'.μ0) (hM' : R'.IsModels) (hF' : R'.fam_tie)
    (ht' : TieIn T' R' κ' v₀') (i : Fin X.toD7.R.m) (i' : Fin X'.toD7.R.m) (hi : (i : ℕ) = i')
    (eW : HEq (R'.cV i').W (R.cV i).W) (en : HEq (R'.cV i').nW (R.cV i).nW) (ei : HEq (R'.cV i').iW (R.cV i).iW)
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (hOF : O.c'.F = X.toD7.what₂.embLL.toRatAlgHom.fieldRange)
    (hO : O.Pins (κ i) (v₀ i (sg0 X.toD7 A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) (P : Prop)
    (hc : ∀ c0L, CoefFam R c0L → P ∨ ∃ c0L', CoefFam R' c0L' ∧
      ∀ (v : VsV X.toD7 i X.toD7.what₂.LL) (v' : VsV X'.toD7 i' X'.toD7.what₂.LL),
        HEq (MvPolynomial.map X'.toD7.what₂.embLL v'.1) (MvPolynomial.map X.toD7.what₂.embLL v.1) → HEq (c0L' i' v') (c0L i v)) :
    ∃ O' : OMDat T'.toCore R' i' Unit (fun _ => A'.μ0), O'.c'.F = X'.toD7.what₂.embLL.toRatAlgHom.fieldRange ∧
      O'.Pins (κ' i') (v₀' i' (sg0 X'.toD7 A')) (iotaW T' i') (T'.x₀ ((i' : ℕ) + 1) O'.s0) ∧
      IsBCOf O' (v₀' i' (sg0 X'.toD7 A')) O (v₀ i (sg0 X.toD7 A)) (κ i) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) P := by
  obtain ⟨c₃, hF₃, h₃⟩ := GlobalTheory.RefPins.exists_coeff_rows T' ht'.alg ht'.laws.pins.2.2.1
  have hmem : ∀ y, X'.toD7.what₂.embLL y ∈ c₃.F := fun y => hF₃.ge ⟨y, rfl⟩
  let jL' : X'.toD7.what₂.LL →+* c₃.F := X'.toD7.what₂.embLL.codRestrict c₃.F hmem
  have hjL' : (inC c₃).comp jL' = X'.toD7.what₂.embLL := RingHom.ext fun _ => rfl
  have sj' : Function.Surjective jL' := fun y => by
    obtain ⟨x, hx⟩ := hF₃.le y.2
    exact ⟨x, Subtype.ext hx⟩
  have sj : Function.Surjective O.jL := fun y => by
    obtain ⟨x, hx⟩ := hOF.le y.2
    exact ⟨x, Subtype.ext ((RingHom.congr_fun hO.lift.field x).trans hx)⟩
  have hs : O.c'.F ≤ c₃.F := fun y hy => by
    obtain ⟨x, hx⟩ := hOF.le hy
    obtain ⟨x', hx'⟩ := hLL ⟨x, hx⟩
    exact hF₃.ge ⟨x', hx'⟩
  have hQ := GlobalTheory.RefPins.places_ref R hL
  have hQ' := GlobalTheory.RefPins.places_ref R' hL'
  have hV₃ : T'.V ((i' : ℕ) + 1) (sOv T'.toCore c₃ h₃) = Wc X'.toD7 i' := ht'.laws.spaceW _ (inR i') _ rfl
  obtain ⟨g, r, c0L, hT, hbc⟩ := hO.lift.c0
  have hx1 := hL.xi A.μ0
  have hx1' := hL'.xi A'.μ0
  rw [hL.xi_base] at hx1
  rw [hL'.xi_base] at hx1'
  have hplace : ∀ (c0L') (c0'' : VsV X'.toD7 i' c₃.F →ₛₗ[inC c₃] (R'.cV i').W), CoefFam R' c0L' →
      CoefficientBaseChange R' i' jL' (inC c₃) (c0L' i') c0'' → ∀ (Cl : Type) [Fintype Cl] (h : Cl → GA X'.toD7 (Vc X'.toD7 i')),
      PlaceEx R' i' A'.μ0 h c0'' := by
    rintro c0L' c0'' ⟨_, _, htie⟩ hc0 Cl _ h
    exact GlobalTheory.RationalValues.placeEx_of_type_mem R' i' jL' (inC c₃) A'.μ0 h c0'' hM'.jV htie hc0
      (GlobalTheory.RationalValues.type_mem R' i' A'.μ0 _
        (fun PP hPP x => by
          obtain ⟨y, hy⟩ := GlobalTheory.RefPins.chiVal_of_tie T' R' κ' v₀' hL' ht' i' PP hPP x
          exact ⟨jL' y, hy⟩)
        fun PP hPP => absurd (hQ' ▸ hPP) (Finset.notMem_empty _))
  have hv0' := ht'.hv₀ i' (sg0 X'.toD7 A')
  have hκ' := ht'.kap i'
  clear ht'
  have hc' : ∃ c0L', CoefFam R' c0L' ∧ (P ∨ ∀ (v : VsV X.toD7 i X.toD7.what₂.LL) (v' : VsV X'.toD7 i' X'.toD7.what₂.LL),
        HEq (MvPolynomial.map X'.toD7.what₂.embLL v'.1) (MvPolynomial.map X.toD7.what₂.embLL v.1) → HEq (c0L' i' v') (c0L i v)) := by
    rcases hc c0L ⟨g, r, hT⟩ with h | ⟨c, h1, h2⟩
    · obtain ⟨g', r', c, h1⟩ := hF'
      exact ⟨c, ⟨g', r', h1⟩, Or.inl h⟩
    · exact ⟨c, h1, Or.inr h2⟩
  clear hc
  obtain ⟨c0L', hT', hag⟩ := hc'
  obtain ⟨c0'', hbc'⟩ := GlobalTheory.Mem.PlaceVal.exists_ext_VV (W := (R'.cV i').W) jL' (inC c₃) hjL' (lamV X'.toD7 i') (c0L' i')
  have hpl' := hplace c0L' c0'' hT' hbc'
  clear hplace
  obtain ⟨B', C', W', V', S', N', G'⟩ := X'
  rcases B' with ⟨P'⟩
  change P' = X.B.toPre at hP
  subst hP
  obtain ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V'', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := T'
  dsimp only at eH el ec eD eX ex eι
  obtain rfl := eq_of_heq eH
  obtain rfl := eq_of_heq el
  obtain rfl := eq_of_heq ec
  obtain rfl := eq_of_heq eD
  obtain rfl := eq_of_heq eX
  obtain rfl := eq_of_heq ex
  obtain rfl := eq_of_heq eι
  obtain rfl : i = i' := Fin.ext hi
  have h0 : ∃ c0₃ : VsV X.toD7 i c₃.F →ₛₗ[inC c₃] (R.cV i).W, (∀ (v : VsV X.toD7 i O.c'.F) (v' : VsV X.toD7 i c₃.F),
      (v' : Pol c₃.F X.toD7.what₂.Tau (Vc X.toD7 i).rank) =
        MvPolynomial.map (incF O.c' c₃ hs) (v : Pol O.c'.F X.toD7.what₂.Tau (Vc X.toD7 i).rank) → c0₃ v' = O.c0' v) ∧
      (HEq c0'' c0₃ ∨ P) := by
    rcases hag with hp | hag
    · obtain ⟨c0₃, h⟩ := exists_coef_ext (incF O.c' c₃ hs) (σ := inC O.c') (inC c₃) (fun _ => rfl) (lamV X.toD7 i) O.c0'
      exact ⟨c0₃, h, Or.inr hp⟩
    · obtain ⟨c0₃, h1, h2⟩ := exists_cast_map (V := VsV X.toD7 i c₃.F) (σ := inC c₃) (R.cV i).nW (R.cV i).iW (R'.cV i).nW (R'.cV i).iW
        eW en ei ((by with_unfolding_all exact (c0'' :)))
      refine ⟨c0₃, fun v v' e => eq_of_heq ((h2 v').symm.trans ?_), Or.inl ((by with_unfolding_all exact (h1 :)))⟩
      exact coef_agree (W' := (R'.cV i).W) (lamV X.toD7 i) O.jL jL' (incF O.c' c₃ hs) hO.lift.field hjL' (RingHom.ext fun _ => rfl) sj sj'
        (cL' := (by with_unfolding_all exact ((c0L' i) :))) hbc ((by with_unfolding_all exact (hbc' :))) ((by with_unfolding_all exact (hag :))) v v' e
  obtain ⟨c0₃, hc0, hor⟩ := h0
  obtain ⟨io₃, hw₃, h, J', hB⟩ := exists_isBC O c₃ hs c0₃ (v₀ i (sg0 X.toD7 A)) hV hO hc0
  have hM := hB.pins
  have eχ : R'.C.mu0 i * R'.xiH A'.μ0 * R'.C.eta⁻¹ = R.C.mu0 i * R.xiH A.μ0 * R.C.eta⁻¹ := (by with_unfolding_all exact ((congrArg₂ (fun a b : Formalism.L2.Host.HChar X.toD7.host.E => a * b⁻¹)
      (congrArg₂ (fun a b : Formalism.L2.Host.HChar X.toD7.host.E => a * b) (congrFun (eq_of_heq emu) i) (hL'.xi_base.trans hL.xi_base.symm))
      (eq_of_heq eeta)) :))
  have eξ : R'.xi A'.μ0 = R.xi A.μ0 := (GlobalTheory.ChrEqUnique.chrEq_unique X.toD7).2.1 _ _ _ ((by with_unfolding_all exact (hx1' :))) hx1
  have hT1 := (tupOver_iff R A.μ0).2 ⟨repsR_map (incF O.c' c₃ hs) hB.reps, (hM.tuple ()).B, (hM.tuple ()).xi, (hM.tuple ()).phi,
    (hM.tuple ()).half⟩
  have hT2 := tupOver_cast (D := X.toD7) (Pg₂ := R'.Pg) (Q₂ := R'.Q A'.μ0) (βV₂ := (by with_unfolding_all exact (R'.βV :))) (βW₂ := (by with_unfolding_all exact (R'.βW :)))
    (ξR₂ := (by with_unfolding_all exact ((R'.xiR A'.μ0) :))) ePg hQ hQ' ((by with_unfolding_all exact (eβV :))) ((by with_unfolding_all exact (eβW :))) eχ eξ hT1
  have hl2 := levOver_cast' (D := X.toD7) (Pg₂ := R'.Pg) (β₂ := (by with_unfolding_all exact (R'.βW :))) (e₂ := (by with_unfolding_all exact (R'.eG :))) ePg ((by with_unfolding_all exact (eβW :))) ((by with_unfolding_all exact (eG :)))
    ((levOver_iff T R i O.lev).2 hO.lift.lev)
  let κ₀ : WeightFamilies.Wt X.toD7 ((i : ℕ) + 1) := ⟨(by with_unfolding_all exact ((κ' i).aP :)), (by with_unfolding_all exact ((κ' i).aM :)), (by with_unfolding_all exact ((κ' i).aPlus_antitone :)), (by with_unfolding_all exact ((κ' i).aM_anti :)), (κ' i).n, (κ' i).n_even⟩
  have ew : wtA κ₀ = wtA (κ i) := wtA_eq _ _
    (funext fun τ => funext fun k => Eq.trans ((by with_unfolding_all exact (((hκ' τ).1 k) :))) ((hκ i τ).1 k).symm)
    (funext fun τ => funext fun k => Eq.trans ((by with_unfolding_all exact (((hκ' τ).2.1 k) :))) ((hκ i τ).2.1 k).symm)
  have hio := hM.io
  rw [← ew] at hio
  let M := bc O c₃ hs c0₃ io₃ hw₃ h (v₀ i (sg0 X.toD7 A))
  refine ⟨@OMDat.mk _ G _ _ Pl0' T0' A' _ alg' R' i Unit _ (c' := c₃) (hle := h₃) (jL := jL') (hV := hV₃) (c0' := c0'') (lev := (by with_unfolding_all exact (M.lev :)))
    (dδ := (by with_unfolding_all exact (M.dδ :))) (Cl' := M.Cl') (fCl := M.fCl) (bad := M.bad) (Lh := (by with_unfolding_all exact (M.Lh :))) (La := (by with_unfolding_all exact (M.La :))) (Nc := (by with_unfolding_all exact (M.Nc :))) (gam := (by with_unfolding_all exact (M.gam :)))
    (vol := (by with_unfolding_all exact (M.vol :))) (ep := (by with_unfolding_all exact (M.ep :))) (B := (by with_unfolding_all exact (M.B :))) (epF := (by with_unfolding_all exact (M.epF :))) (io := (by with_unfolding_all exact (M.io :))) (hw := (by with_unfolding_all exact (M.hw :))) (φ := (by with_unfolding_all exact (M.φ :)))
    (w := (by with_unfolding_all exact (M.w :))) (U₂ := (by with_unfolding_all exact (M.U₂ :))) (dict₂ := (by with_unfolding_all exact (M.dict₂ :))) (xi := (by with_unfolding_all exact (M.xi :)))
    (thAd := fun _ => thAdOf R' i A'.μ0 (Cl := O.Cl' ()) ((by with_unfolding_all exact (h :))) c0'' (v₀' i (sg0 _ A')))
    (Plc := fun _ x => ∃ x₀, Place R' i A'.μ0 (Cl := O.Cl' ()) ((by with_unfolding_all exact (h :))) c0'' (jVx R' i A'.μ0 x₀) x), hF₃, ?_, ?_⟩
  · have hth := thAdIs_thAdOf R' i A'.μ0 (Cl := O.Cl' ()) ((by with_unfolding_all exact (h :))) c0'' hM'.HV (J' := (by with_unfolding_all exact (J' :))) ((by with_unfolding_all exact (hT2.1.2.2.1 :))) ((by with_unfolding_all exact (hT2.1.2.2.2.2.2.1 :)))
      (v₀' i (sg0 _ A'))
    obtain ⟨g', r', hT'⟩ := hT'
    apply (config := { synthAssignedInstances := false }) OMDat.Pins.mk
    case lift =>
      apply (config := { synthAssignedInstances := false }) ThPinsR.mk
      case field => exact hjL'
      case std => exact (by with_unfolding_all exact (hO.lift.std :))
      case v0 => exact hv0'
      case lev => exact (by with_unfolding_all exact (hl2 :))
      case c0 => exact ⟨g', r', c0L', hT', hbc'⟩
    case tuple =>
      intro t
      apply (config := { synthAssignedInstances := false }) ThPinsT.mk
      case reps => exact ⟨(by with_unfolding_all exact (h :)), (by with_unfolding_all exact (J' :)), (by with_unfolding_all exact (hT2.1 :)), (by with_unfolding_all exact ((hpl' (O.Cl' ()) ((by with_unfolding_all exact (h :)))) :)), (by with_unfolding_all exact (hth :)), fun _ => Iff.rfl⟩
      case B => exact (by with_unfolding_all exact (hT2.2.1 :))
      case xi => exact (by with_unfolding_all exact (hT2.2.2.1 :))
      case phi => exact (by with_unfolding_all exact (hT2.2.2.2.1 :))
      case half => exact (by with_unfolding_all exact (hT2.2.2.2.2 :))
    case act => exact (by with_unfolding_all exact (hM.act :))
    case bad => exact (by with_unfolding_all exact (hM.bad :))
    case reps => exact (by with_unfolding_all exact (hM.reps :))
    case ep => exact (by with_unfolding_all exact (hM.ep :))
    case io => exact (by with_unfolding_all exact (hio :))
    case w => exact (by with_unfolding_all exact (hM.w :))
    case cov => exact (by with_unfolding_all exact (hM.cov :))
    case cxi => exact (by with_unfolding_all exact (hM.cxi :))
    case model₂ => exact (by with_unfolding_all exact (hM.model₂ :))
  · have hth := thAdIs_thAdOf R' i A'.μ0 (Cl := O.Cl' ()) ((by with_unfolding_all exact (h :))) c0'' hM'.HV (J' := (by with_unfolding_all exact (J' :))) ((by with_unfolding_all exact (hT2.1.2.2.1 :))) ((by with_unfolding_all exact (hT2.1.2.2.2.2.2.1 :)))
      (v₀' i (sg0 _ A'))
    refine ⟨c₃, hs, c0₃, io₃, hw₃, h, J', hB, ?_, hor, (by with_unfolding_all exact (h :)), (by with_unfolding_all exact (J' :)), (by with_unfolding_all exact ((HEq.refl h) :)), (by with_unfolding_all exact ((HEq.refl J') :)), (by with_unfolding_all exact (hT2.1 :)),
      (by with_unfolding_all exact ((hpl' (O.Cl' ()) ((by with_unfolding_all exact (h :)))) :)), (by with_unfolding_all exact (hth :)), fun _ => Iff.rfl⟩
    exact ⟨(by with_unfolding_all exact ((HEq.refl M.c') :)), (by with_unfolding_all exact ((HEq.refl M.lev) :)), (by with_unfolding_all exact ((HEq.refl M.dδ) :)), rfl, (by with_unfolding_all exact ((HEq.refl M.fCl) :)), rfl, (by with_unfolding_all exact ((HEq.refl M.Lh) :)),
      (by with_unfolding_all exact ((HEq.refl M.La) :)), (by with_unfolding_all exact ((HEq.refl M.Nc) :)), (by with_unfolding_all exact ((HEq.refl M.gam) :)), (by with_unfolding_all exact ((HEq.refl M.vol) :)), (by with_unfolding_all exact ((HEq.refl M.ep) :)), (by with_unfolding_all exact ((HEq.refl M.B) :)),
      (by with_unfolding_all exact ((HEq.refl M.epF) :)), (by with_unfolding_all exact ((HEq.refl M.io) :)), (by with_unfolding_all exact ((HEq.refl M.hw) :)), (by with_unfolding_all exact ((HEq.refl M.φ) :)), (by with_unfolding_all exact ((HEq.refl M.w) :)), (by with_unfolding_all exact ((HEq.refl M.U₂) :)),
      (by with_unfolding_all exact ((HEq.refl M.dict₂) :)), (by with_unfolding_all exact ((HEq.refl M.xi) :))⟩

end GlobalTheory.Mem.R3.Rw.OmExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorIsIntegral
section
open ReciprocityTheory.ChartRestriction.G.FD NumberField

namespace GlobalTheory

theorem exists_common_denominator (E : Type) [Field E] [NumberField E] (n : ℕ) (f : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ ∀ j, IsIntegral ℤ ((d : E) * f j) := by
  classical
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image f)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, fun j => ?_⟩
  have hj := h (f j) (Finset.mem_image_of_mem f (Finset.mem_univ j))
  rw [zsmul_eq_mul] at hj
  rcases Int.natAbs_eq y with e | e
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [e]
      simp
    rw [this]; exact hj
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [e]
      simp
    rw [this, neg_mul]; exact hj.neg

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedPointOverOfLieEigenspaceFrame
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.FlagBundle

namespace GlobalTheory.ShFam

theorem exists_frPt_ptF_over_of_eigFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (L : Type) [Field L] (φ : c.F →+* L) (z : Sp L ⟶ Xo.XF c) (x : Sp L ⟶ Z.X) (g : EigFrame Z φ x), z ≫ pullback.snd _ _ = spMap φ → z ≫ Z.jQ ≫ genι Z = x → letI := φ.toAlgebra; ∃ y : FrPt Xo c L, GlobalTheory.AllWt.ptF y = z ∧ ∀ τ i, ∃ w : Sp (DualNumber L) ⟶ Z.oF.t.G.left, w ≫ Z.oF.t.G.hom = spMap (algebraMap L (DualNumber L)) ≫ z ∧ w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = g.v τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z L _ φ z x g hs hx
  letI := φ.toAlgebra
  obtain ⟨y, w, hy, hw⟩ := OpenReg.exists_frPt_of_eigFrame (Z := Z) z hs hx g
  refine ⟨y, pullback.hom_ext ?_ ?_, fun τ i => ⟨w τ i, hw τ i⟩⟩
  · exact (pullback.lift_fst _ _ _).trans hy
  · exact (pullback.lift_snd _ _ _).trans hs.symm

end GlobalTheory.ShFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFundamentalSetChartPreimageFundamentalDomainStatement
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFundamentalSet_chart_preimage_fundamentalDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1) → (∀ N, MeasurableSet N → N ⊆ DomFlat Tau j (r - j) → muD Tau j (r - j) N = 0 → muF X (x0F X) (proj X hj κ ⁻¹' N) = 0) → ∀ F, IsFD (gammaU X hj κ) F → ∃ F', MeasurableSet F' ∧ F' ⊆ F ∧ muD Tau j (r - j) (F \ F') = 0 ∧ IsFundSet X (x0F X) (proj X hj κ ⁻¹' F' ∩ OmF X (x0F X)) := by
  first | exact @GlobalTheory.FlagFibre.FundPre.isFundSet_preimage | exact GlobalTheory.FlagFibre.FundPre.isFundSet_preimage | (intros; apply GlobalTheory.FlagFibre.FundPre.isFundSet_preimage <;> assumption)
end

