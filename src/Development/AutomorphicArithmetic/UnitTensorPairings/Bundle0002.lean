module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0490
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.UnitTensorPairings.GeometricActionOverCoefficientExtension
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000

noncomputable section
namespace UpperTheory.RhoMove

private def RhoP {Rl L G : Type} [Field L] {n : ℕ} (P : Rl → Prop) (act : G → Rl → Rl) (e : Subtype P → Fin n → L)
    (ρ : G → (Fin n → L) →ₗ[L] (Fin n → L)) : Prop :=
  ((∀ g f, P f → P (act g f)) → ∀ g (f : Subtype P), ∃ hf : P (act g f.1), e ⟨act g f.1, hf⟩ = ρ g (e f)) ∧
    (¬ (∀ g f, P f → P (act g f)) → ∀ g, ρ g = 1)

private theorem rhoP_move {Rl L L' G : Type} [Field L] [Field L'] {n : ℕ} (P : Rl → Prop) (act : G → Rl → Rl)
    (e : Subtype P → Fin n → L) (e' : Subtype P → Fin n → L')
    (ρ : G → (Fin n → L) →ₗ[L] (Fin n → L)) (ρ' : G → (Fin n → L') →ₗ[L'] (Fin n → L')) (ι : L →+* L')
    (he : ∀ φ k, e' φ k = ι (e φ k))
    (hρ : ∀ g x x', CrdOver ι x x' → CrdOver ι (ρ g x) (ρ' g x'))
    (h : RhoP P act e ρ) : RhoP P act e' ρ' := by
  have hc : ∀ (x : Fin n → L) (x' : Fin n → L'), (∀ k, x' k = ι (x k)) → CrdOver ι x x' := fun x x' hx =>
    ⟨rfl, fun k k' hk => by obtain rfl : k = k' := Fin.ext hk; exact hx k⟩
  refine ⟨fun hk g f => ?_, fun hk g => ?_⟩
  · obtain ⟨hf, h2⟩ := h.1 hk g f
    refine ⟨hf, funext fun k => ?_⟩
    rw [he, h2]
    exact ((hρ g _ _ (hc _ _ (he f))).2 k k rfl).symm
  · have h1 := h.2 hk g
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    funext k
    have h3 := (hρ g (Pi.single j 1) (Pi.single j 1) (hc _ _ fun k => by
      by_cases hjk : k = j
      · subst hjk; simp
      · simp [Pi.single_eq_of_ne hjk])).2 k k rfl
    simp only [LinearMap.comp_apply, LinearMap.single_apply, Module.End.one_apply]
    rw [h3, h1, Module.End.one_apply]
    by_cases hjk : k = j
    · subst hjk; simp
    · simp [Pi.single_eq_of_ne hjk]

private theorem rhoP_core {D : D7} (T : CoreJ D) (i : Fin D.R.m)
    {a a' : (D.host.E →+* ℂ) × ℕ → ℕ} (ha : a' = a) {m m' : ℕ} (hm : m' = m)
    {G G' : Type} [iG : Group G] [iG' : Group G'] (hG : G' = G) (hi : HEq iG' iG)
    {lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La}
    {lev' : G' → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La} (hl : HEq lev' lev)
    {L L' : Type} [Field L] [Field L'] {n n' : ℕ} (hn : n = n')
    (e : T.cuspA ((i : ℕ) + 1) a m → Fin n → L) (e' : T.cuspA ((i : ℕ) + 1) a' m' → Fin n' → L')
    (ρ : G → (Fin n → L) →ₗ[L] (Fin n → L)) (ρ' : G' → (Fin n' → L') →ₗ[L'] (Fin n' → L')) (ι : L →+* L')
    (emb : L →+* ℂ) (emb' : L' →+* ℂ) (hι : ∀ x, emb' (ι x) = emb x)
    (he : ∀ φ φ', HEq φ' φ → ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → emb' (e' φ' k') = emb (e φ k))
    (hρ : ∀ g' g, HEq g' g → ∀ x x', CrdOver ι x x' → CrdOver ι (ρ g x) (ρ' g' x'))
    (h : RhoP (fun f => f ∈ T.cuspA ((i : ℕ) + 1) a m) (fun g f => actLev T.Q.c (fun g => (lev g, LinearMap.id)) g f) e ρ) :
    RhoP (fun f => f ∈ T.cuspA ((i : ℕ) + 1) a' m') (fun g f => actLev T.Q.c (fun g => (lev' g, LinearMap.id)) g f) e' ρ' := by
  subst ha hm hG hn
  cases hi; cases hl
  exact rhoP_move _ _ e e' ρ ρ' ι (fun φ k => emb'.injective ((he φ φ HEq.rfl k k rfl).trans (hι _).symm))
    (fun g => hρ g g HEq.rfl) h

private theorem rhoGeo_iff {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T R κ v₀)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) :
    RhoGeo fw O ↔ ∀ i : Fin D.R.m, RhoP (fun f => f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n)
      (fun g f => actLev T.Q.c (fun g => ((O i).lev g, LinearMap.id)) g f)
      (fun φ => ((fw.e i φ : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)) (fun g => (R.FW i).ρ g) := Iff.rfl

end UpperTheory.RhoMove
end

open UpperTheory.RhoMove in
theorem UpperTheory.geometric_action_over_coefficient_extension :
    ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T) (w' : ColW B' f' T')
        (Z : w.Lt) (Z' : w'.Lt) (hX : B.fields.Ok) (hX' : B'.fields.Ok) (Wt : Set B.places.Pl) (Wt' : Set B'.places.Pl)
        (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq w'.px w.px →
        ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) (alg' : Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL),
          (∀ y : core'.Q.c.F, B'.embLL (@algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL _ _ alg' y) = (y : ℂ)) →
          (HEq core'.Q.H z.core.Q.H ∧ HEq core'.Q.l z.core.Q.l ∧ HEq core'.Q.c z.core.Q.c ∧ HEq core'.Q.Dw z.core.Q.Dw ∧
          HEq core'.Q.Xo z.core.Q.Xo ∧ HEq core'.U z.core.U ∧ HEq core'.V z.core.V ∧ HEq core'.dict z.core.dict ∧
          HEq core'.mu z.core.mu ∧ HEq core'.Kf z.core.Kf ∧ HEq core'.cE z.core.cE ∧ HEq core'.chiW z.core.chiW ∧
          HEq core'.x₀ z.core.x₀ ∧ HEq core'.iota z.core.iota) →
          letI := alg'; ∀ (Xg : Finset (Gc B' w'.px → B'.LL)) (tr : TrI B' w'.px)
            (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
            (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
            GlobalTheory.Mem.R3.Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → RSide z Wt' R' →
            ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1)),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
              HEq (κ' i').aP (z.geo.κ i).aP ∧ HEq (κ' i').aM (z.geo.κ i).aM ∧ (κ' i').n = (z.geo.κ i).n) →
            ∀ (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (fw' : FWTie core' R'.toRealDat κ' v₀'),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
              ∀ (k : Fin (z.R.nW i)) (k' : Fin (R'.nW i')), (k : ℕ) = k' →
              (w'.st Z').toD7.what₂.embLL ((fw'.e i' φ' : (R'.FW i').WK).1 k') = (w.st Z).toD7.what₂.embLL ((z.geo.fw.e i φ : (z.R.FW i).WK).1 k)) →
            ∀ (O' : ∀ i, OMDat core'.toCore R'.toRealDat i Unit (fun _ => (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0)),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → HEq (O' i').lev (z.geo.O i).lev) →
            RhoGeo fw' O' := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hpx core' alg' halg' hcore Xg tr R' cG' hP hRS κ' hκ v₀' fw' hcrd O' hO
  obtain ⟨h1, -, -, hR⟩ := hE
  have hι := enlEmb_spec hR
  rcases B' with ⟨P'⟩
  change P' = B.toPre at h1
  subst h1
  have hpx' : w'.px = w.px := eq_of_heq hpx
  have hG : Gc _ w'.px = Gc B w.px := by rw [hpx']; rfl
  have hi : HEq (inferInstance : Group (Gc _ w'.px)) (inferInstance : Group (Gc B w.px)) := by rw [hpx']; exact HEq.rfl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hI, -⟩ := hRS.1
  rcases core' with ⟨⟨⟨H', l', c', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩
  obtain ⟨hH, hl, hc, hDw, hXo, hU, -, -, -, -, -, -, -, -⟩ := hcore
  obtain rfl : H' = z.core.Q.H := eq_of_heq hH
  obtain rfl : l' = z.core.Q.l := eq_of_heq hl
  obtain rfl : c' = z.core.Q.c := eq_of_heq hc
  obtain rfl : Dw' = z.core.Q.Dw := eq_of_heq hDw
  obtain rfl : Xo' = z.core.Q.Xo := eq_of_heq hXo
  obtain rfl : U' = z.core.U := eq_of_heq hU
  refine (rhoGeo_iff fw' O').2 fun i => ?_
  have hk := hκ i i rfl
  have a1 := hk.1
  have a2 := hk.2.1
  have a3 := hk.2.2
  have ha : wtA (κ' i) = wtA (z.geo.κ i) := by
    have e1 := eq_of_heq a1
    have e2 := eq_of_heq a2
    unfold wtA
    rw [e1, e2]
    rfl
  have hιc := (hI i i rfl).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (enlEmb hR) hι
  have hρ := hιc.2.2.2.1
  have hW := hιc.2.1.2
  have hn : z.R.nW i = R'.nW i := (hW 0 (Submodule.zero_mem _)).elim fun _ h => h.1
  have hz := (@rhoGeo_iff _ _ _ _ _ _ _ _ z.alg _ _ _ z.geo.fw z.geo.O).1 z.geo.rhoGeo i
  have key := rhoP_core z.core i ha a3 hG hi (hO i i rfl) hn _
    ((by with_unfolding_all exact ((fun φ => ((fw'.e i φ : (R'.FW i).WK) : Fin (R'.nW i) → (w'.st Z').toD7.what₂.LL)) :))) _ (fun g => (R'.FW i).ρ g) (enlEmb hR)
    (w.st Z).toD7.what₂.embLL (w'.st Z').toD7.what₂.embLL hι ((by with_unfolding_all exact ((hcrd i i rfl) :))) hρ hz
  exact (by with_unfolding_all exact (key :))
end

-- bundled from Development.AutomorphicArithmetic.UnitTensorPairings.LocalCuspNormsIndepOfBaseSamePre
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult GlobalTheory.RealGeo
set_option maxHeartbeats 4000000

private def UpperTheory.LocalNormsMatchCuspForms {D : D7} (T : CoreJ D) (j : ℕ) (w : WeightFamilies.Wt D j)
    (Pt : HeightOneSpectrum (𝓞 T.Q.c.F) → Type) {W : Type} (nrm : ∀ la, Pt la → W → ℝ)
    (e : T.cuspA j (wtA w) w.n → W) (pt : ∀ la, Pt la → T.PtM j la) : Prop :=
  ∀ la (y : Pt la) (f : T.cuspA j (wtA w) w.n), nrm la y (e f) = T.nrmM j la (pt la y) (f : T.R j)

private theorem UpperTheory.congr_of_heq {D : D7} (T T' : CoreJ D) (h1 : HEq T'.Q.H T.Q.H) (h2 : HEq T'.Q.l T.Q.l) (h3 : HEq T'.Q.c T.Q.c)
    (h4 : HEq T'.Q.Dw T.Q.Dw) (h5 : HEq T'.Q.Xo T.Q.Xo) (h6 : HEq T'.U T.U)
    (j : ℕ) (w w' : WeightFamilies.Wt D j) (hP : HEq w'.aP w.aP) (hM : HEq w'.aM w.aM) (hn : w'.n = w.n)
    (Pt : HeightOneSpectrum (𝓞 T.Q.c.F) → Type) (Pt' : HeightOneSpectrum (𝓞 T'.Q.c.F) → Type) (hPt : HEq Pt' Pt)
    {W W' : Type} (Rel : W → W' → Prop) (nrm : ∀ la, Pt la → W → ℝ) (nrm' : ∀ la, Pt' la → W' → ℝ)
    (hnrm : ∀ la' la, HEq la' la → ∀ y' y, HEq y' y → ∀ φ' φ, Rel φ φ' → nrm' la' y' φ' = nrm la y φ)
    (e : T.cuspA j (wtA w) w.n → W) (e' : T'.cuspA j (wtA w') w'.n → W') (he : ∀ φ φ', HEq φ' φ → Rel (e φ) (e' φ'))
    (pt : ∀ la, Pt la → T.PtM j la) (pt' : ∀ la, Pt' la → T'.PtM j la)
    (hpt : ∀ la la', HEq la' la → ∀ y' y, HEq y' y → HEq (pt' la' y') (pt la y)) :
    UpperTheory.LocalNormsMatchCuspForms T j w Pt nrm e pt → UpperTheory.LocalNormsMatchCuspForms T' j w' Pt' nrm' e' pt' := by
  obtain ⟨⟨⟨H, l, cc, Dw, Xo, eO⟩, U, V, dict, mu, Kf, pb⟩, cE, chiW, x₀, iota⟩ := T
  obtain ⟨⟨⟨H', l', cc', Dw', Xo', eO'⟩, U', V', dict', mu', Kf', pb'⟩, cE', chiW', x₀', iota'⟩ := T'
  dsimp only at h1 h2 h3 h4 h5 h6
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases h6
  obtain ⟨aP, aM, _, _, m, _⟩ := w
  obtain ⟨aP', aM', _, _, m', _⟩ := w'
  dsimp only at hP hM hn
  cases hP
  cases hM
  cases hn
  cases hPt
  intro h la y f
  have k1 := hnrm la la HEq.rfl y y HEq.rfl _ _ (he f f HEq.rfl)
  have k3 : pt' la y = pt la y := eq_of_heq (hpt la la HEq.rfl y y HEq.rfl)
  rw [k1, k3]
  exact h la y f

private noncomputable def UpperTheory.ringOfIntegersEquivOfEqSubfield {F F' : IntermediateField ℚ ℂ} (h : F' = F) : 𝓞 F ≃+* 𝓞 F' := by
  subst h
  exact RingEquiv.refl _

private theorem UpperTheory.coeff_field_eq_of_heq {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {l' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H'}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l'}
    (h1 : HEq H' H) (h2 : HEq l' l) (h3 : HEq c' c) : c'.F = c.F := by
  cases h1
  cases h2
  cases h3
  rfl

theorem UpperTheory.localCuspNorms_indep_of_base_same_pre :
    ∀ (B B' : Base) (f : Fr B.toPre) (f' : Fr B'.toPre) (T : TwDat B) (T' : TwDat B') (w : ColW B f T) (w' : ColW B' f' T'),
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
          ∀ (e' : ∀ i : Fin (w'.st Z').toD7.R.m, core'.cuspA ((i : ℕ) + 1) (wtA (κ' i)) (κ' i).n ≃ₗ[core'.Q.c.F] (R'.FW i).WK),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ φ φ', HEq φ' φ →
              CrdOver ι (z.geo.fw.e i φ : (z.R.FW i).WK).1 (e' i' φ' : (R'.FW i').WK).1) →
          ∀ (pt' : ∀ (i : Fin (w'.st Z').toD7.R.m) (la : HeightOneSpectrum (𝓞 core'.Q.c.F)), (R'.FW i).Pt la ≃ core'.PtM ((i : ℕ) + 1) la),
            (∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → ∀ la la', HEq la' la → ∀ y' y, HEq y' y →
              HEq (pt' i' la' y') (z.geo.fw.pt i la y)) →
          ∀ (i : Fin (w'.st Z').toD7.R.m) (la : HeightOneSpectrum (𝓞 core'.Q.c.F)) (y : (R'.FW i).Pt la) (f : core'.cuspA ((i : ℕ) + 1) (wtA (κ' i)) (κ' i).n),
            (R'.FW i).nrm la y (e' i f) = core'.nrmM ((i : ℕ) + 1) la (pt' i la y) (f : core'.R ((i : ℕ) + 1)) := by
  intro B B' f f' T T' w w' hPre Z hX Wt z Z' hX' Wt' core' alg' halg hc _ Xg tr R' hRS _ ι hι κ' hκ e' he pt' hpt i'
  letI := alg'
  letI := z.alg
  have hm : (w'.st Z').toD7.R.m = (w.st Z).toD7.R.m := (by with_unfolding_all exact ((congrArg (fun P : Pre => P.R.m) hPre) :))
  let i : Fin (w.st Z).toD7.R.m := ⟨i'.1, hm ▸ i'.2⟩
  have hi : (i : ℕ) = i' := rfl
  have hb : UpperTheory.LocalNormsMatchCuspForms z.core ((i : ℕ) + 1) (z.geo.κ i) (z.R.FW i).Pt (W := (z.R.FW i).WK) (z.R.FW i).nrm
      (fun φ => z.geo.fw.e i φ) (fun la y => z.geo.fw.pt i la y) := (by with_unfolding_all exact ((z.geo.fw.nrm_eq i) :))
  have hcl := ((hRS.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 ι hι).2.2.2.2
  have hPt := hcl.1
  have hnrm := hcl.2
  have he1 := he i i' hi
  have hpt1 := hpt i i' hi
  obtain ⟨hP, hM, hnn⟩ := hκ i i' hi
  obtain ⟨c1, c2, c3, c4, c5, c6, -⟩ := hc
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  let H₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host (w'.st Z').toD7.host.E := (by with_unfolding_all exact (z.core.Q.H :))
  let l₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₁ := (by with_unfolding_all exact (z.core.Q.l :))
  let c₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₁ := (by with_unfolding_all exact (z.core.Q.c :))
  have hF : core'.Q.c.F = c₁.F := UpperTheory.coeff_field_eq_of_heq (H := H₁) (l := l₁) (c := c₁) ((by with_unfolding_all exact (c1 :))) ((by with_unfolding_all exact (c2 :))) ((by with_unfolding_all exact (c3 :)))
  let Q₀ : Formalism.L2.Pj.Par (w'.st Z').toD7 :=
    { H := H₁, l := l₁, c := c₁, Dw := (by with_unfolding_all exact (z.core.Q.Dw :)), Xo := (by with_unfolding_all exact (z.core.Q.Xo :)),
      eO := (UpperTheory.ringOfIntegersEquivOfEqSubfield hF).trans core'.Q.eO }
  let core₀ : Formalism.L2.Pj.CoreJ (w'.st Z').toD7 :=
    { toCore :=
        { Q := Q₀, U := (by with_unfolding_all exact (z.core.U :)), V := (by with_unfolding_all exact (z.core.V :)), dict := (by with_unfolding_all exact (z.core.dict :)), mu := (by with_unfolding_all exact (z.core.mu :)),
          Kf := (by with_unfolding_all exact (z.core.Kf :)), pb := (by with_unfolding_all exact (z.core.pb :)) }
      cE := (by with_unfolding_all exact (z.core.cE :)), chiW := (by with_unfolding_all exact (z.core.chiW :)), x₀ := (by with_unfolding_all exact (z.core.x₀ :)), iota := (by with_unfolding_all exact (z.core.iota :)) }
  let κ₀ : WeightFamilies.Wt (w'.st Z').toD7 ((i' : ℕ) + 1) :=
    { aP := (by with_unfolding_all exact ((z.geo.κ i).aP :)), aM := (by with_unfolding_all exact ((z.geo.κ i).aM :)), aPlus_antitone := (by with_unfolding_all exact ((z.geo.κ i).aPlus_antitone :)),
      aM_anti := (by with_unfolding_all exact ((z.geo.κ i).aM_anti :)), n := (z.geo.κ i).n, n_even := (z.geo.κ i).n_even }
  let Pt₀ : HeightOneSpectrum (𝓞 core₀.Q.c.F) → Type := (by with_unfolding_all exact ((z.R.FW i).Pt :))
  let nrm₀ : ∀ la, Pt₀ la → (z.R.FW i).WK → ℝ := (by with_unfolding_all exact ((z.R.FW i).nrm :))
  let e₀ : core₀.cuspA ((i' : ℕ) + 1) (wtA κ₀) κ₀.n → (z.R.FW i).WK := (by with_unfolding_all exact ((fun φ => z.geo.fw.e i φ) :))
  let pt₀ : ∀ la, Pt₀ la → core₀.PtM ((i' : ℕ) + 1) la := (by with_unfolding_all exact ((fun la y => z.geo.fw.pt i la y) :))
  exact (by with_unfolding_all exact ((UpperTheory.congr_of_heq core₀ core' ((c1)) ((c2)) ((c3)) ((c4)) ((c5)) ((c6))
    ((i' : ℕ) + 1) κ₀ (κ' i') ((hP)) ((hM)) ((hnn)) Pt₀ (R'.FW i').Pt ((hPt))
    (W := (z.R.FW i).WK) (W' := (R'.FW i').WK) (fun φ φ' => CrdOver ι φ.1 φ'.1) nrm₀ (R'.FW i').nrm ((hnrm))
    e₀ (fun φ => e' i' φ) ((he1)) pt₀ (fun la y => pt' i' la y) ((hpt1)) ((hb))) : _))
end

