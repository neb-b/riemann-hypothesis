module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineStableLieEigenspaceFrame
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0603
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricUniformisationSmoothOnInterior
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0554
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomCongrSymmEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.Mem.Top.TypesTrue GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.CopySide

theorem mem_center_map {G G' : Type} [Monoid G] [Monoid G'] (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ] MonoidAlgebra ℂ G')
    {a : MonoidAlgebra ℂ G} (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) :
    φ a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G') := by
  rw [Subalgebra.mem_center_iff] at ha ⊢
  intro b
  obtain ⟨b, rfl⟩ := φ.surjective b
  rw [← map_mul, ← map_mul, ha b]

def cenMap {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Subalgebra.center ℂ (MonoidAlgebra ℂ H) :=
  ((MonoidAlgebra.domCongr ℂ ℂ e).toAlgHom.comp (Subalgebra.center ℂ (MonoidAlgebra ℂ G)).val).codRestrict _ fun z =>
    mem_center_map (MonoidAlgebra.domCongr ℂ ℂ e) z.2

theorem cenMap_coeff {G H : Type} [Group G] [Group H] (e : G ≃* H) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (h : H) :
    ((cenMap e z : Subalgebra.center ℂ (MonoidAlgebra ℂ H)) : MonoidAlgebra ℂ H).coeff h =
      (z : MonoidAlgebra ℂ G).coeff (e.symm h) := by
  show (MonoidAlgebra.domCongr ℂ ℂ e (z : MonoidAlgebra ℂ G)).coeff h = _
  rw [MonoidAlgebra.coeff_domCongr]

theorem domCongr_symm_eq {G H : Type} [Group G] [Group H] (e : G ≃* H) (a : MonoidAlgebra ℂ H) (b : MonoidAlgebra ℂ G)
    (h : ∀ g, a.coeff (e g) = b.coeff g) : MonoidAlgebra.domCongr ℂ ℂ e.symm a = b := by
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun g => ?_
  rw [MonoidAlgebra.coeff_domCongr, MulEquiv.symm_symm]
  exact h g

theorem domCongr_eq {G H : Type} [Group G] [Group H] (e : G ≃* H) (a : MonoidAlgebra ℂ H) (b : MonoidAlgebra ℂ G)
    (h : ∀ g, a.coeff (e g) = b.coeff g) : MonoidAlgebra.domCongr ℂ ℂ e b = a := by
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun g => ?_
  rw [MonoidAlgebra.coeff_domCongr, ← h, MulEquiv.apply_symm_apply]


open Classical in
theorem tie_tr {G H E : Type} [Group G] [Group H] [AddCommGroup E] [Module ℂ E] (e : G ≃* H)
    (cen : Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ E) (a : MonoidAlgebra ℂ G) (b : MonoidAlgebra ℂ H)
    (h : ∀ g, b.coeff (e g) = a.coeff g) :
    (if ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) then cen ⟨a, ha⟩ else 0) =
      (if hb : b ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ H) then (cen.comp (cenMap e.symm)) ⟨b, hb⟩ else 0) := by
  have h1 := domCongr_symm_eq e b a h
  have h2 := domCongr_eq e b a h
  by_cases hb : b ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ H)
  · have ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
      rw [← h1]; exact mem_center_map _ hb
    rw [dite_eq_left ha, dite_eq_left hb, AlgHom.comp_apply]
    congr 1
    exact Subtype.ext h1.symm
  · have ha : a ∉ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
      intro ha; apply hb; rw [← h2]; exact mem_center_map _ ha
    rw [dite_eq_right ha, dite_eq_right hb]


set_option maxHeartbeats 1000000 in
theorem side_copy : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → ∃ (sg : SameGrp (B := B) (C := w.C) x.o.Z (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) (s : Side0 (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)), s.RR = x.s.RR ∧ HEq s.jEE x.s.jEE ∧ ∀ μ (c : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).nd))) (c0 : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))), (∀ g, (c0 : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)).coeff g = (c : MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).nd)).coeff (sg.iso g)) → s.cen μ c = x.s.cen μ c0 := by
  intro K B f T w P x N hN
  let sg : SameGrp (B := B) (C := w.C) x.o.Z (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)) :=
    { e := (by with_unfolding_all exact ((plEquiv x.o.N.naut N.naut) :))
      pl := (by with_unfolding_all exact ((TypesTrue.plGw_plEquiv x.fits.grp hN) :))
      e0 := (by with_unfolding_all exact ((x.fits.grp.typeIdempotent_coeff_across_layers hN) :)) }
  let φ := cenMap sg.iso.symm
  have hφ : ∀ c g, (φ c).val.coeff g = c.val.coeff (sg.iso g) := by
    intro c g
    rw [cenMap_coeff, MulEquiv.symm_symm]

  have hstd : ∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR →
      StdIso (w.st x.o.Z) w.px (eR.trans sg.iso.symm) := by
    rintro eR ⟨plg1, iso1, hpl1, hact1⟩
    refine ⟨(Equiv.sigmaCongrRight fun k => sg.e k).trans plg1, fun kv => iso1 ⟨kv.1, sg.e kv.1 kv.2⟩, fun kv => ?_, fun g kv => ?_⟩
    · exact (hpl1 _).trans (sg.pl kv.1 kv.2)
    · exact hact1 g _
  refine ⟨sg, { cen := fun μ => (x.s.cen μ).comp φ
                tie := fun μ => (x.s.tie μ).trans ((by with_unfolding_all exact ((tie_tr sg.iso (x.s.cen μ) _ _ sg.e0) :)))
                is := fun eR h μ c c' hc xx => ?_
                RR := x.s.RR
                frames := x.s.frames
                jEE := x.s.jEE
                basis := x.s.basis
                norm := x.s.norm }, rfl, HEq.rfl, fun μ c c0 hc => ?_⟩
  · show x.s.cen μ (φ c) xx = _
    refine x.s.is (eR.trans sg.iso.symm) (hstd eR h) μ (φ c) c' (fun g => ?_) xx
    exact (hc g).trans ((congrArg c.val.coeff (sg.iso.apply_symm_apply (eR g))).symm.trans (hφ c _).symm)
  · show x.s.cen μ (φ c) = _
    congr 1
    apply Subtype.ext
    apply MonoidAlgebra.coeff_injective
    refine Finsupp.ext fun g => ?_
    exact (hφ c g).trans (hc g).symm

end GlobalTheory.Mem.R3.Rw.CopySide

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenMetricGramSmoothInFamilyFrames
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.LieBase GlobalTheory.CxPts GlobalTheory.Cartier
open Filter Topology
open scoped Matrix
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LieBase.GramSmooth

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {y : GlobalTheory.CxPts p σ}

theorem cInfAt_mul {f g : GlobalTheory.CxPts p σ → ℝ} (hf : CInfAt f y) (hg : CInfAt g y) : CInfAt (fun z => f z * g z) y :=
  hf.comp₂ hg (G := fun x => x.1 * x.2) (contDiff_fst.mul contDiff_snd)

theorem cInfAt_sub {f g : GlobalTheory.CxPts p σ → ℝ} (hf : CInfAt f y) (hg : CInfAt g y) : CInfAt (fun z => f z - g z) y :=
  hf.comp₂ hg (G := fun x => x.1 - x.2) (contDiff_fst.sub contDiff_snd)

def CxInf (f : GlobalTheory.CxPts p σ → ℂ) (y : GlobalTheory.CxPts p σ) : Prop :=
  CInfAt (fun z => (f z).re) y ∧ CInfAt (fun z => (f z).im) y

variable {f g : GlobalTheory.CxPts p σ → ℂ}

theorem CxInf.mul (hf : CxInf f y) (hg : CxInf g y) : CxInf (fun z => f z * g z) y := by
  refine ⟨?_, ?_⟩
  · simp only [Complex.mul_re]; exact cInfAt_sub (cInfAt_mul hf.1 hg.1) (cInfAt_mul hf.2 hg.2)
  · simp only [Complex.mul_im]; exact (cInfAt_mul hf.1 hg.2).add (cInfAt_mul hf.2 hg.1)

theorem CxInf.star (hf : CxInf f y) : CxInf (fun z => star (f z)) y := by
  refine ⟨?_, ?_⟩
  · simpa [Complex.star_def] using hf.1
  · simpa [Complex.star_def] using hf.2.neg

theorem CxInf.sum {κ : Type} (s : Finset κ) {f : κ → GlobalTheory.CxPts p σ → ℂ} (h : ∀ a ∈ s, CxInf (f a) y) :
    CxInf (fun z => ∑ a ∈ s, f a z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => refine ⟨?_, ?_⟩ <;> simpa using cInfAt_const 0 y
  | insert a s ha ih =>
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun b hb => h b (Finset.mem_insert_of_mem hb)
    refine ⟨?_, ?_⟩
    · simp only [Finset.sum_insert ha, Complex.add_re]; exact h1.1.add h2.1
    · simp only [Finset.sum_insert ha, Complex.add_im]; exact h1.2.add h2.2

theorem cxInf_ratVal {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {y : GlobalTheory.CxPts X.str σ} {f : X.Fn}
    (hf : RegAt (under y) f) : CxInf (fun z => ratVal f z) y :=
  ⟨GlobalTheory.GoodMetric.cInfAt_ratVal (κ := Unit) (f := fun _ => f) (fun _ => hf)
               (G := fun v => (v ()).re) (Complex.reCLM.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) ())),
    GlobalTheory.GoodMetric.cInfAt_ratVal (κ := Unit) (f := fun _ => f) (fun _ => hf)
      (G := fun v => (v ()).im) (Complex.imCLM.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) ()))⟩

end GlobalTheory.LieBase.GramSmooth

namespace GlobalTheory.LieBase.GramSmooth

theorem cInfAt_comp {k k' : Type} [CommRing k] [CommRing k'] {Y Y' : Scheme.{0}} {p : Y ⟶ Sp k} {p' : Y' ⟶ Sp k'}
    {σ : k →+* ℂ} {σ' : k' →+* ℂ} {π : Y' ⟶ Y} {m : GlobalTheory.CxPts p' σ' → GlobalTheory.CxPts p σ} (hm : ∀ z, (m z).1 = z.1 ≫ π)
    {f : GlobalTheory.CxPts p σ → ℝ} {z : GlobalTheory.CxPts p' σ'} (h : CInfAt f (m z)) : CInfAt (fun w => f (m w)) z := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨π ⁻¹ᵁ W, ι, inferInstance, fun a => π.app W (g a), F, O, (mem_ptsIn_preimage hm).2 h₁, h₂, ?_, h₄, ?_⟩
  · simpa only [ev_of_comp hm] using h₃
  · simp only [← ev_of_comp hm]
    exact (continuous_of_comp hm).continuousAt.eventually h₅

end GlobalTheory.LieBase.GramSmooth

namespace GlobalTheory.LieBase.GramSmooth

theorem eventually_mem : ∀ (F : Type) [Field F] (X : Var F) (σ : F →+* ℂ) (ι : Type) [Finite ι] (m : ι → ℕ) (S : Fr (ratOf X) m 0) (y : GlobalTheory.CxPts X.str σ) (A : Mat m X.Fn), A ∈ S.S (under y) → ∀ᶠ z in 𝓝 y, A ∈ S.S (under z) := by
  intro F _ X σ ι _ m S y A hA
  obtain ⟨U, B, hU, hB, hS⟩ := S.loc (under y)
  have hP := (hS _ hU A).1 hA
  have hreg : ∀ g : X.Fn, RegAt (under y) g → ∀ᶠ z in 𝓝 y, RegAt (under z) g := by
    intro g hg
    obtain ⟨W, hW, a, rfl⟩ := hg.exists_fnOf
    filter_upwards [(isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)] with z hz
    exact regAt_fnOf (mem_ptsIn.1 hz) _ a
  have hU' : ∀ᶠ z in 𝓝 y, under z ∈ U := by
    filter_upwards [(isOpen_ptsIn U).mem_nhds (mem_ptsIn.2 hU)] with z hz
    exact mem_ptsIn.1 hz
  have h1 : ∀ᶠ z in 𝓝 y, ∀ τ, (∀ i j, RegAt (under z) ((A * B⁻¹) τ i j)) ∧ RegAt (under z) ((A * B⁻¹) τ).det⁻¹ :=
    Filter.eventually_all.2 fun τ => (Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      hreg _ (mem_O_ratOf.1 ((hP τ).1 i j))).and (hreg _ (mem_O_ratOf.1 (hP τ).2.2.1))
  filter_upwards [hU', h1] with z hz hz1
  exact (hS _ hz A).2 fun τ => ⟨fun i j => mem_O_ratOf.2 ((hz1 τ).1 i j), (hP τ).2.1, mem_O_ratOf.2 (hz1 τ).2,
    fun i j hi => absurd hi (by simp)⟩

theorem gram_entry_cInfAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (σ : c.F →+* ℂ) (G : EigMet Z σ), G.SmoothOn (manifold Z σ) {y | ¬ LiesIn y (genBd Z)} → ∀ (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Φ : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ → ∀ (τ : E →+* ℂ) (p q : Fin (Dw.mult τ)) (y : GlobalTheory.CxPts X.str (σ.comp e.toRingHom)), y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j) → cxOf e σ hj y ∈ ptsIn (genStr Z) σ V.1 → ∃ h : GlobalTheory.CxPts X.str (σ.comp e.toRingHom) → ℂ, CInfAt (fun z => (h z).re) y ∧ CInfAt (fun z => (h z).im) y ∧ ∀ᶠ z in 𝓝 y, ∀ (hz : cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1) (f : EigFrame Z σ ((cxOf e σ hj z).1 ≫ genι Z)), (fun mapψ dstFrame => ∀ embτ basisIdx, _root_.GlobalTheory.ShFam.EigFrame.v dstFrame embτ basisIdx = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (_root_.Formalism.L2.Pj.dualMap mapψ) ≫ _root_.GlobalTheory.ShFam.EigFrame.v Φ embτ basisIdx) (evHom hz) f → G.gram (cxOf e σ hj z) f τ p q = h z := by
  intro E _ _ _ H Dw l Xo c O _ β Z _ σ G hG F _ e X j hj V φ Φ hφ τ p q y hy hyV
  obtain ⟨g, hre, him, hg⟩ := hG V φ Φ τ p q hφ
  have hT : IsOpen ({y | ¬ LiesIn y (genBd Z)} ∩ ptsIn (genStr Z) σ V.1) := (isOpen_not_liesIn _).inter (isOpen_ptsIn _)
  have hm : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom), (cxOf e σ hj z).1 = z.1 ≫ j := fun _ => rfl
  have hyT : cxOf e σ hj y ∈ {y | ¬ LiesIn y (genBd Z)} ∩ ptsIn (genStr Z) σ V.1 :=
    ⟨mem_ptsIn.1 ((mem_ptsIn_preimage hm).1 hy), hyV⟩
  have cre := (cInfAt_iff_smoothOn (manifold Z σ) hT).2 hre _ hyT
  have cim := (cInfAt_iff_smoothOn (manifold Z σ) hT).2 him _ hyT
  refine ⟨fun z => g (cxOf e σ hj z), GlobalTheory.LieBase.GramSmooth.cInfAt_comp hm cre,
    GlobalTheory.LieBase.GramSmooth.cInfAt_comp hm cim, ?_⟩
  filter_upwards [(continuous_of_comp hm).continuousAt.preimage_mem_nhds (hT.mem_nhds hyT)] with z hz hz' f hf
  exact hg _ hz.1 hz' f hf

end GlobalTheory.LieBase.GramSmooth

theorem GlobalTheory.LieBase.cInfAt_gramOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) [SmoothOfRelativeDimension Dw.dim (genStr Z)] (σ : c.F →+* ℂ) (G : EigMet Z σ), G.SmoothOn (manifold Z σ) {y | ¬ LiesIn y (genBd Z)} → ∀ (F : Type) [Field F] (e : F ≃+* c.F) (X : Var F) (j : X.X ⟶ gen Z) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (S : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str), IsOpenImmersion j → Tied e X j f₀ S A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ A ∈ S.S (under y), ∀ (τ : E →+* ℂ) (a b : Fin (Dw.mult τ)), CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).re) y ∧ CInfAt (fun z => (gramOf e G hj f₀ A₀ A z τ a b).im) y := by
  intro E _ _ _ H Dw l Xo c O _ β Z _ σ G hG F _ e X j f₀ S A₀ hj hoi hT y hy A hA τ a b
  obtain ⟨U, hU, φ, Φ, hzU, hφ, -⟩ := EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z
    ((cxOf e σ hj y).1 (IsLocalRing.closedPoint ℂ))
  let V : (gen Z).affineOpens := ⟨U, hU⟩
  have hφ' : LogKS.chart V ≫ genStr Z = spMap φ := hφ
  have hyV : cxOf e σ hj y ∈ ptsIn (genStr Z) σ V.1 := mem_ptsIn.2 hzU
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.LieBase.coords_eq_ratVal_of_chart E H Dw l Xo c O β Z σ F e X j f₀ S A₀ hj hoi hT V φ Φ hφ' A
  choose h hre him hev using fun p q => GlobalTheory.LieBase.GramSmooth.gram_entry_cInfAt E H Dw l Xo c O β Z σ G hG F e X j hj V φ Φ hφ' τ p q y hy hyV
  have hS := GlobalTheory.LieBase.GramSmooth.eventually_mem F X (σ.comp e.toRingHom) (E →+* ℂ) Dw.mult S y A hA
  have hpre : ∀ z : GlobalTheory.CxPts X.str (σ.comp e.toRingHom),
      z ∈ ptsIn X.str (σ.comp e.toRingHom) (j ⁻¹ᵁ V.1) ↔ cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1 :=
    fun z => mem_ptsIn_preimage (m := cxOf e σ hj) (f := j) (fun _ => rfl)
  have hVn : ∀ᶠ z in 𝓝 y, cxOf e σ hj z ∈ ptsIn (genStr Z) σ V.1 := by
    filter_upwards [(isOpen_ptsIn _).mem_nhds ((hpre y).2 hyV)] with z hz
    exact (hpre z).1 hz
  have hall := Filter.eventually_all.2 fun pq : Fin (Dw.mult τ) × Fin (Dw.mult τ) => hev pq.1 pq.2
  have hreg := (hM y hA hyV).1 τ
  have key : ∀ᶠ z in 𝓝 y, gramOf e G hj f₀ A₀ A z τ a b =
      ∑ q, (∑ p, star (ratVal (M τ p b) z) * h p q z) * ratVal (M τ q a) z := by
    filter_upwards [hS, hVn, hall] with z hzS hzV hzall
    obtain ⟨-, hex, hco⟩ := hM z hzS hzV
    have hov : σ = (evHom hzV).comp φ := GlobalTheory.ShFam.EigLoc.spMap_inj ((cxOf e σ hj z).2.symm.trans (by
      rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]))
    have hx : (cxOf e σ hj z).1 ≫ genι Z = spMap (evHom hzV) ≫ LogKS.chart V ≫ genι Z := by
      rw [← Category.assoc, GlobalTheory.LieMet.spMap_evHom hzV]
    obtain ⟨f, hf⟩ := Φ.exists_isMap (evHom hzV) hov hx
    rw [gramOf, dite_eq_left hex]
    show (G.gram (cxOf e σ hj z) hex.choose τ)ᵀ a b = _
    rw [Matrix.transpose_apply, G.change (cxOf e σ hj z) f, hco _ hex.choose_spec f hf τ]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hzall (p, q) hzV f hf]
  open GlobalTheory.LieBase.GramSmooth in
  have hC : CxInf (fun z => ∑ q, (∑ p, star (ratVal (M τ p b) z) * h p q z) * ratVal (M τ q a) z) y :=
    CxInf.sum _ fun q _ => (CxInf.sum _ fun p _ => (cxInf_ratVal (hreg p b)).star.mul ⟨hre p q, him p q⟩).mul
      (cxInf_ratVal (hreg q a))
  exact ⟨hC.1.congr (key.mono fun z hz => congrArg Complex.re hz), hC.2.congr (key.mono fun z hz => congrArg Complex.im hz)⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalPullSemilinearOfIsTwInv
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

namespace OrbMark

theorem eval_pull_semilinear_of_isTwInv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)),
    IsTwInv H φ →
    ∀ {X Y : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y]
      [Module.Finite (𝓞 E) Y] (τ : 𝓞 E ≃+* 𝓞 E), τ H.w0 = H.w0 → ∀ (f : X →+ Y), Function.Surjective f →
      (∀ (a : 𝓞 E) (x : X), f (a • x) = τ a • f x) →
      ∀ B : Y → Y → ℝ, φ.eval X (fun x y => B (f x) (f y)) = φ.eval Y B := by
  intro E _ _ _ H φ htw X Y _ _ _ _ _ _ τ hτ f hf hsm B
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  let r₁ : (Fin n → 𝓞 E) →ₗ[𝓞 E] Y :=
    { toFun := fun a => f (r (twv τ.symm a))
      map_add' := fun a b => by
        have e : twv τ.symm (a + b) = twv τ.symm a + twv τ.symm b := funext fun _ => map_add τ.symm _ _
        rw [e, map_add (f := _), map_add (f := _)]
      map_smul' := fun c a => by
        rw [twv_smul, map_smul, hsm, RingEquiv.apply_symm_apply]
        rfl }
  have hr₁ : ∀ a, r₁ (twv τ a) = f (r a) := fun a => by
    show f (r (twv τ.symm (twv τ a))) = f (r a)
    rw [twv_symm_twv]
  have hs₁ : Function.Surjective r₁ := fun y => by
    obtain ⟨x, rfl⟩ := hf y
    obtain ⟨a, rfl⟩ := hr x
    exact ⟨twv τ a, hr₁ a⟩
  rw [φ.eval_eq hr, φ.eval_eq hs₁]
  have h := htw τ hτ n fun a b => B (r₁ a) (r₁ b)
  have e : (fun a b : Fin n → 𝓞 E => B (f (r a)) (f (r b))) = fun a b => B (r₁ (fun i => τ (a i))) (r₁ (fun i => τ (b i))) := by
    funext a b
    exact congrArg₂ B (hr₁ a).symm (hr₁ b).symm
  rw [e]
  exact h

end OrbMark

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDiagonalRiemannFormOrthonormalFrame
section
open AlgebraicGeometry CategoryTheory Limits MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.HodgeSmooth
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

section EigenvectorOrthogonality

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ProjVar.Var GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ArcQ GlobalTheory.FrameNormLie GlobalTheory.ShFam
open scoped ComplexOrder

namespace GlobalTheory.HodgeSmooth.EigOrth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}


open Classical in
def riemConst (U : Formalism.L2.PjFree.Unf Xo c σ r) (k : U.Comp) (τ : E →+* ℂ) : ℝ :=
  2 * ((if Formalism.L2.PjFree.relab c σ τ ∈ (U.X k).Ψ then Formalism.L2.PjFree.relab c σ τ
    else ComplexEmbedding.conjugate (Formalism.L2.PjFree.relab c σ τ)) (-(U.X k).ξ0)).im

theorem exists_diag_im {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (hx : IsOrth (U.X k) x.1) :
    ∃ D : Fin W.g → ℂ, (∀ τ (j : Fin (Dw.mult τ)), D (W.e.symm ⟨τ, j⟩) = ((riemConst U k τ : ℝ) : ℂ)) ∧
      ∀ v w, (hermForm (diagonal D) (W.Pm k x v) (W.Pm k x w)).im = (W.F.Di (W.ik k)).EF v w := by
  classical
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  obtain ⟨hbij, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨f, hf⟩ := FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hU.1
    (Formalism.L2.PjFree.relab c σ) hbij Dw.mult
    (fun τ h => by unfold Datum.mult; rw [if_pos ((hrt τ).1 ((hty _).1 h))])
    (fun τ h => by unfold Datum.mult; rw [if_neg (fun h' => h ((hty _).2 ((hrt τ).2 h')))])
  rw [← hp0] at hf
  have hper (v) : W.Pm k x v = perVec (U.X k) (W.e.trans f) x.1 (W.φ k v : Fin r → E) := funext fun j => by
    rw [W.Pm_eq, perVec, Equiv.trans_apply]
    have h := hf (W.e j)
    generalize f (W.e j) = t at h ⊢
    obtain ⟨⟨τ, hτ⟩, ⟨n, hn⟩⟩ := t
    dsimp only at h ⊢
    rcases h with ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl, d⟩
    · rw [if_neg (by omega), Formalism.L2.PjFree.perFr, dite_eq_left a, dite_eq_left hn]
    · rw [if_pos (by omega), Formalism.L2.PjFree.perFr, dite_eq_right a,
        dite_eq_left (show conjEmb (Formalism.L2.PjFree.relab c σ (W.e j).1) ∈ (U.X k).Ψ from hτ), dite_eq_left hn]
      rfl
  refine ⟨diagXi (U.X k) (W.e.trans f), fun τ j => ?_, fun v w => ?_⟩
  · rw [diagXi, Equiv.trans_apply, Equiv.apply_symm_apply]
    rcases hf ⟨τ, j⟩ with ⟨a, h1, -⟩ | ⟨a, h1, -, -⟩
    · rw [h1]
      simp only [riemConst, if_pos a]
    · rw [h1]
      simp only [riemConst, if_neg a]
  · rw [hper, hper, im_diag_ortho _ _ _ hx, ← W.iso]
    simp

theorem riemConst_pos {U : Formalism.L2.PjFree.Unf Xo c σ r} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (W : UnfWit U) (k : U.Comp) (x : (U.X k).dom) (hx : IsOrth (U.X k) x.1)
    (τ : E →+* ℂ) (hτ : 0 < Dw.mult τ) : 0 < riemConst U k τ := by
  classical
  obtain ⟨D, hD, him⟩ := exists_diag_im hσ hU W k x hx
  obtain ⟨-, -, -, hspan, Hm₀, -, hpos, hHm₀⟩ := W.period k x
  have e := UnitDet.eq_of_im_hermForm_eq _ hspan (diagonal D) Hm₀ (by
    rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    rw [him, hHm₀])
  set j := W.e.symm ⟨τ, ⟨0, hτ⟩⟩
  have h := hpos (Pi.single j 1) (by simp)
  rw [← e] at h
  have h2 : hermForm (diagonal D) (Pi.single j 1) (Pi.single j 1) = D j := by
    simp [hermForm]
  rw [h2, hD] at h
  simpa using h

end GlobalTheory.HodgeSmooth.EigOrth

end EigenvectorOrthogonality


open GlobalTheory.HodgeSmooth.EigOrth in
theorem GlobalTheory.HodgeSmooth.exists_diag_riem_orth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (W : UnfWit U), ∃ d : U.Comp → (E →+* ℂ) → ℝ, (∀ (k : U.Comp) (x : (U.X k).dom), IsOrth (U.X k) x.1 → ∀ τ : E →+* ℂ, 0 < Dw.mult τ → 0 < d k τ) ∧ ∀ (k : U.Comp) (x : (U.X k).dom), IsOrth (U.X k) x.1 → ∀ (i : Fin W.F.n) (P : (W.F.Di i).La →+ (Fin W.g → ℂ)), IsPeriod (W.F.Di i) (fun j => Formalism.L2.PjFree.relab c σ (W.e j).1) P → ∀ (Hm : Matrix (Fin W.g) (Fin W.g) ℂ), (∀ v w, (hermForm Hm (P v) (P w)).im = (W.F.Di i).EF v w) → W.F.u i P = (U.un k x).x → ∀ (τ τ' : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ)) (zz' : Fin (Dw.mult τ') → (Fin W.g → ℂ)) (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (uu' : Fin (Dw.mult τ') → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left)) (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ) (T' : Matrix (Fin (Dw.mult τ')) (Fin (Dw.mult τ')) ℂ), (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) → (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz' b) (uu' b)) → (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) → (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ') (show Fin (Dw.mult τ') → CAt σ from fun b' => T' b' b) (uu' b)) → (of fun b b' => hermForm Hm (zz b') (zz b)) = ((d k τ : ℝ) : ℂ) • (Tᴴ * T) ∧ (τ' ≠ τ → ∀ b b', hermForm Hm (zz' b') (zz b) = 0) := by
  classical
  intro E _ _ _ H Dw l Xo c σ r U hσ hU W
  refine ⟨fun k τ => riemConst U k τ, fun k x hx τ hτ => riemConst_pos hσ hU W k x hx τ hτ, ?_⟩
  intro k x hx i P hP Hm hH hPu τ τ' zz zz' uu uu' T T' hder hder' hT hT'
  obtain ⟨D, hD, him⟩ := exists_diag_im hσ hU W k x hx
  have p := W.period k x
  obtain ⟨hPx, hv⟩ := W.lie k x
  obtain ⟨h, gam, hex, hh, hiso, -⟩ := familyUnif_exp_unique E H Dw l Xo _ _ _ W.F i (W.ik k) P _ hP p
    (by rw [← hPx]; exact hPu)
  set A := LinearMap.toMatrix' h.toLinearMap with hA
  have hAv : ∀ z, A *ᵥ z = h z := fun z => by rw [hA, LinearMap.toMatrix'_mulVec]; rfl
  have hcol : ∀ (τ : E →+* ℂ) (zz : Fin (Dw.mult τ) → (Fin W.g → ℂ))
      (uu : Fin (Dw.mult τ) → (Sp (DualNumber ℂ) ⟶ Xo.univ.t.G.left))
      (T : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ),
      (∀ b, IsDerivAt0 (fun w => (W.F.ex i P w).left) (zz b) (uu b)) →
      (∀ b, IsCombAt (U.un k x).x ((U.un k x).u τ) (show Fin (Dw.mult τ) → CAt σ from fun b' => T b' b) (uu b)) →
      ∀ b, A *ᵥ zz b = ∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ) := by
    intro τ zz uu T hder hT b
    have d1 := (DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ _ _ W.F _ _ p _ ((U.un k x).u τ) _ (hv τ) _
      (uu b)).1 (hPx ▸ hT b)
    have d2 := (ExpChain.isDerivAt0_ex_iff E H Dw l Xo _ _ _ W.F _ P hP _ _ h.toLinearMap p hex _ _).1 (hder b)
    have tn := isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ W.F _ _ p
    rw [hAv]
    exact (tn.2.2 _ (tn.1 _ _ d2)).unique d2 d1
  have key := UnitDet.eq_of_im_hermForm_eq _ hP.2.2.2.1
    (Aᵀ * (diagonal D * A.map (starRingEnd ℂ))) Hm (by
      rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
      rw [← UnitDet.hermForm_mulVec, hAv, hAv, ← hh, ← hh, him, hiso, hH])
  refine ⟨?_, fun hne b b' => ?_⟩
  · have hsupp : ∀ b, diagonal D *ᵥ star (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) =
        (((riemConst U k τ : ℝ) : ℂ) • (1 : Matrix (Fin W.g) (Fin W.g) ℂ)) *ᵥ
          star (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) := by
      intro b
      simp only [smul_mulVec, Matrix.one_mulVec]
      funext p'
      rw [mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
      by_cases hp : ∃ j, W.e.symm ⟨τ, j⟩ = p'
      · obtain ⟨j, rfl⟩ := hp
        rw [hD τ j]
      · push_neg at hp
        have : (∑ j, T j b • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)) p' = 0 := by
          rw [Finset.sum_apply]
          exact Finset.sum_eq_zero fun j _ => by rw [Pi.smul_apply, Pi.single_eq_of_ne (hp j).symm, smul_zero]
        simp [Pi.star_apply, this]
    ext b b'
    rw [of_apply, ← key, ← UnitDet.hermForm_mulVec, hcol τ zz uu T hder hT, hcol τ zz uu T hder hT, hermForm,
      hsupp, ← hermForm]
    beta_reduce
    generalize ((riemConst U k τ : ℝ) : ℂ) = dd
    clear hsupp key hcol hAv hiso hh hex him hD hT hder hH hPu hT' hder'
    have hi : ∀ j j' : Fin (Dw.mult τ), W.e.symm ⟨τ, j⟩ = W.e.symm ⟨τ, j'⟩ ↔ j = j' := fun j j' => by simp
    simp [hermForm, smul_mulVec, sum_dotProduct, dotProduct_sum, star_sum, Pi.single_apply, hi, mul_apply, mul_comm]
    left
    simp [Matrix.mul_apply, mul_comm]
  · rw [← key, ← UnitDet.hermForm_mulVec, hcol τ' zz' uu' T' hder' hT', hcol τ zz uu T hder hT]
    simp only [hermForm, dotProduct, mulVec_diagonal, Pi.star_apply]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : ∃ j, W.e.symm ⟨τ', j⟩ = q
    · obtain ⟨j, rfl⟩ := hq
      have : (∑ j'', T j'' b • (Pi.single (W.e.symm ⟨τ, j''⟩) 1 : Fin W.g → ℂ)) (W.e.symm ⟨τ', j⟩) = 0 := by
        rw [Finset.sum_apply]
        refine Finset.sum_eq_zero fun j'' _ => ?_
        rw [Pi.smul_apply, Pi.single_eq_of_ne, smul_zero]
        intro he
        exact hne (congrArg Sigma.fst (W.e.symm.injective he))
      rw [this]
      simp
    · push_neg at hq
      have : (∑ j, T' j b' • (Pi.single (W.e.symm ⟨τ', j⟩) 1 : Fin W.g → ℂ)) q = 0 := by
        rw [Finset.sum_apply]
        exact Finset.sum_eq_zero fun j _ => by rw [Pi.smul_apply, Pi.single_eq_of_ne (hq j).symm, smul_zero]
      rw [this]
      simp
end
end

