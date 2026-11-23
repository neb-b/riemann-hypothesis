module

public import Development.WeilBound.CoreStatements.ProjectiveValuations.OpenImmersionCompStructureEqGeneric
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1958
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2041
public import Development.WeilBound.CoreStatements.ProjectiveValuations.InitSpanEqOfTri
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1943
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LocallyQuasiFiniteOfFiniteGeometricPoints

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.ProjectiveValuations.ExistsFrBorOfMatches
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt

noncomputable section

namespace DifferentiableLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

open Limits GlobalTheory.CxPts Filter Topology GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory


open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory Formalism.BasicNotions MonObj GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CovTop GlobalTheory.HSApp in
theorem exists_frBor_of_matches (T : TorFlag Xo c) {A : Type} [CommRing A] (q : Sp A ⟶ T.X.YY) (k : T.X.F.J)
    (hz : ⊤ ≤ q ⁻¹ᵁ T.X.F.U k) {φ : c.F →+* A} {x : Sp A ⟶ gen T.Y} (hx : q ≫ T.X.π = x ≫ genι T.Y)
    (fr : EigFrame T.Y φ (x ≫ genι T.Y))
    (hfr : ∀ τ j, fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (T.X.F.vecAt k q hz hx τ j)).left) (ψ : A →+* CAt σ)
    {y : FrPt Xo c (CAt σ)} (hm : Matches fr ψ y) {z : Sp (CAt σ) ⟶ T.X.YY}
    (e : spMap ψ ≫ q = z) (hz' : ⊤ ≤ z ⁻¹ᵁ T.X.F.U k) :
    ∃ (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ), T.X.F.ChartFr k z hz' Q ∧ FrBor t Q y ∧ ∀ s, t (some s) = 1 := by
  subst e
  let z' : Sp (CAt σ) ⟶ T.X.YY := spMap ψ ≫ q
  have ex : spMap ψ ≫ (x ≫ genι T.Y) = z' ≫ T.X.π := by
    rw [← hx]; exact (Category.assoc _ _ _).symm
  have hxy : GlobalTheory.FlagMod.frX y ≫ T.Y.j = z' ≫ T.X.π := by
    calc GlobalTheory.FlagMod.frX y ≫ T.Y.j = (GlobalTheory.AllWt.ptF y ≫ T.Y.jQ) ≫ genι T.Y := by rw [Category.assoc]; rfl
    _ = spMap ψ ≫ (x ≫ genι T.Y) := (congrArg (· ≫ genι T.Y) hm.1).trans (Category.assoc _ _ _)
    _ = z' ≫ T.X.π := ex
  obtain ⟨Q, hQ⟩ := T.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) hxy.symm k hz'
  have hv : ∀ τ j, GlobalTheory.FlagMod.frVec T.Y y hxy τ j = GlobalTheory.FlagMod.frVec T.Y Q hQ.over τ j := fun τ j => by
    rw [hQ.frVec_eq rfl hQ.over τ]
    refine (GlobalTheory.FlagMod.toModel_eq_iff _ _ _ _ _).2 ?_
    obtain ⟨w, h1, h2, h3⟩ := hm.2 τ j
    refine ⟨w, h1, h2, h3.trans ?_⟩
    rw [hfr τ j, ← T.X.F.tanPull_vecAt k ψ q hz hz' hx rfl ex]
    rfl
  have eQ : y.x = Q.x := by
    rw [← GlobalTheory.FlagMod.frX_fst, ← GlobalTheory.FlagMod.frX_fst,
      GlobalTheory.FlagMod.xF_ext (Y := T.Y) (GlobalTheory.FlagMod.frX_snd y) (GlobalTheory.FlagMod.frX_snd Q) (hxy.trans hQ.over.symm)]
  obtain ⟨u0, hu0⟩ := GlobalTheory.CompHS.BridgeValue.exists_gen_unit Q y eQ
  let t : Ix D → (CAt σ)ˣ := fun ix => ix.elim u0 fun _ => 1
  refine ⟨Q, t, hQ, GlobalTheory.FlagMod.frBor_of_frVec (T.X.F.inM hz' rfl) hQ.over hxy t (fun _ => 1)
    (fun _ => Matrix.blockTriangular_one) (fun _ i => Matrix.one_apply_eq i)
    (fun τ j => ?_) (fun _ => hu0), fun _ => rfl⟩
  rw [hv τ j]
  refine ((Fintype.sum_eq_single j fun j' hj' => ?_).trans ?_).symm
  · show (1 : Matrix (Fin (D.mult τ)) (Fin (D.mult τ)) (CAt σ)) j' j • _ = 0
    rw [Matrix.one_apply_ne hj', zero_smul]
  · show (1 : Matrix (Fin (D.mult τ)) (Fin (D.mult τ)) (CAt σ)) j j • _ = _
    rw [Matrix.one_apply_eq, one_smul]

theorem matches_of_sameLie {Z : Model Xo c (RingHom.id c.F)} {A : Type} [CommRing A] {φ : c.F →+* A} {x : Sp A ⟶ gen Z}
    {fr : EigFrame Z φ (x ≫ genι Z)} {ψ : A →+* ℂ} {y y' : FrPt Xo c (CAt σ)} (hm : Matches fr ψ y)
    (h : SameLie y' y) : Matches fr ψ y' := by
  have e : GlobalTheory.AllWt.ptF y' = GlobalTheory.AllWt.ptF y := by
    refine pullback.hom_ext ?_ ?_
    · exact (pullback.lift_fst _ _ _).trans (h.1.trans (pullback.lift_fst _ _ _).symm)
    · exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  refine ⟨e ▸ hm.1, fun τ i => ?_⟩
  rw [e, h.2 τ i]
  exact hm.2 τ i

theorem chr_of_some {e : Ix D → ℤ} {t : Ix D → (CAt σ)ˣ} (h : ∀ s, t (some s) = 1) :
    chr e t = toC (t none).val ^ e none := by
  classical
  have : (∏ ix, t ix ^ e ix) = t none ^ e none := by
    rw [Fintype.prod_option, Finset.prod_eq_one fun s _ => by rw [h, one_zpow], mul_one]
  exact (congrArg (fun u : (CAt σ)ˣ => toC u.val) this).trans (@Units.val_zpow_eq_zpow_val ℂ _ (t none) (e none))

theorem tendsto_punctured {f : ℂ → ℂ} (h : Tendsto (fun w => f (eTwoPi w)) imTop (𝓝 0)) :
    Tendsto f (𝓝[≠] 0) (𝓝 0) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have t₁ : Tendsto (fun u : ℂ => Complex.log u / (2 * Real.pi * Complex.I)) (𝓝[≠] 0) imTop := by
    refine tendsto_comap_iff.2 ?_
    have h₁ : Tendsto (fun u : ℂ => ‖u‖) (𝓝[≠] 0) (𝓝[>] 0) := tendsto_norm_nhdsNE_zero
    have h₂ := (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h₁)).atTop_div_const hπ
    refine h₂.congr fun u => ?_
    have e : (2 * Real.pi * Complex.I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by push_cast; ring
    simp only [Function.comp_apply]
    rw [e, ← div_div (Complex.log u), Complex.div_I, Complex.neg_im, Complex.mul_I_im, Complex.div_ofReal_re, Complex.log_re, neg_div]
  refine (h.comp t₁).congr' (eventually_mem_nhdsWithin.mono fun u hu => ?_)
  simp only [Function.comp_apply, eTwoPi]
  rw [mul_div_cancel₀ _ hne, Complex.exp_log hu]


set_option maxHeartbeats 800000 in
theorem exists_eigFrame_tau (T : TorFlag Xo c) {W : T.X.YY.Opens} (hW : IsAffineOpen W) [IsDomain Γ(T.X.YY, W)]
    {φ : c.F →+* Γ(T.X.YY, W)} (hφ : GlobalTheory.FlagMod.tau hW ≫ flagStr T.X = spMap φ) (k : T.X.F.J)
    (hz : ⊤ ≤ GlobalTheory.FlagMod.tau hW ⁻¹ᵁ T.X.F.U k) {x' : Sp Γ(T.X.YY, W) ⟶ T.Y.X} (hx : GlobalTheory.FlagMod.tau hW ≫ T.X.π = x') :
    ∃ fr : EigFrame T.Y φ x', ∀ τ j, fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (T.X.F.vecAt k _ hz hx τ j)).left := by
  subst hx
  let A : Type := Γ(T.X.YY, W)
  let K : Type := FractionRing A
  letI : Algebra c.F K := ((algebraMap A K).comp φ).toAlgebra
  let z : Sp K ⟶ T.X.YY := spMap (algebraMap A K) ≫ GlobalTheory.FlagMod.tau hW
  have hO : ⊤ ≤ z ⁻¹ᵁ flagOpen T.X := by
    intro s _
    let η : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
    have hs : spMap (algebraMap A K) s = η := by
      refine PrimeSpectrum.ext ?_
      let s' : PrimeSpectrum K := s
      have h0 : s'.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
      show Ideal.comap (algebraMap A K) s'.asIdeal = ⊥
      rw [h0]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective A K)
    obtain ⟨p, hpW, hpO⟩ := (dense_flagOpen T.X).inter_open_nonempty W W.isOpen
      ⟨_, GlobalTheory.FlagMod.tau_le hW le_rfl (Set.mem_univ η)⟩
    obtain ⟨p', rfl⟩ : p ∈ Set.range hW.fromSpec := hW.range_fromSpec.ge hpW
    have hsp : η ⤳ (p' : PrimeSpectrum A) := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    show GlobalTheory.FlagMod.tau hW (spMap (algebraMap A K) s) ∈ flagOpen T.X
    rw [hs]
    exact (hsp.map (GlobalTheory.FlagMod.tau hW).continuous).mem_open (flagOpen T.X).isOpen hpO
  have hr : Set.range (z ≫ T.X.π) ⊆ Set.range T.Y.j := by
    rintro _ ⟨s, rfl⟩
    exact hO (Set.mem_univ s)
  have hf := IsOpenImmersion.lift_fac T.Y.j (z ≫ T.X.π) hr
  refine GlobalTheory.ChartEigFrame.exists_eigFrame_vecAt E H D l Xo c _ _ T.Y T.X A K φ rfl _ k hz
    (IsOpenImmersion.lift T.Y.j (z ≫ T.X.π) hr) ?_ hf.symm
  rw [← openImmersion_comp_structure_eq_generic T.Y, ← Category.assoc, hf, Category.assoc, Category.assoc]
  exact (congrArg (_ ≫ ·) hφ).trans (Spec.map_comp _ _).symm


end DifferentiableLines
end
end

-- bundled from Development.WeilBound.CoreStatements.ProjectiveValuations.FlagModelProjectiveEmbedding
section
noncomputable section

namespace DifferentiableLines.FlagIso

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str pm)
open MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory GlobalTheory.CompHS
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {S : Type} [CommRing S]

theorem step_congr {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {z z' : Sp S ⟶ Z} (e : z = z')
    {x : Sp S ⟶ Y.X} (hx : z ≫ π = x) (hx' : z' ≫ π = x) (σ : E →+* ℂ) (i : ℕ) :
    F.step z hx σ i = F.step z' hx' σ i := by
  subst e; rfl

theorem dense_interior {Z : Scheme.{0}} (π : Z ⟶ Y.X) (h : Dense (genMap π ⁻¹' Set.range Y.jQ)) :
    Dense ((π ⁻¹ᵁ LogKS.interior Y : Z.Opens) : Set Z) := by
  have : IsIso (spMap (RingHom.id c.F)) := by
    show IsIso (Spec.map (𝟙 _))
    infer_instance
  let r := pullback.fst (π ≫ Y.s) (spMap (RingHom.id c.F))
  refine (r.surjective.denseRange.dense_image r.continuous h).mono ?_
  rintro _ ⟨z, ⟨x, hx⟩, rfl⟩
  refine ⟨x, ?_⟩
  rw [Model.j, Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, FlagMod.genMap,
    pullback.lift_fst]

theorem lies_of_step [Algebra c.F S] (X : FlagCover Y) (z : Sp S ⟶ X.YY) (Q : FrPt Xo c S) (k : X.F.J)
    (hk : ⊤ ≤ z ⁻¹ᵁ X.F.U k) (hx : z ≫ X.π = frX Q ≫ Y.j)
    (h : ∀ σ i, initSpan S (frVec Y Q rfl σ) i = X.F.step z hx σ i) : X.F.Lies z Q := by
  have ex : ∀ σ, ∃ b : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧
      ∀ i, frVec Y Q rfl σ i = ∑ j, b j i • X.F.vecAt k z hk hx σ j := fun σ =>
    exists_tri_of_eq (X.F.linearIndependent_vecAt k z hk hx σ) fun i => (h σ i).trans (X.F.step_eq k z hk hx σ i)
  choose U hU hu hv using ex
  exact _root_.GlobalTheory.FlagMod.Frames.lies_of_chart_tri E H Dw l Xo c c.F (RingHom.id c.F) Y X.YY X.π X.F X.top S Q z k hk hx U hU hu hv

theorem step_eq_of_rfl {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {z z' : Sp S ⟶ Z} (hx' : z' ≫ π = z ≫ π)
    (h : ∀ σ i, F.step z' hx' σ i = F.step z rfl σ i) {x : Sp S ⟶ Y.X} (e : z ≫ π = x) (e' : z' ≫ π = x)
    (σ : E →+* ℂ) (i : ℕ) : F.step z' e' σ i = F.step z e σ i := by
  subst e
  exact h σ i

theorem eq_of_step [IsLocalRing S] (X : FlagCover Y) (z z' : Sp S ⟶ X.YY) (hx' : z' ≫ X.π = z ≫ X.π)
    (hi : ⊤ ≤ (z ≫ X.π) ⁻¹ᵁ LogKS.interior Y) (h : ∀ σ i, X.F.step z' hx' σ i = X.F.step z rfl σ i) : z' = z := by
  obtain ⟨_, y, hy, hx⟩ := exists_y _ hi
  obtain ⟨k, hk⟩ := exists_chart_of_isLocalRing X.F.cover z
  obtain ⟨k', hk'⟩ := exists_chart_of_isLocalRing X.F.cover z'
  obtain ⟨Q, hQ⟩ := X.top.exists_chartFr hy hx k hk
  have hl : X.F.Lies z Q := hQ.lies
  have e : z ≫ X.π = frX Q ≫ Y.j := hl.1
  have e' : z' ≫ X.π = frX Q ≫ Y.j := hx'.trans e
  have hl' : X.F.Lies z' Q := lies_of_step X z' Q k' hk' e' fun σ i =>
    (hl.initSpan_eq hk e rfl σ i).trans (step_eq_of_rfl X.F hx' h e e' σ i).symm
  exact (X.rep S Q).unique hl' hl

variable {p : Proj (RingHom.id c.F)} {A : Atlas Y p} {Z : Scheme.{0}} {π : Z ⟶ Y.X}
  {g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)}
  {κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)} [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ)
  (ht : FlagCellFrameChangeTriangular hZ)

theorem Rel.step_eq {X : FlagCover Y} {z : Sp S ⟶ X.YY} {z' : Sp S ⟶ Z} (h : Rel hZ ht X z z') {x : Sp S ⟶ Y.X}
    (hx : z ≫ X.π = x) (hx' : z' ≫ π = x) (σ : E →+* ℂ) (i : ℕ) :
    (cellFrames hZ ht).step z' hx' σ i = X.F.step z hx σ i := by
  subst hx
  exact h.2 σ i


include hZ in
theorem exists_iso (M : FlagModel Y) : ∃ h : M.YY ⟶ Z, IsIso h ∧ h ≫ π = M.π := by
  have ht := _root_.GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular E H Dw l Xo c Y p A Z π g κ hZ
  have hT := _root_.GlobalTheory.FlagMod.FieldFlag.cellFrames_topEigen E H Dw l Xo c Y p A Z π g κ hZ ht
  have hu := _root_.GlobalTheory.FlagMod.FieldFlag.cell_sep E H Dw l Xo c Y p A Z π g κ hZ ht
  obtain ⟨h, hR⟩ := exists_glue (fun S _ _ z z' => Rel hZ ht M.toFlagCover z z')
    (fun S _ _ t z z' h h' => hu S z z' _ h.1 h'.1 fun σ i => (h.2 σ i).trans (h'.2 σ i).symm)
    (exists_local hZ ht M.toFlagCover)
  have hπ : h ≫ π = M.π := hom_ext_local fun S _ _ t => (Category.assoc _ _ _).symm.trans (hR S t).1
  have two : ∀ (S : Type) [CommRing S] [IsLocalRing S] (z z' : Sp S ⟶ M.YY), z' ≫ h = z ≫ h →
      ∃ hx : z' ≫ M.π = z ≫ M.π, ∀ σ i, M.F.step z' hx σ i = M.F.step z rfl σ i := fun S _ _ z z' e => by
    have hx : z' ≫ M.π = z ≫ M.π := by rw [← hπ, ← Category.assoc, e, Category.assoc]
    refine ⟨hx, fun σ i => ?_⟩
    rw [← (hR S z').step_eq hZ ht hx ((hR S z').1.trans hx), ← (hR S z).step_eq hZ ht rfl (hR S z).1]
    exact step_congr _ e _ _ σ i
  refine ⟨h, ?_, hπ⟩
  have := hZ.proper
  have : IsProper (h ≫ π) := hπ ▸ M.proper
  have : IsProper h := IsProper.of_comp h π
  have : LocallyQuasiFinite h := GlobalTheory.locallyQuasiFinite_of_finite_geometric_points h fun Ω _ _ y => by
    rcases isEmpty_or_nonempty {x : Spec (.of Ω) ⟶ M.YY // x ≫ h = y} with h0 | ⟨⟨z, hz⟩⟩
    · infer_instance
    · exact ((M.fin Ω z).subset (t := {z' | z' ≫ h = y})
        (fun z' hz' => two Ω z z' (hz'.trans hz.symm))).to_subtype
  have : IsProper Y.s := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (π ≫ Y.s)
  have : IsReduced M.YY := isReduced_flag M.toFlagCover
  refine isIso_of_normal h hZ.normal (π ⁻¹ᵁ LogKS.interior Y)
    (dense_interior π (_root_.GlobalTheory.FlagMod.FieldFlag.dense_genMap_preimage E H Dw l Xo c Y p A Z π g κ hZ)) ?_ (fun W a a' ha e => ?_) fun w hw => ?_
  · rw [← Scheme.Hom.comp_preimage, hπ]
    exact dense_interior M.π M.dense
  · refine hom_ext_local fun S _ _ t => ?_
    obtain ⟨hx, hs⟩ := two S (t ≫ a) (t ≫ a') (by rw [Category.assoc, Category.assoc, e])
    refine (eq_of_step M.toFlagCover _ _ hx (fun q _ => ?_) hs).symm
    have := ha (t q)
    rw [← hπ]
    exact this
  · let K : Type := Z.residueField w
    let t : Sp K ⟶ Z := Z.fromSpecResidueField w
    have hi : ⊤ ≤ (t ≫ π) ⁻¹ᵁ LogKS.interior Y := fun q _ => by
      have e : t q = w := Scheme.fromSpecResidueField_apply w q
      change π (t q) ∈ LogKS.interior Y
      rw [e]
      exact hw
    obtain ⟨_, y, hy, hx⟩ := exists_y _ hi
    obtain ⟨k', hk'⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover t
    obtain ⟨Q, hQ⟩ := hT.exists_chartFr hy hx k' hk'
    have hl' := hQ.lies
    have hl := M.lies_ptY Q
    obtain ⟨k, hk⟩ := exists_chart_of_isLocalRing M.F.cover (M.ptY Q)
    have e : M.ptY Q ≫ h = t := hu K _ _ _ ((hR K _).1.trans hl.1) hl'.1 fun σ i => by
      rw [(hR K _).step_eq hZ ht hl.1, ← hl.initSpan_eq hk hl.1 rfl, hl'.initSpan_eq hk' hl'.1 rfl]
    let q : Sp K := IsLocalRing.closedPoint K
    refine ⟨M.ptY Q q, ?_⟩
    rw [← Scheme.Hom.comp_apply, e]
    exact Scheme.fromSpecResidueField_apply w _

end DifferentiableLines.FlagIso

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

theorem DifferentiableLines.flag_model_projective_embedding_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : GlobalTheory.FlagMod.LowRank.Proj (RingHom.id c.F)) (A : GlobalTheory.FlagMod.FieldFlag.Atlas Y p) (M' : GlobalTheory.FlagMod.FlagModel Y) (g : ∀ en : GlobalTheory.FlagEmb.En Dw.mult, M'.YY ⟶ PSpace c.F (GlobalTheory.FlagEmb.plN A.N en.1)) (κ : ∀ b, GlobalTheory.FlagEmb.Pm Dw.mult → (Sp (GlobalTheory.FlagEmb.CR Dw.mult (A.V b)) ⟶ M'.YY)), (∀ b w, IsOpenImmersion (κ b w)) → GlobalTheory.FlagMod.FieldFlag.Cells A M'.π g κ → SmoothOfRelativeDimension Dw.dim Y.s → ∀ M : GlobalTheory.FlagMod.FlagModel Y, ∃ h : M.YY ⟶ M'.YY, IsIso h ∧ h ≫ M'.π = M.π := by
  intro E _ _ _ H Dw l Xo c Y p A M' g κ hκ hZ _ M
  exact DifferentiableLines.FlagIso.exists_iso hZ M
end
end

