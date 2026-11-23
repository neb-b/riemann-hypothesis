module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0490
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0504
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupActsByLiftTranslationPrincipalType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0503
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0489

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.ExpDirs

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc ReciprocityTheory.ChartRestriction.G.PullbackSections Filter
open ReciprocityTheory.ChartRestriction.G.Chart (IsUnivChart sp)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem isDerivAt0_of_comb {X : Scheme.{0}} {t : SAB H X} {x : Sp ℂ ⟶ X} {g m : ℕ}
    {e : (Fin g → ℂ) → (Sp ℂ ⟶ t.G.left)} (e0 : e 0 = (1 : Over.mk x ⟶ t.G).left)
    {v : Fin m → (Sp (DualNumber ℂ) ⟶ t.G.left)} {w : Fin m → Fin g → ℂ} (ht : ∀ i, IsTanAtG t x (v i))
    (hv : ∀ i, IsDerivAt0 e (w i) (v i)) {a : Fin m → ℂ} {v' : Sp (DualNumber ℂ) ⟶ t.G.left} (ht' : IsTanAtG t x v')
    (hc : IsCombAtG t x v a v') : IsDerivAt0 e (∑ i, a i • w i) v' := by
  refine ⟨ht'.2.trans e0.symm, fun U h f => ?_⟩
  have hU : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U := fun i => DerLin.le_of_fst_eq ((ht i).2.trans ht'.2.symm) h
  let b : Fin m → TanMod.TanSp x t.G := fun i =>
    TanMod.TanSp.mk (Over.homMk (v i) (ht i).1) (TanMod.smT_zero_of x _ (ht i).2)
  have key : (TanDeriv.evAt v' U h f).snd = ∑ i, a i * (TanDeriv.evAt (v i) U (hU i) f).snd := by
    refine TanDeriv.derivAt_sum b a v' ?_ U h hU f
    obtain ⟨u, hu, rfl⟩ := hc
    have hub : u = fun i => (a i • b i).pt := funext fun i => Over.OverMorphism.ext (hu i)
    subst hub
    rw [List.prod_ofFn, ← TanMod.TanSp.pt_sum]
  refine key.trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  exact congrArg (a i * ·) ((hv i).2 U (hU i) f)

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {σ : c.F →+* ℂ}

theorem frame_basis {x : Sp ℂ ⟶ Z.X} (f : EigFrame Z σ x) {n : ℕ}
    {xc : ∀ m : ℕ, sp (R₀ := ℂ) (ReciprocityTheory.ChartRestriction.G.Chart.JetR ℂ (Fin n) m) ⟶ (Over.pullback x).obj Z.t.G}
    (hx : IsUnivChart _ n xc) (cc : Letter Dw → Fin n → ℂ) (hcc : ∀ z, f.v z.1 z.2 = vec Z.t x xc (cc z)) :
    LinearIndependent ℂ cc ∧ ⊤ ≤ Submodule.span ℂ (Set.range cc) := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨p, hp, hps⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  letI : Algebra c.F ℂ := σ.toAlgebra
  have hE : ∀ τ m, IsEigV (rho hx) (embK c τ) m ↔ ∀ a : 𝓞 E, vec Z.t x xc m ≫ (Z.t.act.act a).left =
      spMap (epsMul (σ (embK c τ a))) ≫ vec Z.t x xc m := fun τ m => by
    rw [vec_eig_iff hx (fun a => σ (embK c τ a)), ReciprocityTheory.ChartRestriction.G.Chart.mem_eigLat_iff]
    rfl
  have hv : ∀ τ, f.v τ = fun i => vec Z.t x xc (cc ⟨τ, i⟩) := fun τ => funext fun i => hcc ⟨τ, i⟩
  have hb : ∀ τ m, IsEigV (rho hx) (embK c τ) m → ∃! a : Fin (Dw.mult τ) → ℂ, m = ∑ i, a i • cc ⟨τ, i⟩ :=
    fun τ m hm => by
      have := f.basis τ _ (vec_tan hx m) ((hE τ m).1 hm)
      rw [hv] at this
      simpa only [LieLocBasis.comb_iff hx] using this
  have he : ∀ τ (a : Fin (Dw.mult τ) → ℂ), IsEigV (rho hx) (embK c τ) (∑ i, a i • cc ⟨τ, i⟩) := fun τ a r => by
    have h1 : ∀ i, IsEigV (rho hx) (embK c τ) (cc ⟨τ, i⟩) := fun i => (hE _ _).2 (hcc ⟨τ, i⟩ ▸ f.eig τ i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, h1 i r, smul_comm]
  refine ⟨Fintype.linearIndependent_iff.2 fun a ha z => ?_, fun m _ => ?_⟩
  · rw [Fintype.sum_sigma] at ha
    have h1 := proj_sum_eig (rho hx) (embK c) α hinj _ (fun τ => he τ fun i => a ⟨τ, i⟩) z.1
    rw [ha, map_zero] at h1
    exact congrFun ((hb z.1 0 fun r => by simp).unique h1 (y₂ := 0) (by simp)) z.2
  · have h1 := LinearMap.congr_fun (sum_proj (rho hx) (embK c) α hinj) m
    rw [LinearMap.sum_apply, Module.End.one_apply] at h1
    rw [← h1]
    refine Submodule.sum_mem _ fun τ _ => ?_
    obtain ⟨a, ha, -⟩ := hb τ _ (eig_of_alpha _ _ α hN τ (proj_eig_alpha (rho hx) _ α hinj p hp hps τ m))
    rw [ha]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem dirs_basis {x : Sp ℂ ⟶ Z.X} (f : EigFrame Z σ x) {g : ℕ} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left)}
    (e0 : e 0 = (1 : Over.mk x ⟶ Z.t.G).left) (h1 : ∀ w, ∃! v, IsTanAtG Z.t x v ∧ IsDerivAt0 e w v)
    (h2 : ∀ v, IsTanAtG Z.t x v → ∃! w, IsDerivAt0 e w v) {W : Letter Dw → Fin g → ℂ}
    (hW : ∀ z, IsDerivAt0 e (W z) (f.v z.1 z.2)) : ∃ b : Module.Basis (Letter Dw) ℂ (Fin g → ℂ), ⇑b = W := by
  classical
  obtain ⟨n, xc, hx⟩ := exists_chart Z.t x
  choose cc hcc using fun z : Letter Dw => vec_exists hx _ (f.tan z.1 z.2)
  obtain ⟨hli, hsp⟩ := frame_basis f hx cc hcc
  choose u hu using fun j : Fin n => (h2 _ (vec_tan hx (Pi.single j 1))).exists
  let T : (Fin n → ℂ) →ₗ[ℂ] (Fin g → ℂ) := Fintype.linearCombination ℂ u
  have hT : ∀ m, IsDerivAt0 e (T m) (vec Z.t x xc m) := fun m =>
    isDerivAt0_of_comb e0 (fun j => vec_tan hx _) hu (vec_tan hx m) ((LieLocBasis.comb_iff hx _ m m).2 (by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]))
  have hbij : Function.Bijective T := by
    refine ⟨fun m m' h => vec_inj hx ((h1 (T m)).unique ⟨vec_tan hx m, hT m⟩ ⟨vec_tan hx m', h ▸ hT m'⟩), fun w => ?_⟩
    obtain ⟨v, ⟨hv, hd⟩, -⟩ := h1 w
    obtain ⟨m, rfl⟩ := vec_exists hx v hv
    exact ⟨m, (h2 _ hv).unique (hT m) hd⟩
  refine ⟨(Module.Basis.mk hli hsp).map (LinearEquiv.ofBijective T hbij), funext fun z => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.mk_apply]
  exact (h2 _ (f.tan z.1 z.2)).unique (hcc z ▸ hT (cc z)) (hW z)

theorem differentiableAt_dir {n g : ℕ} {e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)}
    {ex : ExpMaps Z σ g} (he : IsExpChart e ex) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {B : Set V} (hB : IsOpen B) {x : V → CxPts (genStr Z) σ}
    (hx : IsHolTo B fun b => (x b).1) (hs : ∀ b ∈ B, x b ∈ e.source) {v : V → (Sp (DualNumber ℂ) ⟶ Z.t.G.left)}
    (hv : HolTan B v) {W : V → Fin g → ℂ} (hW : ∀ b ∈ B, IsDerivAt0 (fun w => (ex (x b) w).left) (W b) (v b))
    {b₀ : V} (hb₀ : b₀ ∈ B) : DifferentiableAt ℂ W b₀ := by
  obtain ⟨-, h1, -, h3, h4, h5⟩ := he
  let ε : CxPts (genStr Z) σ → (Fin g → ℂ) → (Sp ℂ ⟶ Z.t.G.left) := fun y w => (ex y w).left
  have hz : DifferentiableAt ℂ (fun b => e (x b)) b₀ :=
    differentiableAt_pi.2 fun k => (h1 k V B x hB hx hs).differentiableAt (hB.mem_nhds hb₀)
  have ht := e.map_source (hs b₀ hb₀)
  have hl : ∀ b ∈ B, ε (e.symm (e (x b))) = ε (x b) := fun b hb => by rw [e.left_inv (hs b hb)]
  refine HolLieFrame.differentiableAt_of_forms _ b₀ fun w hw => ?_
  have hw' : ∀ (U : Z.t.G.left.Opens) (f : Γ(Z.t.G.left, U)), ⊤ ≤ ε (x b₀) 0 ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (ε (x b₀) z) U f) 0 w = 0 := by
    intro U f hU
    have hU' : ⊤ ≤ ε (e.symm (e (x b₀))) 0 ⁻¹ᵁ U := by rwa [hl b₀ hb₀]
    have d := (HolLieFrame.differentiableAt_fderiv (e := fun z => ε (e.symm z)) h4 ht U f hU').comp b₀ hz
    have hn : ∀ᶠ b in 𝓝 b₀, b ∈ B ∧ ⊤ ≤ v b ⁻¹ᵁ U := by
      have hc : ContinuousAt (fun b => (e (x b), (0 : Fin g → ℂ))) b₀ := hz.continuousAt.prodMk continuousAt_const
      filter_upwards [hB.mem_nhds hb₀, hc.preimage_mem_nhds ((h4 U f).1.mem_nhds ⟨⟨ht, trivial⟩, hU'⟩)] with b hb hb'
      have h' : ⊤ ≤ ε (e.symm (e (x b))) 0 ⁻¹ᵁ U := hb'.2
      rw [hl b hb] at h'
      exact ⟨hb, (TangentOrigin.top_le_preimage_iff _ U).2 (by rw [(hW b hb).1]; exact h')⟩
    refine hw (fun b => fderiv ℂ (fun z => valAt' (ε (x b) z) U f) 0) (d.congr_of_eventuallyEq ?_)
      (((hv U f).differentiableAt hn).congr_of_eventuallyEq ?_)
    · filter_upwards [hB.mem_nhds hb₀] with b hb
      simp only [Function.comp_apply, hl b hb]
    · filter_upwards [hn] with b ⟨hb, h⟩
      refine ((hW b hb).2 U h f).symm.trans ?_
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR, dite_eq_left h]
  have d₁ := LocalLift.isDerivAt0_const (ε (x b₀)) w hw'
  have d₀ := LocalLift.isDerivAt0_const (ε (x b₀)) 0 fun _ _ _ => map_zero _
  have e0 : ex (x b₀) 0 = 1 := by simpa using h3 _ (hs b₀ hb₀) 0 0
  exact ((h5 _ (hs b₀ hb₀)).2 _ ⟨(Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Over.w (ex (x b₀) 0))),
    d₁.1.trans (congrArg (·.left) e0)⟩).unique d₁ d₀

theorem exists_inverse {J : Type} [Fintype J] [DecidableEq J] {g : ℕ} (b : Module.Basis J ℂ (Fin g → ℂ)) :
    ∃ Wi : Matrix (Fin g) J ℂ, Matrix.of b * Wi = 1 ∧ Wi * Matrix.of b = 1 := by
  refine ⟨Matrix.of fun j z => b.repr (Pi.single j 1) z, ?_, ?_⟩
  · ext z z'
    have h : b z = ∑ j, b z j • (Pi.single j 1 : Fin g → ℂ) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    have h2 := congrArg (fun w => b.repr w z') h
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.single_apply, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul] at h2
    rw [Matrix.mul_apply, Matrix.one_apply, h2]
    rfl
  · ext j k
    have h := congrFun (b.sum_repr (Pi.single j 1)) k
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Finset.sum_apply, Pi.single_apply, eq_comm] using h

theorem exists_dirs_continuousOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr Z) σ) (Fin n → ℂ)) (ex : ExpMaps Z σ g), IsExpChart e ex → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, (a b).1 ∈ e.source) → ∃ (W : V → Matrix (Letter Dw) (Fin g) ℂ) (Wi : V → Matrix (Fin g) (Letter Dw) ℂ), ContinuousOn W B ∧ ContinuousOn Wi B ∧ ∀ b ∈ B, Dirs (a b) (fun w => (ex (a b).1 w).left) (W b) ∧ W b * Wi b = 1 ∧ Wi b * W b = 1 := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ n g e ex he V _ _ _ B a hB ha hs
  have h5 := fun b hb => he.2.2.2.2.2 _ (hs b hb)
  choose! W hW using fun b hb (z : Letter Dw) => ((h5 b hb).2 _ ((a b).2.tan z.1 z.2)).exists
  have hbas : ∀ b ∈ B, ∃ bs : Module.Basis (Letter Dw) ℂ (Fin g → ℂ), ⇑bs = W b := fun b hb => by
    have e0 : ex (a b).1 0 = 1 := by simpa using he.2.2.2.1 _ (hs b hb) 0 0
    exact dirs_basis (a b).2 (e := fun w => (ex (a b).1 w).left) (congrArg (·.left) e0) (h5 b hb).1 (h5 b hb).2 (hW b hb)
  have hinv : ∀ b ∈ B, ∃ Wi : Matrix (Fin g) (Letter Dw) ℂ, Matrix.of (W b) * Wi = 1 ∧ Wi * Matrix.of (W b) = 1 :=
    fun b hb => by
      obtain ⟨bs, h⟩ := hbas b hb
      rw [← h]
      exact exists_inverse bs
  choose! Wi hWi using hinv
  have hd : ∀ b ∈ B, ∀ z, DifferentiableAt ℂ (fun b => W b z) b := fun b hb z =>
    differentiableAt_dir he hB ha.1 hs (ha.2 z.1 z.2) (fun b hb => hW b hb z) hb
  refine ⟨fun b => Matrix.of (W b), Wi, fun b hb => ContinuousAt.continuousWithinAt ?_,
    fun b hb => ContinuousAt.continuousWithinAt ?_, fun b hb => ⟨hW b hb, hWi b hb⟩⟩
  · exact continuousAt_pi.2 fun z => (hd b hb z).continuousAt
  · obtain ⟨bs, -⟩ := hbas b hb
    let q : Fin g ≃ Letter Dw := (Pi.basisFun ℂ (Fin g)).indexEquiv bs
    refine continuousAt_pi.2 fun j => continuousAt_pi.2 fun z => ?_
    have := HolFrameMatrix.differentiableAt_of_mul_eq_one (fun b => (Wi b).submatrix id q)
      (fun b => (Matrix.of (W b)).submatrix q id) b (fun i k => differentiableAt_pi.1 (hd b hb (q i)) k) (by
        filter_upwards [hB.mem_nhds hb] with b' hb'
        rw [Matrix.submatrix_mul_equiv, (hWi b' hb').2]
        rfl) j (q.symm z)
    simpa using this.continuousAt

end GlobalTheory.ShFam.Hor.ExpDirs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivLift
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Mult
open GlobalTheory.RealGeo GlobalTheory.OneMapAll GlobalTheory.AdTh

namespace GlobalTheory.Mem.R3.Rw.GeoTies

theorem eq_of_span {H ι X : Type} [AddCommGroup H] [Module ℂ H] {M : ι → Type} [∀ t, AddCommGroup (M t)] [∀ t, Module ℂ (M t)]
    (θ : H →ₗ[ℂ] ((∀ t, M t) →ₘₗ[ℂ] (X → ℂ))) (v : ∀ t, M t) (a b : X) (c : ℂ) {S : Set H} (hS : Submodule.span ℂ S = ⊤)
    (h : ∀ y ∈ S, θ y v a = c * θ y v b) (y : H) : θ y v a = c * θ y v b := by
  have hy : y ∈ Submodule.span ℂ S := hS ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => simp
  | add y y' _ _ h h' =>
    simp only [map_add (f := _), add_apply, Pi.add_apply]
    linear_combination h + h'
  | smul a y _ h =>
    simp only [map_smul, smul_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination a * h

theorem span_image {H H' : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup H'] [Module ℂ H'] (e : H ≃ₗ[ℂ] H') {S : Set H}
    (hS : Submodule.span ℂ S = ⊤) : Submodule.span ℂ (e '' S) = ⊤ := by
  have := congrArg (Submodule.map (e : H →ₗ[ℂ] H')) hS
  rwa [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at this

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section One

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}

def adOver (O : OMDat C R i Tp tup) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c')
    (g : GA D (Wc D i)) : ℂ :=
  cc (O.dict g).1 * (O.mu g * rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) f (O.dict g).1 (O.dict g).2)

theorem adOver_of_isBC (O : OMDat C R i Tp tup) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) {m : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} {as : Fin m → O.c'.F} {fs : Fin m → Rul (C.Q.Xo ((i : ℕ) + 1)) C.Q.c}
    (h : IsBC O.hle f as fs) (g : GA D (Wc D i)) : adOver O cc f g = ∑ k, (as k : ℂ) * O.phi cc (fs k) g := by
  have h2 := GlobalTheory.PhaseRational.rdU_of_isBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') h (O.dict g).1 (O.dict g).2
  refine (congrArg (fun w => cc (O.dict g).1 * (O.mu g * w)) h2).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show cc _ * (O.mu _ * ((as k : ℂ) * _)) = (as k : ℂ) * (cc _ * O.mu _ * _)
  ring

theorem adOver_act (O : OMDat C R i Tp tup) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} (hn : κ.n = (Vc D i).rank)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2) {cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ} (hE : O.EquivAt κ cc)
    {z : G} {k : GA D (Wc D i)} (hk : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z) k)
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ cuspOver O κ) (g : GA D (Wc D i)) :
    adOver O cc (actLev O.c' O.lev2 z f) g =
      (∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG z PP)) : ℂˣ) : ℂ)) * adOver O cc f (g * k) := by
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).2 _ (C.U ((i : ℕ) + 1)) _ _ f hf
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hact).2 _ _ z m as fs f ((mem_cusp _ _ _ _ _ _).1 hf).1
    (fun l => ((mem_cusp _ _ _ _ _ _).1 (hfs l)).1) hBC
  rw [adOver_of_isBC O cc h1, adOver_of_isBC O cc hBC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [(hE z k hk (fs l) (by rw [hn]; exact hfs l)).2 g]
  ring

end One

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {i : Fin D.R.m}

def LiftIsSum (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : (R.MW i (sg0 D A)).Vec)
    (cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (z : G) (ζ : ℂ) (y : (R.HV i A.μ0).H) : Prop :=
  ∃ h J x f, RepsR R i A.μ0 h (O.bad ()) J (O.Lh ()) (O.gam ()) (O.vol ()) ∧ Place R i A.μ0 h O.c0' y x ∧
    f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank ∧ IsSum O () x f ∧
    ∀ q : AutQ (Wc D i), R.thF i A.μ0 y v₀ q.out =
      ζ * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * adOver O cc (actLev O.c' O.lev2 z f) q.out


set_option maxHeartbeats 2000000 in
theorem oneMapOf_of_span (hR : PreChar R) (hchi : R.grp_chiW) (hT : Formalism.IndefR.FWT.TieIn T R κ v₀)
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0))
    (hF : O.c'.F = D.what₂.embLL.toRatAlgHom.fieldRange)
    (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0)) {cE : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ}
    (hU : ∀ k, ‖cE k‖ = 1) (hE : O.EquivAt (κ i) cE) {z : G} (hz : z ∈ Subgroup.center G) {ζ : ℂ}
    (hζL : ζ ∈ D.what₂.embLL.toRatAlgHom.fieldRange) (hζ : ∃ m : ℕ, 0 < m ∧ ζ ^ m = 1)
    (hS : Submodule.span ℂ {y | LiftIsSum O (κ i) (v₀ i (sg0 D A)) cE z ζ y} = ⊤) :
    O.OneMapOf (κ i) (v₀ i (sg0 D A)) cE 1 := by
  have hio : IoExt R := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A T.Q.c.F R hR.lev hR.fam hR.models hR.thP
  have hn : (κ i).n = (Vc D i).rank :=
    (hT.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  obtain ⟨cc₀, -, u, -, -, hser, -⟩ := exists_ccIs_equivAt_serOf_tie D G Pl0 T0 A T R κ v₀ hR hT hio i _ _ O hP
  generalize u • cc₀ = cc at hser
  have hex := GlobalTheory.ClassSumRule.exists_cusp_isThClsD_ofPre GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R κ v₀ hR hT i _ _ O hP ()
  obtain ⟨k, hk, -⟩ := hP.lift.lev z
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℝ) := ⟨_, rfl⟩
  obtain ⟨χ, hχ⟩ : ∃ χ : ℂ, χ = ∏ PP : R.Pg, ((R.chi ((i : ℕ) + 1) PP.1 (Matrix.GeneralLinearGroup.det (R.eG z PP)) : ℂˣ) : ℂ) :=
    ⟨_, rfl⟩
  have hcc : ∀ c, cc c ≠ 0 := fun c => norm_ne_zero_iff.1 ((hser.1 c).trans_ne one_ne_zero)
  have key : ∀ h J x f y, RepsR R i A.μ0 h (O.bad ()) J (O.Lh ()) (O.gam ()) (O.vol ()) → Place R i A.μ0 h O.c0' y x →
      f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA (κ i)) (Vc D i).rank → IsSum O () x f → ∀ g,
      ζ * s * adOver O cE (actLev O.c' O.lev2 z f) g = ζ * χ * (cE (O.dict (g * k)).1 / cc (O.dict (g * k)).1) *
        R.thF i A.μ0 y (v₀ i (sg0 D A)) (g * k) := by
    intro h J x f y hr hy hf hx g
    obtain ⟨f₁, hf₁, hx₁⟩ := hex x
    have e : f = f₁ := isSum_unique hP () hf ((mem_cusp _ _ _ _ _ _).1 hf₁).1 hx hx₁
    have h1 := adOver_act O hn hP.act.1 hE hk (e ▸ hf₁ : f ∈ cuspOver O (κ i)) g
    have h2 := (one_mul _).symm.trans (hser.2.2 () h J hr y x hy f hf hx (g * k))
    rw [h1, h2, ← hχ, ← hs, adOver]
    have := hcc (O.dict (g * k)).1
    field_simp
  have all : ∀ y (q : AutQ (Wc D i)), R.thF i A.μ0 y (v₀ i (sg0 D A)) q.out =
      ζ * χ * (cE (O.dict (q.out * k)).1 / cc (O.dict (q.out * k)).1) * R.thF i A.μ0 y (v₀ i (sg0 D A)) (q.out * k) := by
    intro y q
    refine eq_of_span (R.thF i A.μ0) _ _ _ _ hS (fun y hy => ?_) y
    obtain ⟨h, J, x, f, h1, h2, h3, h4, h5⟩ := hy
    rw [h5 q, ← hs]
    exact key h J x f y h1 h2 h3 h4 _
  have hid : GlobalTheory.PhaseRational.IdentityAt O (κ i) cE 1 := by
    obtain ⟨h, J, hr, -, hA, hPl⟩ := (hP.tuple ()).reps
    refine ⟨hU, norm_one, z, hz, fun t => ⟨ζ, hζL, hζ, fun x hx => ⟨hex x, fun f hf hc q => ?_⟩⟩⟩
    obtain ⟨x₀, hx₀⟩ := (hPl x).1 hx
    have h1 := (all _ q).trans (key h J x f _ hr hx₀ hf hc q.out).symm
    rw [one_mul, hA _ x hx₀]
    refine h1.trans ?_
    rw [hs, mul_right_comm ζ (cE _), mul_assoc (ζ * _) (cE _)]
    rfl
  exact ⟨hE, ⟨hF.ge, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hP.act.1).2, hid⟩,
    GlobalTheory.PhaseRational.phRat_of_identity O (κ i) _ cE 1 () rfl hF hP hT.laws.toLawsM (hT.kap i (D.eTau.symm 1)).2.2 hchi
      hR.thP.thF_mem hR.thP.thG hE hid⟩


set_option maxHeartbeats 2000000 in
theorem lift_of_oneMapOf (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
    {ι x₀} (hP : O.Pins κ v₀ ι x₀) {cE : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ} (h : O.OneMapOf κ v₀ cE 1) :
    ∃ z ∈ Subgroup.center G, ∃ ζ ∈ D.what₂.embLL.toRatAlgHom.fieldRange, (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ∃ h J, RepsR R i A.μ0 h (O.bad ()) J (O.Lh ()) (O.gam ()) (O.vol ()) ∧ ∀ y₀ : A.fam.amb.FL i A.μ0, ∃ x f,
        Place R i A.μ0 h O.c0' (jVx R i A.μ0 y₀) x ∧ f ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank ∧ IsSum O () x f ∧
        ∀ q : AutQ (Wc D i), R.thF i A.μ0 (jVx R i A.μ0 y₀) v₀ q.out =
          ζ * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * adOver O cE (actLev O.c' O.lev2 z f) q.out := by
  obtain ⟨-, ⟨-, -, -, -, -, z, hz, h1⟩, -⟩ := h
  obtain ⟨ζ, hζL, hζ, h1⟩ := h1 ()
  obtain ⟨h, J, hr, hPx, hA, hPl⟩ := (hP.tuple ()).reps
  refine ⟨z, hz, ζ, hζL, hζ, h, J, hr, fun y₀ => ?_⟩
  obtain ⟨x, hx⟩ := hPx y₀
  obtain ⟨⟨f, hf, hc⟩, h2⟩ := h1 x ((hPl x).2 ⟨y₀, hx⟩)
  have hf' := ((mem_cusp _ _ _ _ _ _).1 hf).1
  refine ⟨x, f, hx, hf', hc, fun q => ?_⟩
  have h3 := h2 f hf' hc q
  rw [one_mul, hA _ x hx, mul_right_comm ζ (cE _), mul_assoc (ζ * _) (cE _)] at h3
  exact h3

theorem exists_equiv_lift {V : HSp D} {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel V S'} (hM : ModelSame M M')
    {Γ W W' : Type} {nW : NormedAddCommGroup W} {nW' : NormedAddCommGroup W'} {iW : InnerProductSpace ℂ W}
    {iW' : InnerProductSpace ℂ W'} (h1 : HEq W' W) (h2 : HEq nW' nW) (h3 : HEq iW' iW) {H : HMod (Γ → W)} {H' : HMod (Γ → W')}
    (hH : HEq H' H) {θ : H.H →ₗ[ℂ] MMap M} {θ' : H'.H →ₗ[ℂ] MMap M'} (hθ : HEq θ' θ) {v : M.Vec} {v' : M'.Vec} (hv : HEq v' v) :
    ∃ e : H.H ≃ₗ[ℂ] H'.H, ∀ y, HEq (e y) y ∧ θ' (e y) v' = θ y v := by
  cases h1; cases h2; cases h3; cases hH
  cases M; cases M'
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hM
  dsimp only at a1 a2 a3 a4 a5 a6 a7
  cases a1; cases a2; cases a3; cases a4; cases a5; cases a6; cases a7
  have e1 : θ' = θ := eq_of_heq hθ
  have e2 : v' = v := eq_of_heq hv
  exact ⟨LinearEquiv.refl _ _, fun y => ⟨HEq.rfl, by rw [e1, e2]; rfl⟩⟩

theorem adOver_rulBC {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type}
    {tup : Tp → T0} (O : OMDat C R i Tp tup) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff C.Q.l) (hle : O.c'.F ≤ c.F) (h₃ : C.Q.c.F ≤ c.F) {lev} (hlev : lev = O.lev)
    (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (z : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ sec _ O.c' a n) (g : GA D (Wc D i)) :
    cc (O.dict g).1 * (O.mu g * rdU (unfBC h₃ (C.U ((i : ℕ) + 1)) (inC c))
      (actLev c (fun g => (lev g, LinearMap.id)) z (GlobalTheory.FieldBC.rulBC hle f)) (O.dict g).1 (O.dict g).2) =
      adOver O cc (actLev O.c' O.lev2 z f) g := by
  subst hlev
  obtain ⟨m, as, fs, hfs, h⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).1 a n f hf
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hact).2 a n z m as fs f hf hfs h
  have h2 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ h₃ _ _ hact).2 a n z m _ fs _ (GlobalTheory.FieldBCModel.rulBC_mem_sec hle hf) hfs
    (isBC_rulBC_trans O.hle hle h₃ hf h)
  have e1 := GlobalTheory.PhaseRational.rdU_of_isBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') h1 (O.dict g).1 (O.dict g).2
  have e2 := GlobalTheory.PhaseRational.rdU_of_isBC h₃ (C.U ((i : ℕ) + 1)) (inC c) h2 (O.dict g).1 (O.dict g).2
  exact congrArg (fun w => cc (O.dict g).1 * (O.mu g * w)) (e2.trans e1.symm)

end GlobalTheory.Mem.R3.Rw.GeoTies

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmPinsEnl
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmExt


set_option maxHeartbeats 4000000 in
theorem exists_omPins_enl : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
    (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
    ∀ (core' : CoreJ (w'.st Z').toD7) [Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL],
      HEq core'.Q.H z.core.Q.H → HEq core'.Q.l z.core.Q.l → HEq core'.Q.c z.core.Q.c → HEq core'.Q.Dw z.core.Q.Dw →
      HEq core'.Q.Xo z.core.Q.Xo → HEq core'.x₀ z.core.x₀ → HEq core'.iota z.core.iota →
    ∀ {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
      (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F)
      (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
      Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
      BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (κ' : ∀ i : Fin (w'.st Z').toD7.R.m, WeightFamilies.Wt (w'.st Z').toD7 ((i : ℕ) + 1))
      (v₀' : ∀ (i : Fin (w'.st Z').toD7.R.m) (σ : (w'.st Z').toD7.what₂.LL →+* ℂ), (R'.MW i σ).Vec),
      TieIn core' R'.toRealDat κ' v₀' →
      ∃ O' : ∀ i', OMDat core'.toCore R'.toRealDat i' Unit (fun _ => (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A.μ0),
        (∀ i', OMPins core' R'.toRealDat κ' v₀' O' i') ∧
        ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' → HEq (O' i').lev (z.geo.O i).lev ∧
          IsBCOf (O' i') (v₀' i' (sg0 _ (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A)) (z.geo.O i)
            (z.geo.v₀ i (sg0 _ (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)) (z.geo.κ i) (iotaW z.core i)
            (z.core.x₀ ((i : ℕ) + 1) (z.geo.O i).s0)
            (∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i
              (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x = 0) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hp hS core' alg' eH el ec eD eX ex eι Xg tr R' cG' hP hL hB hW κ' v₀' ht
  have hc := _root_.GlobalTheory.Mem.R3.Rw.OmCoef.exists_coefFam_ext z hE hf hp hS R' cG' hP hL hB hW
  have a1 : HEq R'.C.mu0 f'.mu0 ∧ HEq R'.C.eta f'.eta := by
    have e := hL.C
    rw [w'.C_eq] at e
    rw [e]
    exact ⟨HEq.rfl, HEq.rfl⟩
  have a2 : HEq z.R.C.mu0 f.mu0 ∧ HEq z.R.C.eta f.eta := by
    have e := z.lev.C
    rw [w.C_eq] at e
    rw [e]
    exact ⟨HEq.rfl, HEq.rfl⟩
  obtain ⟨-, -, eβW, -, -, -, eβV, -, -, ePg, eG, -, hcV, -⟩ := hW
  have hcV' := fun i i' hi => (⟨(hcV i i' hi).1, (hcV i i' hi).2.2.1, (hcV i i' hi).2.2.2.1⟩ : _ ∧ _ ∧ _)
  have h1 := hP.char.base.lev
  have h2 := hP.char.base.models
  have h3 := hP.char.base.fam.tie
  clear hcV hP hL hB hS
  obtain ⟨hPre, -, -, hLL⟩ := hE
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hPre
  subst hPre
  obtain rfl := eq_of_heq hf
  obtain ⟨px', I', ok', C_eq', S_eq', xi_range', pins', l', l0', δ', exact', fld', val'⟩ := w'
  dsimp only at hp
  obtain rfl := eq_of_heq hp
  have key := fun i => exists_bc_stages (w.st Z) _ ((by with_unfolding_all exact ((Eq.refl B.toPre) :))) hLL z.core core' z.R.toRealDat R'.toRealDat eH el ec eD eX ex eι
    ePg eβV eβW eG (a1.1.trans a2.1.symm) (a1.2.trans a2.2.symm) z.pins.char.base.lev z.pins.char.base.models.HV z.geo.fw.kap h1 h2 h3 ht
    i i rfl (hcV' i i rfl).1 (hcV' i i rfl).2.1 (hcV' i i rfl).2.2 (z.geo.O i) (z.geo.pins i).1 (z.geo.pins i).2 _ (hc i i rfl)
  choose O' k1 k2 k3 using key
  refine ⟨(by with_unfolding_all exact (O' :)), fun i => (by with_unfolding_all exact ((And.intro (k1 i) (k2 i)) :)), fun i i' hi => ?_⟩
  obtain rfl : i = i' := Fin.ext hi
  exact (by with_unfolding_all exact ((And.intro (k3 i).lev (k3 i)) :))

end GlobalTheory.Mem.R3.Rw.OmExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingGlueLowerUnitriangularBlocksStatement
section
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePreserving_glueLowerUnitriangularBlocks : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → MeasurePreserving (glue e) volume volume := by
  first | exact @GlobalTheory.FlagFibre.measurePreserving_glue | exact GlobalTheory.FlagFibre.measurePreserving_glue | (intros; apply GlobalTheory.FlagFibre.measurePreserving_glue <;> assumption)
end

