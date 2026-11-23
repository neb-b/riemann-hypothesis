module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0061
public import Formalism.HermitianCurvature.Bundle0008
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SabBaseChangeStIffFree
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SabPullCompare

variable {S S' : Scheme.{0}}

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem lbIso_cubeLB {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L M : LB G.left} (h : LBIso L M) : LBIso (cubeLB G x L) (cubeLB G x M) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨_, DVR.linCombIso_isGen w hw _ _⟩

theorem cubeLB_isLB {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L : LB G.left} (h : L.IsLB) : (cubeLB G x L).IsLB := DVR.linComb_isLB _ h _ _

end GlobalTheory.SabPullCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsDiscreteSeriesGlModule
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

private lemma inv_conj_mul_conj {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q)
    (A B : Matrix (Fin n) (Fin n) ℂ) : (Q⁻¹ * A * Q) * (Q⁻¹ * B * Q) = Q⁻¹ * (A * B) * Q := by
  have h : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q ((Matrix.isUnit_iff_isUnit_det Q).mp hQ)
  calc (Q⁻¹ * A * Q) * (Q⁻¹ * B * Q) = Q⁻¹ * A * (Q * Q⁻¹) * B * Q := by
        simp only [Matrix.mul_assoc]
    _ = Q⁻¹ * (A * B) * Q := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]

private lemma single_one_mul_single_one_jet_harmonics {n : ℕ} (a b c d : Fin n) :
    Matrix.single a b (1 : ℂ) * Matrix.single c d 1 = if b = c then Matrix.single a d 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Matrix.single_mul_single_same, mul_one]
  · simp [h]

theorem conj_single_comm {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) (a b c d : Fin n) :
    (Q⁻¹ * Matrix.single a b 1 * Q) * (Q⁻¹ * Matrix.single c d 1 * Q) -
      (Q⁻¹ * Matrix.single c d 1 * Q) * (Q⁻¹ * Matrix.single a b 1 * Q) =
    (if b = c then Q⁻¹ * Matrix.single a d 1 * Q else 0) -
      (if d = a then Q⁻¹ * Matrix.single c b 1 * Q else 0) := by
  rw [inv_conj_mul_conj Q hQ, inv_conj_mul_conj Q hQ, ← Matrix.sub_mul, ← Matrix.mul_sub,
    single_one_mul_single_one_jet_harmonics, single_one_mul_single_one_jet_harmonics]
  split_ifs <;> simp [Matrix.mul_sub, Matrix.sub_mul]

theorem smooth_gl_module : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDS ε mu → ∀ Q : Mx k r, IsUnit Q → ∃ E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub), R.IsE Q E ∧ Formalism.REAL.GlRel E := by
  intro hK k r ε mu R hDS Q hQ
  obtain ⟨hmem, hlin, hadd, -, hbr, -⟩ := GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hDS
  have h0 : (0 : R.H) ∈ R.sm := R.smSub.zero_mem
  have hz : ∀ Y, R.dC Y 0 = 0 := fun Y => by
    have h := hlin Y 1 0 h0 0 h0
    simpa using h
  have hY0 : ∀ v ∈ R.sm, R.dC 0 v = 0 := fun v hv => by
    have h := hadd 0 0 1 v hv
    simpa using h
  have hsub : ∀ Y Z, ∀ v ∈ R.sm, R.dC (Y - Z) v = R.dC Y v - R.dC Z v := fun Y Z v hv => by
    have h := hadd Z (Y - Z) 1 v hv
    simp only [one_smul, add_sub_cancel] at h
    rw [h, add_sub_cancel_left]
  let E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub := fun a b =>
    { toFun := fun v => ⟨R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v, hmem _ v v.2⟩
      map_add' := fun v w => Subtype.ext (by simpa using hlin _ 1 v v.2 w w.2)
      map_smul' := fun c v => Subtype.ext (by simpa [hz] using hlin _ c v v.2 0 h0) }
  refine ⟨E, fun a b v => rfl, ?_⟩
  intro a b c d
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  have lhs : (((E a b * E c d - E c d * E a b) v : R.smSub) : R.H) =
      R.dC ((Q⁻¹ * Matrix.single a b 1 * Q) * (Q⁻¹ * Matrix.single c d 1 * Q) -
        (Q⁻¹ * Matrix.single c d 1 * Q) * (Q⁻¹ * Matrix.single a b 1 * Q)) v := by
    rw [← hbr _ _ v v.2]; rfl
  rw [lhs, conj_single_comm Q hQ a b c d, hsub _ _ v v.2]
  split_ifs <;> simp [E, hY0 v v.2]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarProjectionSplitCasimirRaisingLast
section
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr

namespace GlobalTheory

theorem starProjection_splitCasimirStd_last : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (Et : Fin (n + 1) → Fin (n + 1) → Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (Om : Module.End ℂ (PiLp 2 (fun _ : Fin (n + 1) => V))) (β : ℂ) (L : Fin (n + 1) → ℤ) (l : Fin (n + 1)), Hyp E β L → (∀ a b x y, inner ℂ (E a b x) y = inner ℂ x (E b a y)) → (∀ a b y c, Et a b y c = E a b (y c) + if c = a then y b else 0) → (∀ y b, Om y b = ∑ c, E c b (y c)) → ∀ (M : Fin n → ℤ) (v : V), v ∈ CapSp (subA E) (shf β M) → (Module.End.eigenspace Om (β + L l + 0)).starProjection (PiLp.single 2 (Fin.last n) v) (Fin.last n) = (GlobalTheory.WigSh.wP L M l : ℂ) • v := by
  intro V _ _ _ n E Et Om β L l hH hadj hEt hOm M v hv
  have hq : ∀ w v, qdet E w v = (∏ j, (w + shf β L j)) • v := hH.cap
  obtain ⟨K, hK, hK'⟩ := comatrix_last_row_inverts_casimir V n E Om (shf β L) hH.gl hq hOm
  obtain ⟨-, -, hsym, -⟩ := tensorStd_rel_adjoint_splitCasimir V n E Et Om hH.gl hadj hEt hOm
  have hev := splitCasimirStd_eigenvalue V n E Et Om (shf β L) hH.gl hadj hq hEt hOm
  have hinj : Function.Injective (shf β L) := by
    intro a b h
    apply hH.anti.injective
    have h' : (L a : ℂ) = (L b : ℂ) := add_left_cancel h
    exact_mod_cast h'
  have hcont : Continuous fun u : ℂ => cpol (shf β M) (u - 1) := by
    unfold cpol
    fun_prop
  have h := ev_starProjection_eigenspace_eq_residue (PiLp 2 (fun _ : Fin (n + 1) => V)) V (n + 1)
    (shf β L) 0 Om (PiLp.projₗ 2 (fun _ : Fin (n + 1) => V) (Fin.last n)) K
    (fun u : ℂ => cpol (shf β M) (u - 1)) (PiLp.single 2 (Fin.last n) v) v l hinj hsym hev hK hcont
    (fun u => (hK' u v).trans (mem_CapSp.1 hv (u - 1)))
  refine Eq.trans h ?_
  congr 1
  simp only [cpol, shf, WigSh.wP]
  push_cast
  congr 1
  · exact Finset.prod_congr rfl fun j _ => by ring
  · exact Finset.prod_congr rfl fun j _ => by ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.PowGerm.starRing_ext_of_star {R : Type*} [NonUnitalNonAssocSemiring R] (s t : StarRing R)
    (h : ∀ a : R, s.toStarMul.toInvolutiveStar.toStar.star a =
      t.toStarMul.toInvolutiveStar.toStar.star a) :
    s = t := by
  rcases s with @⟨@⟨@⟨@⟨s⟩, _⟩, _⟩, _⟩
  rcases t with @⟨@⟨@⟨@⟨t⟩, _⟩, _⟩, _⟩
  obtain rfl : s = t := funext h
  rfl


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.PowGerm.starSt : _root_.GlobalTheory.PowGerm.StarSt := by
  unfold _root_.GlobalTheory.PowGerm.StarSt
  intro E _ _ _ H inst h
  exact _root_.GlobalTheory.PowGerm.starRing_ext_of_star _ _ fun a => (h a).trans rfl

end GlobalTheory.PowGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TruncationFramesLocalSeries
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PowGerm

namespace GlobalTheory.LinkEps

theorem linkEps : LinkEpsSt := by
  intro E _ _ _ H V _ _ t d FT act ph1 ph2 sy ad tg xT eT wPT hch _ _ htr j hj
  have hL := t.PP.isLB
  have hi0 : (e0 t (𝟙 (Sp V))) ⁻¹ᵁ t.PP.L.U j = ⊤ := by
    refine top_unique fun y _ => ?_
    exact hj (x := (toUnit (overAt (𝟙 (Sp V)) V)).left y) trivial
  have hW : ∀ m, LB.wchart t.PP.L
      (cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)]) (fun _ => j) = ⊤ := fun m =>
    wchart_top t (𝟙 (Sp V)) d j hi0 _ fun i => by
      rw [vec2 (fun i => jptG t (𝟙 (Sp V)) d xT m i)]; exact jpt_aug hch m i
  have hU : ∀ m, ∃ u : Γ((jOG (𝟙 (Sp V)) d m 2).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (jOG (𝟙 (Sp V)) d m 2).left) (z : Z)
      (J : (Z ⟶ t.G.left) → t.PP.L.ι),
      (∀ I, J (r ≫ cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)] I) = j) →
      (val (eT m) r z J).val = gs r z ⊤ u := by
    intro m
    refine ⟨((jOG (𝟙 (Sp V)) d m 2).left.presheaf.map (homOfLE (hW m).ge).op).hom ((eT m).s (fun _ => j)).val,
      fun Z r z J hJ => ?_⟩
    exact (congrArg Units.val (val_of (eT m) r z J (fun _ => j) hJ)).trans
      ((gs_unit r z _ ((hW m).ge trivial) _).symm.trans (gs_res r z (hW m).ge trivial _).symm)
  choose U hU using hU
  have hUc : ∀ m, U m = (ρn (𝟙 (Sp V)) d 2 m).left.appTop.hom (U (m + 1)) := by
    intro m
    refine fn_ext (V := ⊤) fun y _ => ?_
    obtain ⟨J, hJ, hJi⟩ := exists_good t.PP.L hL y
      (cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)]) (fun _ => j)
      (fun _ _ _ => rfl) (fun I => Set.mem_iInter.1 ((hW m).ge (Set.mem_univ y)) I)
    have hmor : ∀ I : ULift (Finset (Fin 2)), (𝟙 _ ≫ (ρn (𝟙 (Sp V)) d 2 m).left) ≫
        cφG t ![jptG t (𝟙 (Sp V)) d xT (m + 1) (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT (m + 1) (1 : Fin 2)] I =
        cφG t ![jptG t (𝟙 (Sp V)) d xT m (0 : Fin 2), jptG t (𝟙 (Sp V)) d xT m (1 : Fin 2)] I := by
      intro I
      rw [Category.id_comp, vec2 (fun i => jptG t (𝟙 (Sp V)) d xT (m + 1) i),
        vec2 (fun i => jptG t (𝟙 (Sp V)) d xT m i)]
      simp only [cφG, ← Over.comp_left]
      refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
      exact congrArg (fun f => psum t.G f I.down) (funext fun i => jpt_trunc hch m i)
    have e0' := hU m _ (𝟙 _) y J (fun I => (congrArg J (Category.id_comp _)).trans (hJi I))
    have e1 := hU (m + 1) _ (𝟙 _ ≫ (ρn (𝟙 (Sp V)) d 2 m).left) y J (fun I => (congrArg J (hmor I)).trans (hJi I))
    have e2 := (val_pull hJ (eT (m + 1)) _ _).symm.trans (val_corr hJ (htr m) (𝟙 _))
    have e3 := gs_pull (𝟙 _) (ρn (𝟙 (Sp V)) d 2 m).left y ⊤ trivial (U (m + 1))
    exact e0'.symm.trans ((congrArg Units.val e2).symm.trans (e1.trans e3.symm))
  choose a ha using fun m => (⟨_, congrArg (fun f => CommRingCat.Hom.hom f (U m))
    (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of (Jet V (Fin 2 × Fin d) m))))⟩ :
      ∃ b, toΓ (Jet V (Fin 2 × Fin d) m) b = U m)
  have hac : ∀ m, (jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _) (a (m + 1)) = a m := by
    intro m
    apply toΓ_injective
    rw [ha m, hUc m, ← ha (m + 1)]
    exact congrArg (fun f => CommRingCat.Hom.hom f (a (m + 1)))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ((jetTrunc : Jet V (Fin 2 × Fin d) (m + 1) →ₐ[V] _) :
        Jet V (Fin 2 × Fin d) (m + 1) →+* Jet V (Fin 2 × Fin d) m)))
  obtain ⟨f, hf⟩ := exists_ps_of_jets a hac
  refine ⟨f, fun m y J _ hJ => ?_⟩
  rw [hf m, ha m]
  exact hU m _ (𝟙 _) y J hJ

end GlobalTheory.LinkEps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalJetsPowerProduct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PowGerm.UnivPow

variable {V : Type} [CommRing V]

theorem homAt_comp {A B C : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] [CommRing C] [Algebra V C]
    (f : A →ₐ[V] B) (g : B →ₐ[V] C) :
    Formalism.L2.Pj.homAt (𝟙 (Sp V)) g ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (g.comp f) := by
  apply Over.OverMorphism.ext
  show Spec.map (CommRingCat.ofHom (g : B →+* C)) ≫ Spec.map (CommRingCat.ofHom (f : A →+* B)) =
    Spec.map (CommRingCat.ofHom ((g.comp f : A →ₐ[V] C) : A →+* C))
  rw [← Spec.map_comp]
  rfl

theorem jet_ext {κ : Type} {m : ℕ} {B : Type} [CommRing B] [Algebra V B] (f g : Jet V κ m →ₐ[V] B)
    (h : ∀ i, f (Ideal.Quotient.mk _ (MvPolynomial.X i)) = g (Ideal.Quotient.mk _ (MvPolynomial.X i))) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  exact h i

theorem jetCopy_X {n d m : ℕ} (i : Fin n) (p : Fin 1 × Fin d) :
    (jetCopy d m i : Jet V (Fin 1 × Fin d) m →ₐ[V] Jet V (Fin n × Fin d) m) (Ideal.Quotient.mk _ (MvPolynomial.X p)) =
      Ideal.Quotient.mk _ (MvPolynomial.X (i, p.2)) := by
  show Ideal.Quotient.mk _ (MvPolynomial.aeval (fun p : Fin 1 × Fin d =>
    (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) V)) (MvPolynomial.X p : MvPolynomial _ V)) = _
  rw [MvPolynomial.aeval_X]

theorem jetAug_X {κ : Type} {m : ℕ} (i : κ) :
    (jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0 := by
  show MvPolynomial.aeval (fun _ : κ => (0 : V)) (MvPolynomial.X i : MvPolynomial κ V) = 0
  rw [MvPolynomial.aeval_X]

theorem jetTrunc_mk {κ : Type} {m : ℕ} (p : MvPolynomial κ V) :
    (jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ p := rfl

theorem zV_pr {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {n d : ℕ} (pG : IsPowGrp G' G n)
    (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (m : ℕ) (i : Fin n) :
    zV pG xT m ≫ pG.pr i = Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m i) ≫ xT m :=
  pG.lim.fac _ ⟨i⟩

theorem pow_ext {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {n : ℕ} (pG : IsPowGrp G' G n) {T : Over (Sp V)}
    (f g : T ⟶ G') (h : ∀ i, f ≫ pG.pr i = g ≫ pG.pr i) : f = g :=
  pG.lim.hom_ext fun i => h i.as

theorem one_pr {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] {n : ℕ} (pG : IsPowGrp G' G n) {T : Over (Sp V)} (i : Fin n) :
    (1 : T ⟶ G') ≫ pG.pr i = 1 := by
  haveI := pG.hom i
  exact MonObj.one_comp _

end GlobalTheory.PowGerm.UnivPow

namespace GlobalTheory.PowGerm
open UnivPow

theorem univPow : UnivPowSt := by
  intro V _ G G' _ _ n d pG xT ⟨hT, hA, hU⟩
  refine ⟨fun m => pow_ext pG _ _ fun i => ?_, fun m => pow_ext pG _ _ fun i => ?_, ?_⟩
  · rw [Category.assoc, zV_pr, zV_pr, ← hT m, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp]
    congr 2
    apply jet_ext
    intro p
    rw [AlgHom.comp_apply, AlgHom.comp_apply, jetCopy_X, jetTrunc_mk, jetTrunc_mk, jetCopy_X]
  · rw [Category.assoc, zV_pr, one_pr, ← hA m, ← Category.assoc, homAt_comp]
    congr 2
    apply jet_ext
    intro p
    rw [AlgHom.comp_apply, jetCopy_X, jetAug_X, jetAug_X]
  · intro A _ _ aug m hm y hy
    have hi : ∀ i : Fin n, ∃! ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] A,
        aug.comp ψ = jetAug ∧ y ≫ pG.pr i = Formalism.L2.Pj.homAt (𝟙 (Sp V)) ψ ≫ xT m := fun i =>
      hU A aug m hm (y ≫ pG.pr i) (by rw [← Category.assoc, hy, one_pr])
    choose ψ hψ hψu using hi
    let a : Fin n × Fin d → A := fun p => ψ p.1 (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), p.2)))
    have ha : ∀ p, aug (a p) = 0 := fun p => by
      have := congrArg (fun f : Jet V (Fin 1 × Fin d) m →ₐ[V] V =>
        f (Ideal.Quotient.mk _ (MvPolynomial.X ((0 : Fin 1), p.2)))) (hψ p.1).1
      simp only [AlgHom.comp_apply, jetAug_X] at this
      exact this
    have hsp : Ideal.span (Set.range fun p => (MvPolynomial.aeval a : MvPolynomial (Fin n × Fin d) V →ₐ[V] A)
        (MvPolynomial.X p)) ^ (m + 1) = ⊥ := by
      apply le_bot_iff.1
      rw [← hm]
      apply Ideal.pow_right_mono
      rw [Ideal.span_le]
      rintro _ ⟨p, rfl⟩
      simp only [MvPolynomial.aeval_X]
      exact ha p
    let Ψ : Jet V (Fin n × Fin d) m →ₐ[V] A := liftJet (MvPolynomial.aeval a) hsp
    have hΨ : ∀ p, Ψ (Ideal.Quotient.mk _ (MvPolynomial.X p)) = a p := fun p => by
      show (MvPolynomial.aeval a : MvPolynomial (Fin n × Fin d) V →ₐ[V] A) (MvPolynomial.X p) = a p
      rw [MvPolynomial.aeval_X]
    have hc : ∀ i, Ψ.comp (jetCopy d m i) = ψ i := fun i => by
      apply jet_ext
      rintro ⟨u, j⟩
      obtain rfl : u = 0 := Subsingleton.elim _ _
      rw [AlgHom.comp_apply, jetCopy_X, hΨ]
    refine ⟨Ψ, ⟨?_, pow_ext pG _ _ fun i => ?_⟩, ?_⟩
    · apply jet_ext
      intro p
      rw [AlgHom.comp_apply, hΨ, ha, jetAug_X]
    · rw [Category.assoc, zV_pr, ← Category.assoc, homAt_comp, hc]
      exact (hψ i).2
    · rintro Φ ⟨h1, h2⟩
      have hd : ∀ i, Φ.comp (jetCopy d m i) = ψ i := fun i => by
        apply hψu i
        refine ⟨?_, ?_⟩
        · rw [← AlgHom.comp_assoc, h1]
          apply jet_ext
          intro p
          rw [AlgHom.comp_apply, jetCopy_X, jetAug_X, jetAug_X]
        · rw [h2, Category.assoc, zV_pr, ← Category.assoc, homAt_comp]
      apply jet_ext
      rintro ⟨i, j⟩
      rw [hΨ]
      show _ = ψ i _
      rw [← hd i, AlgHom.comp_apply, jetCopy_X]

end GlobalTheory.PowGerm
end
end

