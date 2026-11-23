module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ZeroMemLatOf
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0072
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0031
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0022
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruence
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
section
noncomputable section

namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem latOf_one_eq (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (h1 : L.FG) (h2 : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    GlobalTheory.AdLat.latOf F (1 : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (L : Set (Fin n → E)) = L := by
  ext v
  have h := (GlobalTheory.AdLat.hat_rational_points_and_approx F E n L h1 h2).1 v
  simp only [GlobalTheory.AdLat.latOf, Set.mem_ofPred_eq, Set.mem_image, Matrix.one_mulVec, exists_eq_right,
    SetLike.mem_coe]
  exact h

theorem latG_eq_span_latOf (D : D7) (V : HSp D) (g : GA D V) :
    latG V g = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA,
      ∃ v ∈ GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (latC V : Set (Fin V.rank → D.host.E)), w = a • v} := by
  have hh := (latHat_eq_hat_and_gram D V).1
  unfold latG gLat
  rw [hh]
  rfl

theorem latGHat_eq_closure (D : D7) (V : HSp D) (g : GA D V) :
    latGHat V g = AddSubgroup.closure {w | ∃ a ∈ D.host.AA,
      ∃ z ∈ (finHom V g).1.mulVec '' (GlobalTheory.AdLat.hat D.host.F (latC V : Set (Fin V.rank → D.host.E))),
        w = fun i => ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] a) * z i} := by
  have hh := (latHat_eq_hat_and_gram D V).1
  unfold latGHat gLat
  rw [hh]

theorem latG_lattice_and_completion : ∀ (D : D7) (V : HSp D), ∀ g : GA D V, (latG V g).FG ∧ Submodule.span D.host.E (latG V g : Set (Fin V.rank → D.host.E)) = ⊤ ∧ (latG V g : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (latG V 1 : Set (Fin V.rank → D.host.E)) ∧ (latGHat V g : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) = (finHom V g).1.mulVec '' (GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E))) ∧ latGHat V g = GlobalTheory.AdLat.hat D.host.F (latG V g : Set (Fin V.rank → D.host.E)) ∧ latG V 1 = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x} := by
  intro D V g
  obtain ⟨-, -, hfg, hsp, -⟩ := latHat_eq_hat_and_gram D V
  have hA : D.host.AA ≠ 0 := AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have h6 : latG V 1 = Submodule.span (𝓞 D.host.E) {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x} := by
    rw [latG_eq_span_latOf, map_one, Units.val_one, latOf_one_eq _ _ _ _ hfg hsp]
    rfl
  obtain ⟨s1, s2, s3, s4⟩ := GlobalTheory.AdLat.scale_latOf D.host.F D.host.E V.rank (latC V) (finHom V g) D.host.AA
    (latG V 1) hfg hsp hA h6
  have h3 : (latG V g : Set (Fin V.rank → D.host.E)) =
      GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (latG V 1 : Set (Fin V.rank → D.host.E)) := by
    rw [latG_eq_span_latOf D V g]; exact s1
  have h4 : (latGHat V g : Set (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)) =
      (finHom V g).1.mulVec '' (GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E))) := by
    rw [latGHat_eq_closure D V g]; exact s2
  obtain ⟨Λ, l1, l2, l3, l4⟩ := GlobalTheory.AdLat.exists_lattice_latOf D.host.F D.host.E V.rank (latG V 1) (finHom V g) s3 s4
  have hΛ : Λ = latG V g := SetLike.coe_injective (l1.trans h3.symm)
  subst hΛ
  exact ⟨l2, l3, h3, h4, SetLike.coe_injective (h4.trans l4.symm), h6⟩

end GlobalTheory.Member
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicative
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.Arch

theorem unit_iff {E : Type} [CommRing E] {n : Type} [Fintype n] (τ : E →+* ℂ) (G : Matrix n n E) (u : Matrix n n ℂ) :
    uᵀ * (-Gᵀ).map τ * u.map (starRingEnd ℂ) = (-Gᵀ).map τ ↔ uᴴ * G.map τ * u = G.map τ := by
  have e : (-Gᵀ).map τ = -(G.map τ)ᵀ := by
    ext a b; simp
  have e2 : u.map (starRingEnd ℂ) = (uᴴ)ᵀ := by
    ext a b; simp
  rw [e, e2, Matrix.mul_neg, Matrix.neg_mul, neg_inj, Matrix.mul_assoc, ← Matrix.transpose_mul, ← Matrix.transpose_mul]
  exact Matrix.transpose_injective.eq_iff

theorem form_map {A : Type} [CommRing A] {n : Type} [Fintype n] (s : A →+* A) (φ : A →+* ℂ)
    (h : ∀ z, φ (s z) = starRingEnd ℂ (φ z)) (M J : Matrix n n A) :
    (Formalism.UG.cT s M * J * M).map φ = (M.map φ)ᴴ * J.map φ * M.map φ := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext a b
  exact h _

theorem mat_ext {A : Type} [CommRing A] {n ι : Type} (θ : ι → (A →+* ℂ))
    (hθ : Function.Injective fun (z : A) (i : ι) => θ i z) {M N : Matrix n n A}
    (h : ∀ i, M.map (θ i) = N.map (θ i)) : M = N :=
  Matrix.ext fun a b => hθ (funext fun i => congrFun (congrFun (h i) a) b)

theorem exists_lift {A : Type} [CommRing A] {n ι : Type} [Fintype n] [DecidableEq n] (s : A →+* A)
    (θ : ι → (A →+* ℂ)) (hθ : Function.Bijective fun (z : A) (i : ι) => θ i z)
    (hs : ∀ i z, θ i (s z) = starRingEnd ℂ (θ i z)) (J : Matrix n n A) (hJ : ∀ i, (J.map (θ i)).det ≠ 0)
    (u : ι → Matrix n n ℂ) (hu : ∀ i, (u i)ᴴ * J.map (θ i) * u i = J.map (θ i)) :
    ∃ g : GL n A, g ∈ Formalism.UG.UJ s J ∧ ∀ i, g.1.map (θ i) = u i := by
  have lift : ∀ w : ι → Matrix n n ℂ, ∃ M : Matrix n n A, ∀ i, M.map (θ i) = w i := by
    intro w
    choose M hM using fun a b => hθ.2 fun i => w i a b
    exact ⟨Matrix.of M, fun i => Matrix.ext fun a b => congrFun (hM a b) i⟩
  have hd : ∀ i, IsUnit (u i).det := by
    intro i
    refine IsUnit.mk0 _ fun h0 => hJ i ?_
    rw [← hu i, Matrix.det_mul, h0, mul_zero]
  obtain ⟨M, hM⟩ := lift u
  obtain ⟨N, hN⟩ := lift fun i => (u i)⁻¹
  refine ⟨⟨M, N, mat_ext θ hθ.1 fun i => ?_, mat_ext θ hθ.1 fun i => ?_⟩, mat_ext θ hθ.1 fun i => ?_, hM⟩
  · rw [Matrix.map_mul, hM, hN, Matrix.mul_nonsing_inv _ (hd i), Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [Matrix.map_mul, hM, hN, Matrix.nonsing_inv_mul _ (hd i), Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [form_map s (θ i) (hs i), hM, hu]

theorem gram_det_ne_zero {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) :
    S.gram.det ≠ 0 := by
  intro h
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  have hy : S.frame.equivFun.symm v = 0 := by
    apply S.nondeg.2
    intro x
    have hi : ∀ i, S.hT (S.frame i) (S.frame.equivFun.symm v) = 0 := by
      intro i
      have := congrFun h0 i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Module.Basis.equivFun_symm_apply, map_sum]
      simpa [Matrix.mulVec, dotProduct, Formalism.BasicNotions.HSpace.gram, mul_comm] using this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← S.frame.sum_repr x, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hi, smul_zero]
  exact S.frame.equivFun.symm.map_eq_zero_iff.1 hy

theorem continuous_inf (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Continuous (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) : AF F ⊗[F] E → Ainf F ⊗[F] E) := by
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousAdd (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Ainf F) _
  have : ContinuousSMul (Ainf F) (Ainf F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  let φ : AF F ⊗[F] E →ₛₗ[(fstA F).toRingHom] Ainf F ⊗[F] E :=
    { toFun := Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)
      map_add' := map_add _
      map_smul' := fun a x => by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        rfl }
  have hs : Continuous ((fstA F).toRingHom : AF F → Ainf F) := continuous_fst
  exact IsModuleTopology.continuous_of_linearMapₛₗ hs φ

theorem inf_mem {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (g : GL (Fin n) (AF F ⊗[F] E)) (hg : g ∈ HR (AF F) σ J) :
    Formalism.UG.bc (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom g ∈ HR (Ainf F) σ J := by
  let π : AF F ⊗[F] E →+* Ainf F ⊗[F] E := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom
  have hπ : ∀ z, π (sigR (AF F) σ z) = sigR (Ainf F) σ (π z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
    | tmul a x => rfl
  have hg' : Formalism.UG.cT (sigR (AF F) σ) g.1 * JR (AF F) J * g.1 = JR (AF F) J := hg
  have hJ : (JR (F := F) (AF F) J).map π = JR (Ainf F) J := rfl
  have hc : (Formalism.UG.cT (sigR (AF F) σ) g.1).map π = Formalism.UG.cT (sigR (Ainf F) σ) (g.1.map π) :=
    Matrix.ext fun a b => hπ _
  change Formalism.UG.cT (sigR (Ainf F) σ) (g.1.map π) * JR (Ainf F) J * g.1.map π = JR (Ainf F) J
  rw [← hc, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']

variable {D : D7}

theorem JR_map (V : HSp D) {τ : D.host.E →+* ℂ} {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ}
    (h : Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) : (JR (F := D.host.F) (Ainf D.host.F) V.gram).map θ = V.gram.map τ :=
  Matrix.ext fun _ _ => h.1 _

theorem archM_of_one (V : HSp D) (θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) {k : GA D V}
    (hk : infHom V k = 1) : archM V θ k = 1 := by
  rw [archM, hk, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem continuous_archM (V : HSp D) {θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ} (hθ : Continuous θ) :
    Continuous fun h => archM V θ h := by
  have h1 : Continuous fun h : GA D V => (matHom V h).1 :=
    Units.continuous_val.comp (continuous_subtype_val (p := (· ∈ HR (AF D.host.F) D.sp.cm.sig V.gram)))
  exact (h1.matrix_map (continuous_inf D.host.F D.host.E)).matrix_map hθ

theorem archM_spec : ∀ (D : D7) (V : HSp D), ∀ (θ : (D.host.E →+* ℂ) → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), (∀ τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ (θ τ)) → (∀ τ, archM V (θ τ) 1 = 1 ∧ (∀ h h', archM V (θ τ) (h * h') = archM V (θ τ) h * archM V (θ τ) h') ∧ (∀ k ∈ GfC V, archM V (θ τ) k = 1) ∧ Continuous (fun h => archM V (θ τ) h) ∧ ∀ h, (archM V (θ τ) h)ᵀ * (-V.gramᵀ).map τ * (archM V (θ τ) h).map (starRingEnd ℂ) = (-V.gramᵀ).map τ) ∧ (∀ h, (∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → archM V (θ τ) h = 1) → h ∈ GfC V) ∧ ∀ u : (D.host.E →+* ℂ) → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → (u τ)ᵀ * (-V.gramᵀ).map τ * (u τ).map (starRingEnd ℂ) = (-V.gramᵀ).map τ) → ∃ a ∈ GinfC V, ∀ τ, τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD → archM V (θ τ) a = u τ := by
  intro D V θ hθ
  obtain ⟨hc, hs, hb⟩ := (_root_.GlobalTheory.Member.infiniteAdele_bijective D).2 θ hθ
  refine ⟨fun τ => ⟨archM_of_one V _ (map_one _), fun h h' => ?_, fun k hk => archM_of_one V _ hk,
    continuous_archM V (hc τ), fun h => ?_⟩, fun h hh => ?_, fun u hu => ?_⟩
  · rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
  · have hm : Formalism.UG.cT (sigR (Ainf D.host.F) D.sp.cm.sig) (infHom V h).1 * JR (Ainf D.host.F) V.gram * (infHom V h).1 =
        JR (Ainf D.host.F) V.gram := inf_mem D.sp.cm.sig V.gram (matHom V h) h.2
    rw [unit_iff, ← JR_map V (hθ τ), archM, ← form_map _ _ (hs τ), hm]
  · refine Units.ext (mat_ext _ hb.1 fun τ => ?_)
    rw [Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hh τ.1 τ.2
  · obtain ⟨g, hg, hgu⟩ := exists_lift (sigR (Ainf D.host.F) D.sp.cm.sig) _ hb (fun τ => hs τ.1)
      (JR (Ainf D.host.F) V.gram) (fun τ => by
        rw [JR_map V (hθ τ.1)]
        have : (V.gram.map τ.1).det = τ.1 V.gram.det := (τ.1.map_det V.gram).symm
        rw [this]
        exact (map_ne_zero τ.1).2 (gram_det_ne_zero V)) (fun τ => u τ.1) (fun τ => by
        rw [JR_map V (hθ τ.1)]
        exact (unit_iff _ _ _).1 (hu τ.1 τ.2))
    obtain ⟨a, ha, hag⟩ := (_root_.GlobalTheory.UnitarySplit.real_finite_split D V).2.2.2.2 g hg
    refine ⟨a, ha, fun τ hτ => ?_⟩
    rw [archM, hag]
    exact hgu ⟨τ, hτ⟩

end GlobalTheory.Member.Arch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DifferentiableOnThetaAlgebraicGeneratorFactor
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.HolGen

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

theorem chart_iff {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (q : Sp ℂ ⟶ Gx x) (j : Xo.univ.t.PP.L.ι) :
    ⊤ ≤ q ⁻¹ᵁ (PPx x).U (fun _ => j) ↔ ⊤ ≤ (q ≫ Formalism.L2.PjFree.gxFst x) ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
  rw [top_le_preimage_iff_mem, top_le_preimage_iff_mem]
  constructor
  · intro hp
    exact Set.mem_iInter.1 hp (0 : Fin 1)
  · intro hp
    exact Set.mem_iInter.2 fun _ => hp

theorem exists_pt {R : Type} [CommRing R] (x : Sp R ⟶ Xo.X) (s : Sp ℂ ⟶ Sp R) (p : Sp ℂ ⟶ Xo.univ.t.G.left)
    (h : s ≫ x = p ≫ Xo.univ.t.G.hom) : ∃ q : Sp ℂ ⟶ Gx x, q ≫ Formalism.L2.PjFree.gxFst x = p ∧ q ≫ Formalism.L2.PjFree.gxSnd x = s :=
  ⟨pullback.lift (f := x) (g := Xo.univ.t.G.hom) s p h, pullback.lift_snd _ _ _, pullback.lift_fst _ _ _⟩

theorem val_pull {R : Type} [CommRing R] (φ : R →+* ℂ) (x₀ : Sp R ⟶ Xo.X) (x : Sp ℂ ⟶ Xo.X)
    (s₀ : LB.Sec (PPx x₀)) (s : LB.Sec (PPx x)) (pm : Gx x ⟶ Gx x₀) (h₁ : pm ≫ Formalism.L2.PjFree.gxFst x₀ = Formalism.L2.PjFree.gxFst x)
    (h₂ : pm ≫ Formalism.L2.PjFree.gxSnd x₀ = Formalism.L2.PjFree.gxSnd x ≫ spMap φ)
    (h₃ : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x).U i ≤ pm ⁻¹ᵁ (PPx x₀).U i),
      (pm.appLE _ _ h).hom (s₀.f i) = s.f i)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (pt : Sp ℂ ⟶ Gx x) (q : Sp ℂ ⟶ Gx x₀) (e₁ : q ≫ Formalism.L2.PjFree.gxFst x₀ = pt ≫ Formalism.L2.PjFree.gxFst x)
    (e₂ : pt ≫ Formalism.L2.PjFree.gxSnd x = 𝟙 _) (e₃ : q ≫ Formalism.L2.PjFree.gxSnd x₀ = spMap φ) (hp : ⊤ ≤ pt ⁻¹ᵁ (PPx x).U i) :
    valAt' pt ((PPx x).U i) (s.f i) = valAt' q ((PPx x₀).U i) (s₀.f i) := by
  have hq : q = pt ≫ pm := SecCalc.pm_ext _ _
    (e₁.trans (show pt ≫ Formalism.L2.PjFree.gxFst x = (pt ≫ pm) ≫ Formalism.L2.PjFree.gxFst x₀ by rw [Category.assoc, h₁]))
    (e₃.trans (show spMap φ = (pt ≫ pm) ≫ Formalism.L2.PjFree.gxSnd x₀ by
      rw [Category.assoc, h₂, ← Category.assoc, e₂, Category.id_comp]))
  rw [← h₃ i (SecCalc.ppx_le pm h₁ i), hq]
  exact valAt'_appLE pt pm _ _ _ _ hp

theorem val_mul_pull (hT : Out.SecTwistSt) {R : Type} [CommRing R] (φ : R →+* ℂ) (a : ℂ) (x₀ : Sp R ⟶ Xo.X)
    (x y : Sp ℂ ⟶ Xo.X) (hxy : y = x)
    (s₀ : LB.Sec (PPx x₀)) (s : LB.Sec (PPx x)) (t : LB.Sec (PPx y)) (pm : Gx x ⟶ Gx x₀)
    (h₁ : pm ≫ Formalism.L2.PjFree.gxFst x₀ = Formalism.L2.PjFree.gxFst x) (h₂ : pm ≫ Formalism.L2.PjFree.gxSnd x₀ = Formalism.L2.PjFree.gxSnd x ≫ spMap φ)
    (h₃ : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x).U i ≤ pm ⁻¹ᵁ (PPx x₀).U i),
      (pm.appLE _ _ h).hom (s₀.f i) = s.f i) (hst : SecBC (RingHom.id ℂ) a x y s t)
    (i : Fin 1 → Xo.univ.t.PP.L.ι) (pt : Sp ℂ ⟶ Gx y) (q : Sp ℂ ⟶ Gx x₀) (e₁ : q ≫ Formalism.L2.PjFree.gxFst x₀ = pt ≫ Formalism.L2.PjFree.gxFst y)
    (e₂ : pt ≫ Formalism.L2.PjFree.gxSnd y = 𝟙 _) (e₃ : q ≫ Formalism.L2.PjFree.gxSnd x₀ = spMap φ) (hp : ⊤ ≤ pt ⁻¹ᵁ (PPx y).U i) :
    valAt' pt ((PPx y).U i) (t.f i) = a * valAt' q ((PPx x₀).U i) (s₀.f i) := by
  subst hxy
  have hy : y = spMap (RingHom.id ℂ) ≫ y := by rw [SecCalc.spMap_id', Category.id_comp]
  have ht := ((SecCalc.sec_calc E H Dw l Xo ℂ ℂ ℂ _ _ y y y hy hy).2.1 a s t).1 hst i
  rw [ht, (sec_values_complex_fibre hT E H Dw l Xo y s).1 a i pt e₂,
    val_pull φ x₀ y s₀ s pm h₁ h₂ h₃ i pt q e₁ e₂ e₃ hp]

theorem exists_val_ne (hT : Out.SecTwistSt) {R : Type} [CommRing R] (φ : R →+* ℂ) (x₀ : Sp R ⟶ Xo.X)
    (x u : Sp ℂ ⟶ Xo.X) (hu : u = x) (s₀ : LB.Sec (PPx x₀)) (s : LB.Sec (PPx x)) (pm : Gx x ⟶ Gx x₀)
    (h₁ : pm ≫ Formalism.L2.PjFree.gxFst x₀ = Formalism.L2.PjFree.gxFst x) (h₂ : pm ≫ Formalism.L2.PjFree.gxSnd x₀ = Formalism.L2.PjFree.gxSnd x ≫ spMap φ)
    (h₃ : ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x).U i ≤ pm ⁻¹ᵁ (PPx x₀).U i),
      (pm.appLE _ _ h).hom (s₀.f i) = s.f i) (hs : SecGen x s) :
    ∃ (e : Over.mk u ⟶ Xo.univ.t.G) (j : Xo.univ.t.PP.L.ι), ∀ q : Sp ℂ ⟶ Gx x₀, q ≫ Formalism.L2.PjFree.gxFst x₀ = e.left →
      q ≫ Formalism.L2.PjFree.gxSnd x₀ = spMap φ → valAt' q ((PPx x₀).U (fun _ => j)) (s₀.f (fun _ => j)) ≠ 0 := by
  subst hu
  obtain ⟨i, pt, hpt, hv⟩ := (sec_values_complex_fibre hT E H Dw l Xo u s).2.1.1 hs
  obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i (0 : Fin 1), funext fun k : Fin 1 => congrArg i (Subsingleton.elim _ _)⟩
  have hc : Formalism.L2.PjFree.gxSnd u ≫ u = Formalism.L2.PjFree.gxFst u ≫ Xo.univ.t.G.hom := pullback.condition (f := u) (g := Xo.univ.t.G.hom)
  refine ⟨Over.homMk (pt ≫ Formalism.L2.PjFree.gxFst u) ?_, j, fun q e₁ e₃ => ?_⟩
  · show (pt ≫ Formalism.L2.PjFree.gxFst u) ≫ Xo.univ.t.G.hom = u
    rw [Category.assoc, ← hc, ← Category.assoc, hpt, Category.id_comp]
  · rw [← val_pull φ x₀ u s₀ s pm h₁ h₂ h₃ _ pt q e₁ hpt e₃ (top_le_preimage_of_valAt'_ne_zero _ hv)]
    exact hv

end

theorem differentiableOn_generator_factor : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.PjFree.relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k) (R : Type) [CommRing R] [Algebra c.F R] (y₀ : FrPt Xo c R) (B : Set (Fin T.m → ℂ)) (ψ : (Fin T.m → ℂ) → (R →ₐ[c.F] CAt σ)) (κ : (Fin T.m → ℂ) → ℂ) (z y : (Fin T.m → ℂ) → FrPt Xo c (CAt σ)) (G : (Fin T.m → ℂ) → (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ))) (a : (Fin T.m → ℂ) → CAt σ), IsOpen B → B ⊆ T.co ⁻¹' (M.X k).dom → (∀ t : R, DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (ψ b t)) B) → (∀ b ∈ B, FrMap (ψ b) y₀ (z b) ∧ FrChg (G b) (a b) (z b) (y b) ∧ IsThetaPt T b (κ b) (y b)) → DifferentiableOn ℂ κ B → DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (a b)) B := by
  intro hT E _ _ _ H Dw l Xo c σ g e F r M k T R _ _ y₀ B ψ κ z y G a hB hBd hψ hb hκ b₀ hb₀
  let φ : (Fin T.m → ℂ) → (R →+* ℂ) := fun b => (ψ b).toRingHom
  have hP : IsHolPeriods (F.Di k) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) B (fun b => T.Pf (T.co b)) :=
    ⟨fun b hb => T.holPer.1 b (hBd hb), fun x => (T.holPer.2 x).mono hBd⟩
  have hux : ∀ b ∈ B, F.u k (T.Pf (T.co b)) = (z b).x := fun b h =>
    (hb b h).2.2.1.symm.trans (hb b h).2.1.1
  obtain ⟨pm₀, p₁, p₂, p₃⟩ := (hb b₀ hb₀).1.2.2
  obtain ⟨e₀, j, hne⟩ := exists_val_ne hT (φ b₀) y₀.x (z b₀).x _ (hux b₀ hb₀) y₀.s (z b₀).s pm₀ p₁ p₂ p₃ (z b₀).gen
  obtain ⟨w₀, rfl⟩ := F.ex_onto k _ (hP.1 b₀ hb₀) e₀
  have hq₁ : ∀ b ∈ B, ∃ q : Sp ℂ ⟶ Gx y₀.x, q ≫ Formalism.L2.PjFree.gxFst y₀.x = (F.ex k (T.Pf (T.co b)) w₀).left ∧
      q ≫ Formalism.L2.PjFree.gxSnd y₀.x = spMap (φ b) := fun b h =>
    exists_pt _ _ _ (((hb b h).1.1.symm.trans (hux b h).symm).trans (Over.w (F.ex k (T.Pf (T.co b)) w₀)).symm)
  have hq₂ : ∀ b, ∃ q : Sp ℂ ⟶ Gx y₀.x, b ∈ B → q ≫ Formalism.L2.PjFree.gxFst y₀.x = (F.ex k (T.Pf (T.co b)) w₀).left ∧
      q ≫ Formalism.L2.PjFree.gxSnd y₀.x = spMap (φ b) := fun b => by
    by_cases h : b ∈ B
    · exact (hq₁ b h).imp fun _ h' _ => h'
    · exact ⟨(hq₁ b₀ hb₀).choose, fun h' => absurd h' h⟩
  choose q hq using hq₂
  have hι : Differentiable ℂ (fun b : Fin T.m → ℂ => ((b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ))) := by fun_prop
  have hol : IsHolTo B q := by
    refine HolPullback.isHolTo_of_components _ B _ _ _ _ (Formalism.L2.PjFree.gxSnd y₀.x) (Formalism.L2.PjFree.gxFst y₀.x) y₀.x Xo.univ.t.G.hom q
      (IsPullback.of_hasPullback y₀.x Xo.univ.t.G.hom) hB ?_ ?_
    · exact LocLift.isHolTo_congr (ThetaValueCont.isHolTo_spMap hB φ hψ) fun b h => (hq b h).2
    · exact LocLift.isHolTo_congr (LocLift.isHolTo_comp (F.hol k _ B _ hB hP).2 hB hι.differentiableOn
        fun b h => ⟨h, trivial⟩) fun b h => (hq b h).1
  have hW := (hol ((Gx y₀.x).basicOpen (y₀.s.f (fun _ => j))) 0).1
  set W := {b ∈ B | ⊤ ≤ q b ⁻¹ᵁ (Gx y₀.x).basicOpen (y₀.s.f (fun _ => j))} with hWd
  have hb₀W : b₀ ∈ W := ⟨hb₀, (top_le_preimage_basicOpen_iff _ _ _).2 (hne _ (hq b₀ hb₀).1 (hq b₀ hb₀).2)⟩
  have vnz : ∀ b ∈ W, valAt' (q b) ((PPx y₀.x).U (fun _ => j)) (y₀.s.f (fun _ => j)) ≠ 0 := fun b h =>
    (top_le_preimage_basicOpen_iff _ _ _).1 h.2
  have m₁ : ∀ b ∈ W, ⊤ ≤ q b ⁻¹ᵁ (PPx y₀.x).U (fun _ => j) := fun b h =>
    top_le_preimage_of_valAt'_ne_zero _ (vnz b h)
  have m₂ : ∀ b ∈ W, ⊤ ≤ (F.ex k (T.Pf (T.co b)) w₀).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun b h => by
    rw [← (hq b h.1).1]
    exact (chart_iff _ _ _).1 (m₁ b h)
  have hθ := (ThetaHalf.thetaChar_holomorphic_ne_zero g T.c₁ T.c₂ T.half₁ T.half₂).2 T.m B T.h T.ta hB
    (fun b h => ⟨(T.norm b (hBd h)).2.1, (T.norm b (hBd h)).2.2.1⟩)
    (fun i i' => ⟨(T.hol i i').1.mono hBd, (T.hol i i').2.mono hBd⟩)
  have d₀ : DifferentiableOn ℂ κ W := hκ.mono fun b h => h.1
  have d₁ : DifferentiableOn ℂ (fun b => thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w₀)) W :=
    DifferentiableOn.comp (f := fun b : Fin T.m → ℂ => ((b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ)))
      (g := fun bz : (Fin T.m → ℂ) × (Fin g → ℂ) => thetaChar (T.ta bz.1) T.c₁ T.c₂ (T.h bz.1 *ᵥ bz.2))
      hθ hι.differentiableOn fun b h => ⟨h.1, trivial⟩
  have d₂ : DifferentiableOn ℂ (fun b => T.fr j (b, w₀)) W :=
    DifferentiableOn.comp (f := fun b : Fin T.m → ℂ => ((b, w₀) : (Fin T.m → ℂ) × (Fin g → ℂ))) (g := T.fr j)
      (T.fr_hol j) hι.differentiableOn fun b h => ⟨hBd h.1, m₂ b h⟩
  have d₃ : DifferentiableOn ℂ (fun b => valAt' (q b) ((PPx y₀.x).U (fun _ => j)) (y₀.s.f (fun _ => j))) W :=
    (hol _ _).2.mono fun b h => ⟨h.1, m₁ b h⟩
  have key : ∀ b ∈ W, κ b * thetaChar (T.ta b) T.c₁ T.c₂ (T.h b *ᵥ w₀) * T.fr j (b, w₀) =
      Formalism.L2.PjFree.toC (a b) * valAt' (q b) ((PPx y₀.x).U (fun _ => j)) (y₀.s.f (fun _ => j)) := fun b h => by
    obtain ⟨⟨-, -, pm, p₁, p₂, p₃⟩, ⟨hyz, -, hbc⟩, hyu, -, hth⟩ := hb b h.1
    obtain ⟨pt, e₁, e₂⟩ := exists_pt (R := ℂ) (y b).x (𝟙 _) (F.ex k (T.Pf (T.co b)) w₀).left
      (((Category.id_comp _).trans hyu).trans (Over.w (F.ex k (T.Pf (T.co b)) w₀)).symm)
    refine (hth j w₀ pt e₁ e₂ (m₂ b h)).symm.trans ?_
    refine val_mul_pull hT (φ b) (Formalism.L2.PjFree.toC (a b)) y₀.x (z b).x (y b).x hyz y₀.s (z b).s (y b).s pm p₁ p₂ p₃ hbc _ pt (q b)
      ((hq b h.1).1.trans e₁.symm) e₂ (hq b h.1).2 ((chart_iff _ _ _).2 ?_)
    rw [e₁]
    exact m₂ b h
  have d : DifferentiableOn ℂ (fun b => Formalism.L2.PjFree.toC (a b)) W := (((d₀.mul d₁).mul d₂).mul (d₃.inv vnz)).congr fun b h =>
    ((mul_inv_eq_iff_eq_mul₀ (vnz b h)).2 (key b h)).symm
  exact (d.differentiableAt (hW.mem_nhds hb₀W)).differentiableWithinAt

end GlobalTheory.HolGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryAdelicCharOfHeckeChar
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem continuous_det_matHom (D : D7) (V : HSp D) :
    Continuous fun g : GA D V => Matrix.GeneralLinearGroup.det (matHom V g) := by
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
  have hm : Continuous fun g : GA D V => matHom V g := continuous_subtype_val
  exact Matrix.GeneralLinearGroup.continuous_det.comp hm

theorem exists_muVal : ∀ (D : D7) (V : HSp D), ∀ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ → (∀ a, χ (idF D a) = 1) → ∃ mu : GA D V → ℂ, MuVal V χ mu ∧ (∀ g g', mu (g * g') = mu g * mu g') ∧ (∀ g, ‖mu g‖ = 1) ∧ (∀ γ ∈ GQ V, mu γ = 1) ∧ Continuous mu := by
  intro D V χ hχ hF
  obtain ⟨hex, huniq, hrat, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D V
  choose r hr using hex
  have hval : ∀ g x, IsDetRoot V g x → χ (r g) = χ x := by
    intro g x hx
    obtain ⟨a, ha⟩ := huniq g _ _ (hr g) hx
    rw [ha, map_mul, hF, mul_one]
  have hm : ∀ g g', χ (r (g * g')) = χ (r g) * χ (r g') := by
    intro g g'
    rw [hval _ _ (hmul _ _ _ _ (hr g) (hr g')), map_mul]
  let m : GA D V →* Circle := MonoidHom.mk' (fun g => χ (r g)) hm
  have hcont : Continuous m := by
    haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
    refine continuous_of_continuousAt_one m ?_
    intro U hU
    rw [map_one] at hU
    have hW : χ ⁻¹' U ∈ 𝓝 (1 : (AE D)ˣ) := hχ.1.continuousAt.preimage_mem_nhds (by rwa [map_one])
    obtain ⟨N, hN, hNW⟩ := GlobalTheory.Member.exists_root_near_one D _ hW
    have hN' : (fun g : GA D V => Matrix.GeneralLinearGroup.det (matHom V g)) ⁻¹' N ∈ 𝓝 (1 : GA D V) :=
      (continuous_det_matHom D V).continuousAt.preimage_mem_nhds (by rwa [map_one, map_one])
    refine Filter.mem_map.2 (Filter.mem_of_superset hN' ?_)
    intro g hg
    obtain ⟨x, hxW, hx⟩ := hNW _ hg (GlobalTheory.Member.finHom_herm_det D V g).2.2
    have : m g = χ x := hval g x hx
    show m g ∈ U
    rw [this]
    exact hxW
  refine ⟨fun g => (m g : ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun g => ⟨r g, hr g⟩, fun g x hx => congrArg (fun z : Circle => (z : ℂ)) (hval g x hx)⟩
  · intro g g'
    simp only [map_mul, Circle.coe_mul]
  · intro g
    exact Circle.norm_coe _
  · intro γ hγ
    obtain ⟨x, hx⟩ := hrat γ hγ
    have : m γ = 1 := (hval γ _ hx).trans (hχ.2 x)
    simp only [this, Circle.coe_one]
  · exact continuous_subtype_val.comp hcont

end GlobalTheory.Member
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GamAtOfLawsCore
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.RunIn

theorem gamAt_of_lawsCore' : ∀ (D : D7) (T : Core D), LawsCore T → GlobalTheory.RunIn.GamAt T :=
  fun D T h j hj σ hσ => _root_.GlobalTheory.PrincCore.hasPrinc_core D T h j hj σ hσ

end GlobalTheory.RunIn
end

