module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSymplecticOfTranslFixed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1642
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1853
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1612
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2129

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectDataDescendsFiniteTypeSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings

namespace GlobalTheory.SiegFg

theorem spMap_subtype_inclusion' {R : Type} [CommRing R] {S₀ R₁ : Subring R} (h : S₀ ≤ R₁) :
    spMap R₁.subtype ≫ spMap (Subring.inclusion h) = spMap S₀.subtype := by
  rw [← Spec.map_comp]
  rfl

theorem smooth_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (B : Over S) (g : ℕ) (hB : SmoothOfRelativeDimension g B.hom) :
    SmoothOfRelativeDimension g ((Over.pullback f).obj B).hom :=
  (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback B.hom f) hB

theorem range_le {n : ℕ} {R : Type} [CommRing R] (β : cycAway n →+* R) (S₀ : Subring R)
    (h₁ : β (zetaAway n) ∈ S₀) (h₂ : ∀ hm : ((n : ℂ))⁻¹ ∈ cycAway n, β ⟨((n : ℂ))⁻¹, hm⟩ ∈ S₀) (x : cycAway n) :
    β x ∈ S₀ := by
  obtain ⟨x, hx⟩ := x
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact h₁
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact h₂ _
  | zero => exact (congrArg (· ∈ S₀) (map_zero β)).mpr S₀.zero_mem
  | one => exact (congrArg (· ∈ S₀) (map_one β)).mpr S₀.one_mem
  | add y z hy hz ihy ihz =>
    have e : β ⟨y + z, Subring.add_mem _ hy hz⟩ = β ⟨y, hy⟩ + β ⟨z, hz⟩ := by rw [← map_add (f := _)]; rfl
    rw [e]; exact S₀.add_mem ihy ihz
  | neg y hy ihy =>
    have e : β ⟨-y, Subring.neg_mem _ hy⟩ = -β ⟨y, hy⟩ := by rw [← map_neg]; rfl
    rw [e]; exact S₀.neg_mem ihy
  | mul y z hy hz ihy ihz =>
    have e : β ⟨y * z, Subring.mul_mem _ hy hz⟩ = β ⟨y, hy⟩ * β ⟨z, hz⟩ := by rw [← map_mul]; rfl
    rw [e]; exact S₀.mul_mem ihy ihz

end GlobalTheory.SiegFg

namespace GlobalTheory.SiegFg

theorem siegPre_data_descends_fg : ∀ (g n : ℕ), 3 ≤ n → ∀ (R : Type) [CommRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)), ∃ (R₁ : Subring R) (β₁ : cycAway n →+* R₁) (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (P₁ : LB (A₁ ⊗ A₁).left) (lv₁ : Std g n → (𝟙_ (Over (Sp R₁)) ⟶ A₁)), Algebra.FiniteType ℤ R₁ ∧ R₁.subtype.comp β₁ = β ∧ IsAbelianScheme A₁ ∧ SmoothOfRelativeDimension g A₁.hom ∧ P₁.IsLB ∧ IsPullbackTriple c.A c.P (lvOf c) A₁ P₁ lv₁ (spMap R₁.subtype) := by
  intro g n hn R _ β c
  classical
  have h0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨h0⟩
  have hdim : SmoothOfRelativeDimension g c.A.hom :=
    relDim (ζ := (cycBase h0).ζ) (by omega) (isUnit_natCast h0) c
  have hm : ((n : ℂ))⁻¹ ∈ cycAway n := Subring.subset_closure (by simp)
  obtain ⟨S₀, B, _, φ, hF, hS₀, hB, hBd, hφ⟩ := GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring R g c.A
    {β (zetaAway n), β ⟨((n : ℂ))⁻¹, hm⟩} c.ab hdim
  have hβ : ∀ x, β x ∈ S₀ := range_le β S₀ (hF (by simp)) (fun _ => hF (by simp))
  have : IsCommMonObj B := hB.comm
  have : IsProper B.hom := hB.proper
  have : Smooth B.hom := hB.smooth
  have : QuasiCompact (B ⊗ B).hom := by
    change QuasiCompact (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
  have : QuasiSeparated (B ⊗ B).hom := by
    change QuasiSeparated (pullback.fst B.hom B.hom ≫ B.hom); infer_instance

  obtain ⟨φ₂, hsq⟩ := GlobalTheory.SiegDesc.exists_isSquare hφ.1.w
  obtain ⟨SP, hSP⟩ := GlobalTheory.LBLimit.lb_descends_to_fg_subring R S₀ (c.A ⊗ c.A).left (B ⊗ B).left (c.A ⊗ c.A).hom
    (B ⊗ B).hom φ₂ c.P (GlobalTheory.SiegDesc.isPullback_of_isSquare hφ.1 hsq) c.isLB

  have hw : ∀ a : Std g n, ((lvOf c a).left ≫ φ) ≫ B.hom = spMap S₀.subtype ≫ 𝟙 _ := fun a => by
    have e : (lvOf c a).left ≫ c.A.hom = 𝟙 _ := Over.w (lvOf c a)
    rw [Category.assoc, hφ.1.w, reassoc_of% e, Category.comp_id]
  choose SL hSL using fun a : Std g n => GlobalTheory.morphism_descends_to_subring R S₀ (Sp R) (Sp S₀) B.left (𝟙 _) (𝟙 _)
    B.hom (spMap S₀.subtype) ((lvOf c a).left ≫ φ) IsPullback.of_id_snd (hw a)

  let T : Finset R := SP ∪ Finset.univ.biUnion SL
  let R₁ : Subring R := (Algebra.adjoin S₀ (T : Set R)).toSubring
  have hFT : Algebra.FiniteType ℤ R₁ :=
    GlobalTheory.SpreadGroup.finiteType_of_fg hS₀ (Subalgebra.fg_adjoin_finset T)
  have h : S₀ ≤ R₁ := fun x hx => Subalgebra.algebraMap_mem (Algebra.adjoin S₀ (T : Set R)) (⟨x, hx⟩ : S₀)
  have hT : (T : Set R) ⊆ R₁ := Algebra.subset_adjoin
  have hSPs : (SP : Set R) ⊆ R₁ := fun x hx => hT (by simp [T, Finset.mem_coe.1 hx])
  have hSLs : ∀ a, (SL a : Set R) ⊆ R₁ := fun a x hx => hT (by
    simp only [T, Finset.coe_union, Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true]
    exact Or.inr (Set.mem_iUnion.2 ⟨a, hx⟩))
  have hj : spMap R₁.subtype ≫ spMap (Subring.inclusion h) = spMap S₀.subtype := spMap_subtype_inclusion' h

  let A₁ : Over (Sp R₁) := (Over.pullback (spMap (Subring.inclusion h))).obj B
  have hA₁ : IsAbelianScheme A₁ :=
    { comm := by infer_instance
      smooth := by show Smooth (pullback.snd _ _); infer_instance
      proper := by show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := hB.geomConnected
        show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have hA₁d : SmoothOfRelativeDimension g A₁.hom := smooth_pull _ B g hBd
  have hpb := Pdiv.PullbackComparison.isGrpPullback (spMap (Subring.inclusion h)) B
  let ψ : c.A.left ⟶ A₁.left := pullback.lift φ (c.A.hom ≫ spMap R₁.subtype)
    (by rw [hφ.1.w, Category.assoc, hj])
  have hψ₁ : ψ ≫ Pdiv.PullbackComparison.pφ (spMap (Subring.inclusion h)) B = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ A₁.hom = c.A.hom ≫ spMap R₁.subtype := pullback.lift_snd _ _ _
  have hgp : IsGrpPullback c.A A₁ (spMap R₁.subtype) ψ :=
    IsGrpPullback.cancel hpb (by rw [hψ₁, hj]; exact hφ) hψ₂

  obtain ⟨ψ₂, hsqψ⟩ := GlobalTheory.SiegDesc.exists_isSquare hψ₂
  obtain ⟨P₁, hP₁, hiso⟩ := hSP R₁ h hSPs (A₁ ⊗ A₁).left (A₁ ⊗ A₁).hom
    (Pdiv.PullbackComparison.pφ₂ (spMap (Subring.inclusion h)) B) ψ₂
    (GlobalTheory.SiegDesc.isPullback_of_isSquare hpb.1 (Pdiv.PullbackComparison.isSquare _ B))
    (GlobalTheory.SiegDesc.isSquare_comp hψ₁ hsqψ (Pdiv.PullbackComparison.isSquare _ B) hsq) (GlobalTheory.SiegDesc.isSquare_w hψ₂ hsqψ)

  choose ψa hψa using fun a : Std g n => hSL a R₁ h (hSLs a) (Sp R₁) (𝟙 _) (spMap (Subring.inclusion h))
    (spMap R₁.subtype) IsPullback.of_id_snd hj (by simp)
  let l : Std g n → (Sp R₁ ⟶ A₁.left) := fun a => pullback.lift (ψa a) (𝟙 _)
    (by rw [(hψa a).2, Category.comp_id, Category.id_comp])
  have hl₁ : ∀ a, l a ≫ pullback.fst _ _ = ψa a := fun a => pullback.lift_fst _ _ _
  have hl₂ : ∀ a, l a ≫ A₁.hom = 𝟙 _ := fun a => pullback.lift_snd _ _ _
  let lv₁ : Std g n → (𝟙_ (Over (Sp R₁)) ⟶ A₁) := fun a => Over.homMk (l a) (hl₂ a)
  refine ⟨R₁, β.codRestrict R₁ (fun x => h (hβ x)), A₁, inferInstance, P₁, lv₁, hFT, by ext; rfl, hA₁, hA₁d, hP₁,
    ψ, ψ₂, hgp, hsqψ.1, hsqψ.2, hiso, fun a => ?_⟩
  have e : (lvOf c a).left ≫ c.A.hom = 𝟙 _ := Over.w (lvOf c a)
  apply pullback.hom_ext
  · change (lvOf c a).left ≫ ψ ≫ pullback.fst _ _ = spMap R₁.subtype ≫ l a ≫ pullback.fst _ _
    rw [hl₁]
    exact (congrArg ((lvOf c a).left ≫ ·) hψ₁).trans (hψa a).1.symm
  · change (lvOf c a).left ≫ ψ ≫ A₁.hom = spMap R₁.subtype ≫ l a ≫ A₁.hom
    rw [hψ₂, hl₂, reassoc_of% e, Category.comp_id]

end GlobalTheory.SiegFg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetWittFrameSchwartzBound
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.TorusTheta

theorem min_pow_le_of_mem_cone {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ}
    (ht : t ∈ GlobalTheory.SiegelSet.cone r c) (i : Fin r) : min 1 c ^ r ≤ t i := by
  obtain ⟨hpos, hstep, hlast⟩ := ht
  have hm0 : 0 < min 1 c := lt_min one_pos hc
  have hm1 : min 1 c ≤ 1 := min_le_left _ _
  have key : ∀ k : ℕ, ∀ i : Fin r, i.val + k + 1 = r → min 1 c ^ (k + 1) ≤ t i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simp only [zero_add, pow_one]
      exact (min_le_right _ _).trans (hlast i (by omega))
    | succ k ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have h1 := ih ⟨i.val + 1, hj⟩ (by simp; omega)
      have h2 := hstep i ⟨i.val + 1, hj⟩ rfl
      have h3 : 0 < t ⟨i.val + 1, hj⟩ := hpos _
      calc min 1 c ^ (k + 1 + 1) = min 1 c * min 1 c ^ (k + 1) := by ring
        _ ≤ min 1 c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_left h1 hm0.le
        _ ≤ c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_right (min_le_right _ _) h3.le
        _ ≤ t i := h2
  have := key (r - i.val - 1) i (by omega)
  refine le_trans ?_ this
  exact pow_le_pow_of_le_one hm0.le hm1 (by omega)

theorem mul_norm_le_norm_smul {ι V : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V] {c' : ℝ} (hc' : 0 < c')
    (s : ι → ℝ) (hs : ∀ i, c' ≤ s i) (v : ι → V) : c' * ‖v‖ ≤ ‖fun i => s i • v i‖ := by
  rw [← le_div_iff₀' hc']
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [le_div_iff₀' hc']
  have hsi : 0 < s i := hc'.trans_le (hs i)
  calc c' * ‖v i‖ ≤ s i * ‖v i‖ := mul_le_mul_of_nonneg_right (hs i) (norm_nonneg _)
    _ = ‖s i • v i‖ := by rw [norm_smul, Real.norm_of_nonneg hsi.le]
    _ ≤ ‖fun i => s i • v i‖ := norm_le_pi_norm (fun i => s i • v i) i

theorem prod_elim_pow {κ : Type} [Fintype κ] {r : ℕ} (blk : κ → Option (Fin r)) (t : Fin r → ℝ) (f d : ℕ)
    (hcard : ∀ i : Fin r, (Finset.univ.filter (fun j => blk j = some i)).card = 2 * d) :
    ∏ j, (blk j).elim 1 t ^ f = (∏ i, t i ^ (f * d)) ^ 2 := by
  rw [← Finset.prod_fiberwise (Finset.univ : Finset κ) blk (fun j => ((blk j).elim 1 t : ℝ) ^ f)]
  have h1 : ∀ o : Option (Fin r), ∏ j ∈ Finset.univ.filter (fun j => blk j = o), (blk j).elim 1 t ^ f =
      (o.elim 1 t ^ f) ^ (Finset.univ.filter (fun j => blk j = o)).card := by
    intro o
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.1 hj).2]
  rw [Finset.prod_congr rfl (fun o _ => h1 o), Fintype.prod_option]
  simp only [Option.elim_none, Option.elim_some, one_pow, one_mul, hcard]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

end GlobalTheory.TorusTheta

namespace GlobalTheory.TorusTheta

theorem theta_torus_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf → ∀ c : ℝ, 0 < c →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ a' : UA σ X.J,
      (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a → ∀ (y : UA σ X.J) (h : UA σ W.J),
      ‖theta om Φ (a' * y) h‖ ≤ C * ((ht y : ℝ) * ht h) ^ k * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt c hc Φ hΦ
  obtain ⟨co, blk, hrat, hcard, hact⟩ := GlobalTheory.T.witt_frame_darboux_coordinates F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt
  obtain ⟨M₁, om₁, e, c₀, hco, hP₁, hc₀, he⟩ := GlobalTheory.T.darboux_coords_rational_points F E σ B n d X W M χX χW om r s r' s' hP co hrat
  obtain ⟨N₀, k₃, C₃, hlat⟩ := GlobalTheory.LatScaleSum.thetaSum_norm_le_pow F (Fin n × Fin d)
  have heΦ := (he Φ hΦ).1
  obtain ⟨C₁, k₁, hdec⟩ := _root_.GlobalTheory.ArchDecay.om_bound_arch F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ (e Φ) heΦ N₀
  obtain ⟨C₂, k₂, hden⟩ := _root_.GlobalTheory.FinDenom.exists_denominator_of_finite_component F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ (e Φ) heΦ
  set c' : ℝ := min 1 c ^ r₀ with hc'def
  have hc'0 : 0 < c' := pow_pos (lt_min one_pos hc) _
  have hc'1 : c' ≤ 1 := pow_le_one₀ (lt_min one_pos hc).le (min_le_left _ _)
  refine ⟨‖c₀‖⁻¹ * |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃, k₁ + k₂ * k₃, ?_⟩
  intro t htc a hta a' ha' y h
  have tlow : ∀ i, c' ≤ t i := min_pow_le_of_mem_cone hc htc
  have tpos : ∀ i, 0 < t i := fun i => hc'0.trans_le (tlow i)
  set u : Fin n × Fin d → ℝ := fun j => (blk j).elim 1 t with hudef
  have hulow : ∀ j, c' ≤ u j := by
    intro j
    simp only [hudef]
    cases blk j with
    | none => exact hc'1
    | some i => exact tlow i
  have hupos : ∀ j, 0 < u j := fun j => hc'0.trans_le (hulow j)
  obtain ⟨κ, hκ, hom⟩ := GlobalTheory.T.torus_action_model_coordinates F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ a' u hupos
    (by rw [hco]; exact hact t tpos a hta a' ha')

  have hΨ0 : om (y, h) Φ ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ _ hΦ
  have hT : om (a', 1) (om (y, h) Φ) ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ _ hΨ0
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ, Ψ = om₁ (y, h) (e Φ) := ⟨_, rfl⟩
  have hΨ : Ψ ∈ schA F (Fin n × Fin d) := hΨdef ▸ (IsUWeilPair.isUSplitting hP₁.weil).pres _ _ heΦ
  have hmul : ((a' * y, h) : UA σ X.J × UA σ W.J) = (a', 1) * (y, h) := by
    ext <;> simp
  have hsplit : om (a' * y, h) Φ = om (a', 1) (om (y, h) Φ) := by
    rw [hmul, map_mul, Module.End.mul_apply]
  have heT : e (om (a', 1) (om (y, h) Φ)) = om₁ (a', 1) Ψ := by
    rw [(he _ hΨ0).2.2, (he Φ hΦ).2.2, hΨdef]
  have hthT : thetaSum F (om (a', 1) (om (y, h) Φ)) = c₀⁻¹ * thetaSum F (om₁ (a', 1) Ψ) := by
    rw [← heT, (he _ hT).2.1, ← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]
  have hfun : om₁ (a', 1) Ψ = fun x => κ * Ψ (fun j => infScale F (u j) * x j) := funext (hom Ψ hΨ)
  have hkey : theta om Φ (a' * y) h =
      c₀⁻¹ * (κ * thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))) := by
    show thetaSum F (om (a' * y, h) Φ) = _
    rw [hsplit, hthT, hfun]
    unfold thetaSum
    rw [tsum_mul_left]

  have hκ' : ‖κ‖ = ∏ i, t i ^ (Module.finrank ℚ F * d) := by
    have h2 : ‖κ‖ ^ 2 = (∏ i, t i ^ (Module.finrank ℚ F * d)) ^ 2 := by
      rw [hκ]
      exact prod_elim_pow blk t _ d hcard
    have hnn : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
      Finset.prod_nonneg fun i _ => pow_nonneg (tpos i).le _
    exact (pow_left_inj₀ (norm_nonneg _) hnn two_ne_zero).1 h2

  set P : ℝ := (ht y : ℝ) * ht h with hPdef
  have hP0 : 0 ≤ P := mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  obtain ⟨m, hm1, hmC, hmint⟩ := hden y h
  have hdecay : ∀ ξ : Fin n × Fin d → F,
      ‖Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j)‖ *
        (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ (c'⁻¹) ^ N₀ * (C₁ * P ^ k₁) := by
    intro ξ
    beta_reduce
    have h1 := hdec y h (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))
    rw [← hΨdef] at h1
    have hnorm : c' * ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
        ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖ := by
      simp only [evI_infScale_mul]
      exact mul_norm_le_norm_smul hc'0 u hulow _
    have hle : 1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
        c'⁻¹ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) := by
      have hi : 1 ≤ c'⁻¹ := one_le_inv₀ hc'0 |>.2 hc'1
      have h3 : ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
          c'⁻¹ * ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖ := by
        rw [le_inv_mul_iff₀ hc'0]; exact hnorm
      nlinarith [norm_nonneg (fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i)))]
    have hpow : (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤
        (c'⁻¹) ^ N₀ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀ := by
      have h0 : 0 ≤ 1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ :=
        add_nonneg zero_le_one (norm_nonneg _)
      have h4 := pow_le_pow_left₀ h0 hle N₀
      rw [mul_pow] at h4
      exact h4
    calc ‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀
        ≤ ‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          ((c'⁻¹) ^ N₀ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (c'⁻¹) ^ N₀ * (‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀) := by ring
      _ ≤ (c'⁻¹) ^ N₀ * (C₁ * P ^ k₁) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hint : ∀ ξ : Fin n × Fin d → F,
      Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j) ≠ 0 →
        ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
    intro ξ hne
    rw [hΨdef] at hne
    exact hmint _ ξ (fun i => infScale_mul_snd F (u i) _) hne
  have hS := hlat ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) m (fun x => Ψ (fun j => infScale F (u j) * x j)) hm1 hdecay hint

  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmk : (m : ℝ) ^ k₃ ≤ |C₂| ^ k₃ * P ^ (k₂ * k₃) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ hm0 (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hP0 _))) k₃
  have hS' : ‖thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))‖ ≤
      |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃) := by
    refine hS.trans ?_
    calc C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) * (m : ℝ) ^ k₃
        ≤ |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) * (m : ℝ) ^ k₃ := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hm0 _)
          calc C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) ≤ |C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁))| := le_abs_self _
            _ = |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (c'⁻¹) ^ N₀),
                abs_of_nonneg (pow_nonneg hP0 _)]
      _ ≤ |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) * (|C₂| ^ k₃ * P ^ (k₂ * k₃)) :=
          mul_le_mul_of_nonneg_left hmk (by positivity)
      _ = |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃) := by ring
  rw [hkey, norm_mul, norm_mul, norm_inv, hκ']
  have hT0 : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (tpos i).le _
  calc ‖c₀‖⁻¹ * ((∏ i, t i ^ (Module.finrank ℚ F * d)) * ‖thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))‖)
      ≤ ‖c₀‖⁻¹ * ((∏ i, t i ^ (Module.finrank ℚ F * d)) *
          (|C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃))) := by gcongr
    _ = _ := by ring

end GlobalTheory.TorusTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyAbelianVarietyAlgClosed
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exists_fin_affineOpen_cover_of_compactSpace (X : Scheme.{0}) [CompactSpace X] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  obtain ⟨Us, hUs, hfin, hU⟩ :=
    X.isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) isCompact_univ
  let s := hfin.toFinset
  refine ⟨s.card, fun i => (s.equivFin.symm i).1, fun i => ?_, ?_⟩
  · have h := (s.equivFin.symm i).2
    exact hUs (hfin.mem_toFinset.mp h)
  · apply le_antisymm le_top
    rw [hU]
    refine sSup_le fun u hu => ?_
    have hs : u ∈ s := hfin.mem_toFinset.mpr hu
    refine le_iSup_of_le (s.equivFin ⟨u, hs⟩) ?_
    simp

theorem structureSheafCoh_abelianVariety_algClosed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ),
      IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
      Module.Finite K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g ∧
        GlobalTheory.AbCoh.WedgeO (OAff A.hom) ∧ GlobalTheory.AbCoh.NoPrimitiveStructureSheafH2 A ∧ GlobalTheory.AbCoh.AxesVanishingStructureSheafDegOne A := by
  intro K _ _ A _ g hA hg
  obtain ⟨hax, -, hrk⟩ := _root_.GlobalTheory.AbCoh.Axes.main K A g hA hg
  obtain ⟨hw, hno⟩ := _root_.GlobalTheory.AbCoh.wedgeO_noPrimO2 K A g hA hg
  refine ⟨?_, hrk, hw, hno, hax⟩
  haveI : IsProper A.hom := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  obtain ⟨n, D, hD, hcov⟩ := exists_fin_affineOpen_cover_of_compactSpace A.left
  obtain ⟨⟨e⟩, -⟩ := _root_.GlobalTheory.AbCoh.hO_equiv_cech K A.left A.hom (Fin n) D inferInstance hD hcov
  obtain ⟨hfin, -, -⟩ := _root_.GlobalTheory.AbCoh.FDim.cechLB_triv_finrank_one_two K A g hA hg (Fin n) D hD hcov
  exact Module.Finite.equiv e.symm

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveIffPtMapSurjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem surjective_iff_ptMap_surjective : ∀ (K : Type) [Field K] (A B : AbVar K) (p : A ⟶ B),
    Surjective p.hom.left ↔ Function.Surjective (ptMap p) := by
  intro K _ A B p
  have hAs : Smooth A.X.hom := A.ab.smooth
  have hBs : Smooth B.X.hom := B.ab.smooth
  have hBp : IsProper B.X.hom := B.ab.proper
  have hw : p.hom.left ≫ B.X.hom = A.X.hom := Over.w p.hom
  have hlft : LocallyOfFiniteType p.hom.left := by
    have : LocallyOfFiniteType (p.hom.left ≫ B.X.hom) := by rw [hw]; infer_instance
    exact locallyOfFiniteType_of_comp p.hom.left B.X.hom
  constructor
  · intro hs y
    obtain ⟨u, hu⟩ := hs.surj (y.left (IsLocalRing.closedPoint (AlgebraicClosure K)))
    obtain ⟨w, hw'⟩ := GlobalTheory.CovLift.exists_lift_of_locallyOfFiniteType _ _ p.hom.left hlft
      (AlgebraicClosure K) y.left u hu
    refine ⟨Over.homMk w ?_, ?_⟩
    · change w ≫ A.X.hom = spMap (algebraMap K (AlgebraicClosure K))
      rw [← hw, ← Category.assoc, hw']
      exact Over.w y
    · apply Over.OverMorphism.ext
      simpa using hw'
  · intro hs
    have : IsProper (p.hom.left ≫ B.X.hom) := by rw [hw]; exact A.ab.proper
    have hp : IsProper p.hom.left := IsProper.of_comp p.hom.left B.X.hom
    have hcl : IsClosed (Set.range p.hom.left) := p.hom.left.isClosedMap.isClosed_range
    have hJ : JacobsonSpace B.X.left := LocallyOfFiniteType.jacobsonSpace B.X.hom
    have hsub : closedPoints B.X.left ⊆ Set.range p.hom.left := by
      intro b hb
      let t : Sp (AlgebraicClosure K) ⟶ Sp K := spMap (algebraMap K (AlgebraicClosure K))
      haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
      obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := B.X.hom) (g := t) b
        (IsLocalRing.closedPoint (AlgebraicClosure K)) (Subsingleton.elim _ _)
      have : JacobsonSpace ↥(pullback B.X.hom t : Scheme.{0}) :=
        LocallyOfFiniteType.jacobsonSpace (pullback.snd B.X.hom t)
      have hF : IsClosed ((pullback.fst B.X.hom t) ⁻¹' {b}) :=
        (show IsClosed {b} from hb).preimage (pullback.fst B.X.hom t).continuous
      obtain ⟨c, hcF, hc'⟩ := nonempty_inter_closedPoints (X := ↥(pullback B.X.hom t : Scheme.{0}))
        (Z := (pullback.fst B.X.hom t) ⁻¹' {b}) ⟨z, hz⟩ hF.isLocallyClosed
      have hc : IsClosed {c} := hc'
      let x0 : Sp (AlgebraicClosure K) ⟶ B.X.left :=
        pointOfClosedPoint (pullback.snd B.X.hom t) c hc ≫ pullback.fst B.X.hom t
      have hx0 : x0 ≫ B.X.hom = t := by
        simp only [x0, Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
      obtain ⟨x, hx⟩ := hs (Over.homMk x0 hx0 : ptOver K (AlgebraicClosure K) ⟶ B.X)
      refine ⟨x.left (IsLocalRing.closedPoint (AlgebraicClosure K)), ?_⟩
      have e : x.left ≫ p.hom.left = x0 := congrArg CommaMorphism.left hx
      have e3 : p.hom.left (x.left (IsLocalRing.closedPoint (AlgebraicClosure K))) =
          x0 (IsLocalRing.closedPoint (AlgebraicClosure K)) := by
        rw [← e]; rfl
      have e4 : x0 (IsLocalRing.closedPoint (AlgebraicClosure K)) = pullback.fst B.X.hom t c := by
        change pullback.fst B.X.hom t (pointOfClosedPoint (pullback.snd B.X.hom t) c hc
          (IsLocalRing.closedPoint (AlgebraicClosure K))) = _
        exact congrArg (pullback.fst B.X.hom t) (pointOfClosedPoint_apply (pullback.snd B.X.hom t) c hc _)
      rw [e3, e4]
      exact hcF
    have huniv : Set.univ ⊆ Set.range p.hom.left := by
      rw [← closure_closedPoints]
      exact closure_minimal hsub hcl
    exact ⟨fun b => huniv (Set.mem_univ b)⟩

end GlobalTheory.AV.AbVar
end

