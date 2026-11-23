module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0106
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelMapGenericallyOpenImmersionCalculus
public import Lean.Elab.Command
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGrpObjOfStrictBirationalLaw
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModelBirationalGroupLaw
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsStrictModelOfBirational
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModel

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisAlongOfIndependentFibres
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.GenericSectionBasis

namespace GlobalTheory.TraitBasis

theorem toStk_valF_eq_gs {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F)
    (h : x z ∈ U) (a : Γ(X, U)) : toStk z (valF x U a) = gs x z U a := by
  rw [valF, dite_eq_left ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

theorem toStk_eq_cst {F : Type} [Field F] (z : Sp F) (a : F) : toStk z a = cst (𝟙 (Sp F)) z a := by
  rw [cst, gs_eq _ z ⊤ trivial]; rfl

theorem gs_eq_zero_of_notMem {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F)
    (h : x z ∈ U) (a : Γ(X, U)) (ha : x z ∉ X.basicOpen a) : gs x z U a = 0 := by
  by_cases h0 : valF x U a = 0
  · rw [← toStk_valF_eq_gs x U z h, h0, map_zero]
  · refine (ha ?_).elim
    have u : IsUnit (gs x z U a) := by
      rw [← toStk_valF_eq_gs x U z h]; exact (IsUnit.mk0 _ h0).map _
    rw [gs_stalkMap x z U h, isUnit_map_iff, gs_eq (𝟙 X) (x z) U h] at u
    exact (X.mem_basicOpen a (x z) h).2 u

theorem map_eq_zero_of_points {X B Y : Scheme.{0}} {M : LB X} (π : X ⟶ B) {n : ℕ} (b : Fin n → LB.Sec M)
    {K : Type} [Field K]
    (H : ∀ (x : Sp K ⟶ B) (c : Fin n → K),
      (∀ (g : Sp K ⟶ X) j, g ≫ π = x → ∑ i, c i * valF g _ ((b i).f j) = 0) → c = 0)
    {R : Type} [CommRing R] {χ : Sp R ⟶ B} {p : Y ⟶ Sp R} {r : Y ⟶ X} (hp : IsPullback r p π χ)
    (κ : R →+* K) (c : Fin n → R)
    (h0 : ∀ (g : Sp K ⟶ Y) (z : Sp K) j, g ≫ p = spMap κ → (g ≫ r) z ∈ M.U j →
      ∑ i, cst (g ≫ p) z (c i) * gs (g ≫ r) z (M.U j) ((b i).f j) = 0) (i : Fin n) : κ (c i) = 0 := by
  refine congrFun (H (spMap κ ≫ χ) (fun i => κ (c i)) fun g j hg => ?_) i
  obtain ⟨g', rfl, h₂⟩ : ∃ g' : Sp K ⟶ Y, g' ≫ r = g ∧ g' ≫ p = spMap κ :=
    ⟨hp.lift g (spMap κ) hg, hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  let z : Sp K := (default : PrimeSpectrum K)
  by_cases hz : (g' ≫ r) z ∈ M.U j
  · apply (toStk z).injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, ← h0 g' z j h₂ hz, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, toStk_valF_eq_gs _ _ z hz, toStk_eq_cst, h₂, H1.gs_spec]
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [valF, dite_eq_right (fun h => hz ((top_le_iff_mem _ _ z).1 h)), mul_zero]

theorem exists_comb_of_independent {F : Type} [Field F] {Y : Scheme.{0}} {M : LB Y} {p : Y ⟶ Sp F} {n : ℕ}
    (H : HasBasis M p n) (β : Fin n → LB.Sec M)
    (ind : ∀ c : Fin n → F, (∀ j, ∑ i, Out.resTop _ (Out.scal p (c i)) * (β i).f j = 0) → c = 0)
    (s : LB.Sec M) : ∃ c, IsComb p β c s := by
  obtain ⟨e, he⟩ := H
  choose m hm using fun i => (he (β i)).exists
  have key : ∀ (c : Fin n → F) j, ∑ i, Out.resTop _ (Out.scal p (c i)) * (β i).f j =
      ∑ k, Out.resTop _ (Out.scal p (Matrix.vecMul c (Matrix.of m) k)) * (e k).f j := fun c j => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [fun i => hm i j, SaturatedSections.cst_eq, Matrix.vecMul, dotProduct, map_sum, map_mul,
      Finset.mul_sum, Finset.sum_mul, Matrix.of_apply, _root_.mul_assoc]
    exact Finset.sum_comm
  have inj : Function.Injective (Matrix.vecMulLinear (Matrix.of m)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    refine ind c fun j => ?_
    have hc' : Matrix.vecMul c (Matrix.of m) = 0 := hc
    rw [key, hc']
    simp only [SaturatedSections.cst_eq, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
  obtain ⟨d, hd, -⟩ := he s
  obtain ⟨c, hc⟩ := LinearMap.injective_iff_surjective.1 inj d
  refine ⟨c, fun j => ?_⟩
  have hc' : Matrix.vecMul c (Matrix.of m) = d := hc
  rw [key, hc']
  exact hd j

theorem existsUnique_comb {X B Y A G : Scheme.{0}} {L : LB G} (hL : L.IsLB) (q : X ⟶ G) (π : X ⟶ B) (N : ℤ)
    {n : ℕ} (b : Fin n → LB.Sec (LB.LinComb L (fun _ : Fin 1 => q) (fun _ => N)))
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ B) (c : Fin n → K),
      (∀ (g : Sp K ⟶ X) j, g ≫ π = x → ∑ i, c i * valF g _ ((b i).f j) = 0) → c = 0)
    {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {χ : Sp W ⟶ B} {p : Y ⟶ Sp W} [Flat p]
    {r : Y ⟶ X} (hp : IsPullback r p π χ) {a : A ⟶ Sp (FractionRing W)} {ρ : A ⟶ Y}
    (hρ : IsPullback ρ a p (Out.jK W)) {q' : Y ⟶ G} (hq : r ≫ q = q') {φ : A ⟶ G} (hφ : ρ ≫ q' = φ)
    (hb : HasBasis (LB.LinComb L (fun _ : Fin 1 => φ) (fun _ => N)) a n)
    (s : Fin n → LB.Sec (LB.LinComb L (fun _ : Fin 1 => q') (fun _ => N)))
    (hs : ∀ i (Z : Scheme.{0}) (u : Z ⟶ Y) (z : Z) j, u z ∈ LB.wchart L (fun _ : Fin 1 => q') j →
      gs u z (LB.wchart L (fun _ : Fin 1 => q') j) ((s i).f j) =
        gs (u ≫ r) z (LB.wchart L (fun _ : Fin 1 => q) j) ((b i).f j))
    (t : LB.Sec (LB.LinComb L (fun _ : Fin 1 => q') (fun _ => N))) : ∃! c : Fin n → W, IsComb p s c t := by
  subst hq hφ
  refine existsUnique_comb_of_independent_special_fibre W Y p _ (DVR.linComb_isLB L hL _ _) n s
    (fun c hc i => ?_) t ?_
  · let k := IsLocalRing.ResidueField W
    let κ : W →+* AlgebraicClosure k := (algebraMap k (AlgebraicClosure k)).comp (IsLocalRing.residue W)
    have hκ : ∀ w, κ w = 0 ↔ w ∈ IsLocalRing.maximalIdeal W := fun w =>
      (map_eq_zero_iff _ (algebraMap k (AlgebraicClosure k)).injective).trans (IsLocalRing.residue_eq_zero_iff w)
    refine (hκ _).1 (map_eq_zero_of_points π b (H _) hp κ c (fun g z j hg hz => ?_) i)
    have hz' : g z ∈ LB.wchart L (fun _ : Fin 1 => r ≫ q) j :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k
    have hcl : p (g z) = IsLocalRing.closedPoint W := by
      have e : p (g z) = spMap κ z := congrArg (fun u : Sp (AlgebraicClosure k) ⟶ Sp W => u z) hg
      rw [e]
      refine PrimeSpectrum.ext (Ideal.ext fun w => ?_)
      have e₂ : z = (⊥ : PrimeSpectrum (AlgebraicClosure k)) :=
        Subsingleton.elim (α := PrimeSpectrum (AlgebraicClosure k)) _ _
      subst e₂
      exact hκ w
    have e := gs_eq_zero_of_notMem g _ z hz' _ (hc j (g z) hz' hcl)
    refine Eq.trans ?_ ((gs_comb p s c g z j hz').symm.trans e)
    exact Finset.sum_congr rfl fun i _ => congrArg _ (hs i _ g z j hz').symm
  · choose s' hs' using fun i => exists_pull_gs (s i) ρ (fun _ : Fin 1 => ρ ≫ r ≫ q) (fun _ => rfl)
    obtain ⟨t', ht'⟩ := exists_pull_gs t ρ (fun _ : Fin 1 => ρ ≫ r ≫ q) (fun _ => rfl)
    obtain ⟨c, hc⟩ := exists_comb_of_independent hb s' (fun c hc => funext fun i => by
      let κ := algebraMap (FractionRing W) (AlgebraicClosure (FractionRing W))
      refine κ.injective ((map_eq_zero_of_points π b (H _) (hρ.paste_horiz hp) κ c
        (fun g z j hg hz => ?_) i).trans (map_zero κ).symm)
      have hz' : g z ∈ LB.wchart L (fun _ : Fin 1 => ρ ≫ r ≫ q) j :=
        Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k
      have hz₂ : (g ≫ ρ) z ∈ LB.wchart L (fun _ : Fin 1 => r ≫ q) j :=
        Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k
      have e := gs_comb a s' c g z j hz'
      rw [hc j] at e
      refine Eq.trans ?_ (e.symm.trans ((gs_eq g z _ hz' _).trans ((congrArg _ (map_zero _)).trans (map_zero _))))
      refine Finset.sum_congr rfl fun i _ => congrArg _ (Eq.symm ?_)
      exact (hs' i _ g z j hz').trans ((hs i _ (g ≫ ρ) z j hz₂).trans (by rw [Category.assoc]; rfl))) t'
    obtain ⟨⟨w, hw⟩, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors W) c
    choose d hd using hd
    refine ⟨w, d, nonZeroDivisors.ne_zero hw, fun j => ?_⟩
    have : IsDominant (Out.jK W) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective W (FractionRing W))).le.trans bot_le)⟩
    have := IsSchemeTheoreticallyDominant.of_isDominant (Out.jK W)
    have : IsSchemeTheoreticallyDominant ρ := IsSchemeTheoreticallyDominant.of_isPullback hρ.flip
    have : QuasiCompact ρ := MorphismProperty.of_isPullback (P := @QuasiCompact) hρ.flip inferInstance
    refine ρ.app_injective _ (fn_ext fun y hy => ?_)
    refine (gs_pull (𝟙 _) ρ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) ρ y _ hy _).symm)
    have hy' : (𝟙 A : A ⟶ A) y ∈ LB.wchart L (fun _ : Fin 1 => ρ ≫ r ≫ q) j :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
    have cc : ∀ v : W, cst ((𝟙 A ≫ ρ) ≫ p) y v = cst (𝟙 A ≫ a) y (algebraMap W (FractionRing W) v) := fun v => by
      rw [Category.assoc, hρ.w, ← Category.assoc]
      exact cst_comp _ _ y v
    refine Eq.trans ?_ (gs_comb p s d (𝟙 A ≫ ρ) y j hy).symm
    refine (gs_mul (𝟙 A ≫ ρ) y _ hy _ _).trans ?_
    refine (congrArg₂ (· * ·) (GlobalTheory.IndivisibleSection.gs_scal p (𝟙 A ≫ ρ) y _ hy w)
      ((ht' _ (𝟙 A) y j hy').symm.trans ((congrArg (gs (𝟙 A) y _) (hc j)).trans
        (gs_comb a s' c (𝟙 A) y j hy')))).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cc, cc, hd i, Algebra.smul_def, H1.cst_mul, _root_.mul_assoc]
    exact congrArg (fun v => _ * (_ * v)) (hs' i _ (𝟙 A) y j hy')

end GlobalTheory.TraitBasis


open GlobalTheory.TraitBasis in
theorem GlobalTheory.basisAlong_of_independent_fibres : Out.Laws → ∀ (Z : Scheme.{0}) (G : Over Z) [GrpObj G] (L : LB G.left) (N n : ℕ) (T : Over Z) (b : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T)), L.IsLB → IsSemiAbelian G → 1 ≤ N → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ T.left) (c : Fin n → K), (∀ (g : Sp K ⟶ (T ⊗ G).left) j, g ≫ (fst T G).left = x → ∑ i, c i * valF g _ ((b i).f j) = 0) → c = 0) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (χ : Sp W ⟶ T.left) (A : Out.PolAV (Sp (FractionRing W))) (φ : A.A.left ⟶ G.left), IsGrpPullback A.A G (Out.jK W ≫ χ ≫ T.hom) φ → LBIso A.L (L.pull φ) → n = N ^ A.g → GlobalTheory.LN.BasisAlong G L N (Over.homMk χ rfl : Over.mk (χ ≫ T.hom) ⟶ T) b := by
  intro laws Z G _ L N n T b hL hG hN H W _ _ _ hW χ A φ hφ hiso hn t
  have := hW.1
  have := hG.smooth
  let T' : Over Z := Over.mk (χ ≫ T.hom)
  let h : T' ⟶ T := Over.homMk χ rfl
  have P₀ : IsPullback (snd T G).left (fst T G).left G.hom T.hom := (IsPullback.of_hasPullback T.hom G.hom).flip
  have P₁ : IsPullback (snd T' G).left (fst T' G).left G.hom (χ ≫ T.hom) :=
    (IsPullback.of_hasPullback T'.hom G.hom).flip
  have e₁ : (h ▷ G).left ≫ (snd T G).left = (snd T' G).left := congrArg CommaMorphism.left (whiskerRight_snd h G)
  have e₂ : (h ▷ G).left ≫ (fst T G).left = (fst T' G).left ≫ χ :=
    congrArg CommaMorphism.left (whiskerRight_fst h G)
  have hp : IsPullback (h ▷ G).left (fst T' G).left (fst T G).left χ :=
    IsPullback.of_right (by rw [e₁]; exact P₁) e₂ P₀
  let ρ : A.A.left ⟶ (T' ⊗ G).left := P₁.lift φ (A.A.hom ≫ Out.jK W) (hφ.1.w.trans (Category.assoc _ _ _).symm)
  have r₁ : ρ ≫ (snd T' G).left = φ := P₁.lift_fst _ _ _
  have hρ : IsPullback ρ A.A.hom (fst T' G).left (Out.jK W) :=
    IsPullback.of_right (by rw [r₁]; exact hφ.1) (P₁.lift_snd _ _ _) P₁
  have : Flat (X := (T' ⊗ G).left) (Y := Sp W) (fst T' G).left :=
    MorphismProperty.of_isPullback (P := @Flat) P₁ inferInstance
  have hb : HasBasis (LB.LinComb L (fun _ : Fin 1 => φ) (fun _ => (N : ℤ))) A.A.hom n := by
    obtain ⟨w, hw⟩ := hiso
    have i := iso_linComb ((isGen_iff w).1 hw) (fun _ : Fin 1 => 𝟙 A.A.left) (fun _ => (N : ℤ))
    simp only [Category.id_comp] at i
    rw [hn]
    exact (hasBasis_field A N laws.secBaseChange hN).of_iso (DVR.linComb_isLB L hL _ _)
      (DVR.linComb_isLB _ A.isLB _ _) i.symm
  choose s hs using fun i => exists_pull_gs (b i) (h ▷ G).left (fun _ : Fin 1 => (snd T' G).left) (fun _ => e₁)
  have main := TraitBasis.existsUnique_comb hL (snd T G).left (fst T G).left (N : ℤ) b H hp hρ e₁ r₁ hb s hs t
  let ε : W ≃+* Γ(Sp W, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).symm.commRingCatIsoToRingEquiv
  have key : ∀ c : Fin n → W, IsComb (fst T' G).left s c t ↔ GlobalTheory.LN.Lin G L N h b (fun i => ε (c i)) t := fun c => by
    obtain ⟨u, hu⟩ := GenericSectionBasis.exists_comb (F := W) (fst T' G).left s c
    have ev : ∀ (z : (T' ⊗ G).left) J, Good L z J →
        sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) u (𝟙 _) z J =
        ∑ i, gs (fst T' G).left z ⊤ (ε (c i)) *
          sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) (b i) (h ▷ G).left z J := by
      intro z J hJ
      have hm := hJ.mem (fun _ : Fin 1 => (snd T' G).left) (𝟙 _)
      refine (congrArg (gs (𝟙 _) z _) (hu _)).trans ((gs_comb (F := W) (fst T' G).left s c (𝟙 _) z _ hm).trans ?_)
      refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ ?_
      · rw [Category.id_comp]; rfl
      · refine (hs i _ (𝟙 _) z _ hm).trans ?_
        rw [sval_of (b i) (h ▷ G).left z J (fun _ => J (𝟙 _ ≫ (snd T' G).left))
          (fun _ => by rw [e₁, Category.id_comp]), Category.id_comp (h ▷ G).left]
    constructor
    · intro hc z J hJ
      refine Eq.trans ?_ (ev z J hJ)
      exact congrArg (gs (𝟙 _) z _) ((hc _).trans (hu _).symm)
    · intro hc j
      exact (sec_ext_val hL (fun y J hJ => (hc y J hJ).trans (ev y J hJ).symm) j).trans (hu j)
  obtain ⟨c, hc, hu⟩ := main
  refine ⟨fun i => ε (c i), (key c).1 hc, fun c' hc' => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d : Fin n → W, c' = fun i => ε (d i) :=
    ⟨fun i => ε.symm (c' i), funext fun i => (ε.apply_symm_apply _).symm⟩
  rw [hu d ((key d).2 hc')]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisSectionsModK
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.AdaptedBasis

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FamDimension IsLocalRing

theorem exists_basis_of_iso {X Y Y₀ : Scheme.{0}} {n : ℕ} {L : LB X} (hL : L.IsLB) {K K' K₃ : Type} [Fintype K]
    [Fintype K'] [Fintype K₃] (h : Y₀ ⟶ Y) (π : Y ⟶ Y₀) (e₁ : h ≫ π = 𝟙 _) (e₂ : π ≫ h = 𝟙 _)
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y₀ ⟶ X)} {ε' : K' → ℤ} {φ₃ : K₃ → (Y₀ ⟶ X)} {ε₃ : K₃ → ℤ}
    (u : LB.Gen (LB.LinComb L φ₃ ε₃)) (hu : u.IsGen)
    (hf : FormEq (Sum.elim (fun k => h ≫ φ k) φ₃) (Sum.elim ε ε₃) φ' ε')
    {A : Type} (g : A → Γ(Y₀, ⊤)) (b : Fin n → LB.Sec (LB.LinComb L φ ε))
    (hb : ∀ s, ∃! c : Fin n → A, IsComb b (fun i => π.appTop.hom (g (c i))) s) :
    ∃ b' : Fin n → LB.Sec (LB.LinComb L φ' ε'), ∀ s, ∃! c : Fin n → A, IsComb b' (fun i => g (c i)) s := by
  have h' : FormEq (Sum.elim (fun k => π ≫ φ' k) (fun k => π ≫ φ₃ k)) (Sum.elim ε' fun k => -ε₃ k) φ ε :=
    fun U _ w => by
      have := hf U (fun ψ => w (π ≫ ψ))
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, ← Category.assoc, e₂, Category.id_comp]
        at this ⊢
      rw [← this]
      simp only [zpow_neg, Finset.prod_inv_distrib, mul_inv_cancel_right]
  choose b' hb' using fun i => exists_sec hL hf (pullMulSec (b i) h u hu)
  refine ⟨b', fun s => ?_⟩
  have hu' := pullGen_isGen L _ _ _ (invGen_isGen L _ _ u hu) π
  obtain ⟨t, ht⟩ := exists_sec hL h' (pullMulSec s π (LB.pullGen L _ _ (LB.invGen L _ _ u) π) hu')
  refine (existsUnique_congr fun c => ⟨fun H => ?_, fun H => ?_⟩).1 (hb t)
  · refine (isComb_iff_sval hL _ _ _).2 fun y J hJ => ?_
    have E := SectionScalarValuation.sval_lin _ b H h y hJ
    rw [ht _ _ y J hJ, sval_pullMulSec _ _ _ hu' _ y hJ, val_pull hJ, val_inv, e₁, Units.mul_inv_eq_iff_eq_mul,
      Finset.sum_mul] at E
    refine E.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [hb' i _ _ y J hJ, sval_pullMulSec _ _ _ hu _ y hJ, Category.id_comp, _root_.mul_assoc]
    congr 1
    exact (gs_pull h π y ⊤ trivial _).trans (by rw [e₁])
  · refine (isComb_iff_sval hL _ _ _).2 fun y J hJ => ?_
    have E := SectionScalarValuation.sval_lin _ b' H π y hJ
    rw [ht _ _ y J hJ, sval_pullMulSec _ _ _ hu' _ y hJ, val_pull hJ, val_inv, Units.mul_inv_eq_iff_eq_mul,
      Finset.sum_mul, Category.id_comp]
    refine E.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [hb' i _ _ y J hJ, sval_pullMulSec _ _ _ hu _ y hJ, e₂, _root_.mul_assoc]
    congr 1

theorem exists_isBasisB (hT : SecTwistSt) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R)
    {k : ℕ} (hk : 1 ≤ k) (α : D.X) : ∃ b : Fin (k ^ D.P.g) → D.SecB k α, IsBasisB D b := by
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 _)
  obtain ⟨⟨b, hb⟩, -⟩ := hT _ D.P k hk R (𝟙 _) (SectionScalarValuation.cQ D T α)
  let a : D.P.A ⟶ T := Over.homMk D.P.A.hom (Category.comp_id _)
  have ha : ∀ {Z : Over (Spec (CommRingCat.of R))} (x y : Z ⟶ T), x = y := fun x y =>
    Over.OverMorphism.ext (((Category.comp_id _).symm.trans (Over.w x)).trans
      ((Category.comp_id _).symm.trans (Over.w y)).symm)
  let h : D.P.A ⟶ T ⊗ D.P.A := lift a (𝟙 _)
  have e₁ : h ≫ snd T D.P.A = 𝟙 _ := lift_snd _ _
  have e₂ : snd T D.P.A ≫ h = 𝟙 _ := CartesianMonoidalCategory.hom_ext _ _ (ha _ _)
    (by rw [Category.assoc, e₁, Category.comp_id, Category.id_comp])
  obtain ⟨e, he⟩ := exists_gen_of_local (V := R) D.P.L D.P.isLB (K := Fin 2)
    ![(SectionScalarValuation.cQ D T α).left, (1 : T ⟶ D.P.A).left] ![-1, 1]
  have e₃ : (snd T D.P.A).left ≫ D.P.A.hom = (fst T D.P.A).left :=
    congrArg (fun q => q.left) (ha (snd T D.P.A ≫ a) (fst T D.P.A))
  obtain ⟨b', hb'⟩ := exists_basis_of_iso D.P.isLB h.left (snd T D.P.A).left (congrArg (fun q => q.left) e₁)
    (congrArg (fun q => q.left) e₂) (φ' := D.famφB α) (ε' := DegPre.famε k)
    (LB.pullGen D.P.L _ _ e a.left) (pullGen_isGen _ _ _ _ he _) (fun U _ w => by
      have p := SectionScalarValuation.prod_famB D (𝟙 _) α k w
      simp only [Over.id_left, Category.id_comp] at p
      rw [p]
      have a₀ : h.left ≫ (snd T D.P.A).left = 𝟙 _ := congrArg (fun q => q.left) e₁
      have a₁ : a.left ≫ (SectionScalarValuation.cQ D T α).left = (SectionScalarValuation.cQ D D.P.A α).left := congrArg (fun x => x.left) (SectionScalarValuation.comp_cQ D a α)
      have a₂ : a.left ≫ (1 : T ⟶ D.P.A).left = (1 : D.P.A ⟶ D.P.A).left :=
        congrArg (fun x : D.P.A ⟶ D.P.A => x.left) (MonObj.comp_one (M := D.P.A) a)
      have a₃ : h.left ≫ (translPt D.P.A (SectionScalarValuation.cQ D T α)).left = (𝟙 D.P.A * SectionScalarValuation.cQ D D.P.A α).left := by
        have : h ≫ translPt D.P.A (SectionScalarValuation.cQ D T α) = 𝟙 D.P.A * SectionScalarValuation.cQ D D.P.A α := by
          show h ≫ ((fst T D.P.A ≫ SectionScalarValuation.cQ D T α) * snd T D.P.A) = _
          rw [MonObj.comp_mul, e₁, ← Category.assoc, SectionScalarValuation.comp_cQ, mul_comm]
        exact congrArg (fun x => x.left) this
      rw [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_two, ← _root_.mul_assoc]
      refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg₂ (· * ·) (congrArg (fun x => w x ^ ((k : ℤ) - 1)) a₀) ?_)
        ?_) ?_
      · exact (zpow_one _).trans (congrArg w a₃)
      · exact (zpow_neg_one _).trans (congrArg (fun x => (w x)⁻¹) a₁)
      · exact (zpow_one _).trans (congrArg w a₂)) (scal D.P.A.hom) b (fun s => by
      refine (Equiv.existsUnique_congr (Equiv.piCongrRight fun _ : Fin (k ^ D.P.g) =>
        (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toEquiv) fun c => ?_).2 (hb s)
      have : ∀ x : R, (snd T D.P.A).left.appTop.hom (scal D.P.A.hom x) = (fst T D.P.A).left.appTop.hom
          ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) := fun x => by
        rw [← e₃]; rfl
      simp only [this]
      rfl)
  exact ⟨b', hb'⟩

theorem isBasisB_reindex {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {k : ℕ} {α : D.X} {I I' : Type}
    [Fintype I] [Fintype I'] (ε : I ≃ I') {b : I' → D.SecB k α} (hb : IsBasisB D b) {β : I → D.SecB k α}
    (h : ∀ i, β i = b (ε i)) : IsBasisB D β := fun s => by
  refine (Equiv.existsUnique_congr (Equiv.arrowCongr ε (Equiv.refl R)) fun a => forall_congr' fun j => ?_).2 (hb s)
  refine Eq.congr_right (Fintype.sum_equiv ε _ _ fun i => ?_)
  simp [h]

section Family

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} {D : DegData V (maximalIdeal V)}


open GlobalTheory.FamInt in
theorem exists_int_of_vge (hϖ : Irreducible ϖ) {k : ℕ} {α : D.toPre.X}
    {s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))} {r : ℚ}
    (hr : 0 ≤ r) (hs : VGe D (FractionRing V) (ordVal hϖ) k α s r) :
    ∃ f : D.toPre.SecB k α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) s
        (D.toPre.famφB α) (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left 1 := by
  obtain ⟨n, a, σ, σF, hσ, hva, hsum⟩ := hs
  choose b hb using fun i => (le_ordFn_iff hϖ (a i) 0).1 (le_trans (by exact_mod_cast hr) (hva i))
  refine ⟨secLin (fun i => scal D.toPre.P.A.hom (b i)) σ, SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_⟩
  rw [SectionScalarValuation.sval_lin (fun i => scal D.toPre.P.A.hom (b i)) σ (fun _ => rfl) _ y hJ,
    SectionScalarValuation.sval_lin (fun i => gF D.toPre (FractionRing V) (a i)) σF (fun j => hsum j) (𝟙 _) y hJ]
  refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ (SectionScalarValuation.secScal_sval (hσ i) _ y hJ)
  have e1 : gs (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) y ⊤ (scal D.toPre.P.A.hom (b i)) =
      cst ((𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom) y (b i) :=
    gs_pull _ _ y ⊤ trivial _
  have e2 : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (a i)) =
      cst (𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) y (a i) :=
    gs_pull _ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial _
  have e3 : (𝟙 _ ≫ (DegPre.prB D.toPre (FractionRing V)).left) ≫ D.toPre.P.A.hom =
      ((𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) ≫
        spMap (algebraMap (FractionRing V) (FractionRing V))) ≫ spMap (algebraMap V (FractionRing V)) := by
    rw [Category.id_comp, Category.id_comp, Category.assoc, Over.w]
    exact (Over.w (fst (TF (R := V) (FractionRing V)) D.toPre.P.A)).symm
  rw [e1, e2, e3, cst_comp, cst_comp, hb i, zpow_zero, _root_.one_mul]
  rfl

theorem integralFamily_of_min (hG : GlobalFnsSt) (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ}
    (hQ : QForm.IsQ D.toPre ϖ Q) {q : ℕ} (hq : 1 ≤ q) (χ : D.toPre.X) (β : D.toPre.SecB q χ)
    (hmin : ∀ z, Q χ ≤ Q (χ + q • z)) :
    ∃ (Φ : Fam D.toPre (FractionRing V) q) (f : ∀ α, D.toPre.SecB q α), FamOf D.toPre _ f Φ ∧ f χ = β ∧
      ∀ α, (∀ z, α ≠ χ + q • z) → ∀ j, (f α).f j = 0 := by
  obtain ⟨σ, hσ⟩ := FamInt.exists_pull (F := FractionRing V) β
  obtain ⟨Φ, hΦ, hΦ0⟩ := FamFree.exists_fam_single (F := FractionRing V) hG D.tau_bimult hq χ σ
  have h0 : VGe D (FractionRing V) (FamInt.ordVal hϖ) q χ (Φ.s χ) 0 := by
    refine ⟨1, fun _ => 1, fun _ => β, fun _ => Φ.s χ, fun _ => hΦ ▸ hσ, fun _ => ?_, fun j => ?_⟩
    · simp
    · simp [DegPre.constBF]
  have key : ∀ α : D.toPre.X, ∃ f : D.toPre.SecB q α,
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α)
        (D.toPre.famφB α) (DegPre.famε q) f (DegPre.prB D.toPre (FractionRing V)).left 1 ∧
      (∀ h : χ = α, f = h ▸ β) ∧ ((∀ z, α ≠ χ + q • z) → ∀ j, f.f j = 0) := by
    intro α
    by_cases hα : χ = α
    · subst hα
      exact ⟨β, hΦ ▸ hσ, fun _ => rfl, fun h => absurd (by simp) (h 0)⟩
    by_cases hc : ∃ z, α = χ + q • z
    · obtain ⟨z, rfl⟩ := hc
      have H := SectionScalarValuation.fe_move hϖ hQ (FamInt.valOver_ordVal hϖ) q z χ Φ h0
      have hle := hmin z
      rw [q_shift hϖ hQ, le_add_iff_nonneg_right] at hle
      have hpos : (0 : ℤ) ≤ q * Q z + QForm.bOf D.toPre Q z χ := nonneg_of_mul_nonneg_right hle (by omega)
      obtain ⟨f, h1⟩ := exists_int_of_vge hϖ (by rw [zero_add]; exact_mod_cast hpos) H
      exact ⟨f, h1, fun h => absurd h hα, fun h => absurd rfl (h z)⟩
    · refine ⟨SecOps.secZero, SectionScalarValuation.secScal_of_sval D.toPre.P.isLB fun y J hJ => ?_, fun h => absurd h hα,
        fun _ _ => rfl⟩
      rw [UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _),
        UUA.sval_zero_of (hΦ0 α fun mu e => hc ⟨mu, e.symm⟩) _ y J (hJ.mem _ _)]
  choose f h1 h2 h3 using key
  exact ⟨Φ, f, h1, h2 χ rfl, h3⟩

end Family

theorem main : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (k : ℕ), 1 ≤ k → ∀ (J : Type) [Fintype J], Fintype.card J = k ^ S.g → ∃ (σ : J → (u.H k).Sec) (cls : J → u.D.toPre.X) (f : J → ∀ α, u.D.toPre.SecB k α), u.Basis l k σ cls f := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u l k hk J _ hJ
  obtain ⟨ϖ, Q, hϖ, hQ, hlt, hq⟩ := _root_.GlobalTheory.ZH.PsiForm.q_eq_val_mul o Ω S ρ p y₀ u l
  have hdim := (_root_.GlobalTheory.ZH.utest_dim_and_split hL o Ω S ρ p y₀ u).2.1
  let C := u.D.toPre.X ⧸ FamFree.multiples u.D.toPre k
  have hc : Nat.card C = k ^ Module.finrank ℤ u.D.toPre.X := AddSubgroup.index_range_nsmul u.D.toPre.X k
  have : Finite C := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have := Fintype.ofFinite C
  let e : J ≃ C × Fin (k ^ u.D.toPre.P.g) := Fintype.equivOfCardEq (by
    rw [hJ, Fintype.card_prod, Fintype.card_fin, ← Nat.card_eq_fintype_card, hc, ← pow_add, add_comm, hdim])
  choose rep hrep hmin using fun c : C => l.pos.exists_within_forall_le
    (s := {α | (QuotientAddGroup.mk α : C) = c}) ⟨c.out, c.out_eq⟩
  have hsh : ∀ c, Short l.q k (rep c) := fun c m =>
    hmin c _ (((FamFree.mk_eq_mk_iff _ _).2 ⟨m, rfl⟩).symm.trans (hrep c))
  have hpos : 0 < -Real.log ‖(u.j ϖ : PadicAlgCl p)‖ := by
    refine neg_pos.2 (Real.log_neg (norm_pos_iff.2 ?_) hlt)
    exact (map_ne_zero (algebraMap (FractionRing u.V) (PadicAlgCl p))).2 ((map_ne_zero_iff _ (IsFractionRing.injective u.V (FractionRing u.V))).2 hϖ.ne_zero)
  have hQmin : ∀ c z, Q (rep c) ≤ Q (rep c + k • z) := fun c z => by
    have := hsh c z
    rw [hq, hq] at this
    exact_mod_cast le_of_mul_le_mul_right this hpos
  choose b hb using fun c => exists_isBasisB hL.2.1.secTwist u.D.toPre hk (rep c)
  choose Φ f hΦ hf hz using fun c m => integralFamily_of_min hL.1.globalFns hϖ hQ hk (rep c) (b c m) (hQmin c)
  choose σ hσ using fun c m => GlobalTheory.IntegralExpansion.main hL.1 u.V u.D u.A u.G u.U k hk (Φ c m) (f c m) (hΦ c m)
  have inj : ∀ c c', rep c = rep c' → c = c' := fun c c' h => (hrep c).symm.trans (by rw [h]; exact hrep c')
  refine ⟨fun i => σ (e i).1 (e i).2, fun i => rep (e i).1, fun i => f (e i).1 (e i).2, fun i => hsh _,
    fun i i' ⟨m, hm⟩ => ?_, fun α => ?_, fun i => hσ _ _, fun i => ⟨_, hΦ _ _⟩, fun i => hz _ _, fun i₀ => ?_⟩
  · exact congrArg rep ((hrep _).symm.trans (((FamFree.mk_eq_mk_iff _ _).2 ⟨m, hm.symm⟩).symm.trans (hrep _)))
  · obtain ⟨m, hm⟩ := (FamFree.mk_eq_mk_iff _ _).1 (hrep (QuotientAddGroup.mk α))
    refine ⟨e.symm (QuotientAddGroup.mk α, ⟨0, by positivity⟩), m, ?_⟩
    simp only [Equiv.apply_symm_apply]
    exact hm.symm
  · let ε : {i // rep (e i).1 = rep (e i₀).1} ≃ Fin (k ^ u.D.toPre.P.g) :=
      { toFun := fun i => (e i.1).2
        invFun := fun m => ⟨e.symm ((e i₀).1, m), by rw [Equiv.apply_symm_apply]⟩
        left_inv := fun i => Subtype.ext (
          e.symm_apply_eq.2 (Prod.ext (inj _ _ i.2).symm rfl))
        right_inv := fun m => by simp }
    refine isBasisB_reindex ε (hb (e i₀).1) fun i => ?_
    have key : ∀ c c' m, c = c' → f c m (rep c') = b c' m := by
      rintro c _ m rfl; exact hf c m
    exact key _ _ _ (inj _ _ i.2)

end GlobalTheory.AdaptedBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeutralGroupModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS

theorem exists_neutral_group_model : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → GlobalTheory.AbLaw.IsProjBy A.hom → ∃ (G : Model R A) (_ : GrpObj G.Y), SmConn G.Y ∧ IsMonHom G.e.hom ∧ ∃ c : ℕ, 1 ≤ c ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), ∃ s : 𝟙_ (Over (Sp R)) ⟶ G.Y, spMap (algebraMap R K) ≫ s.left = (a ^ c).left ≫ G.j := by
  intro R K _ _ _ _ _ hS A _ _ hA hP
  have h1 := hS.1
  have h3 := hS.2.2.1
  have h4 := hS.2.2.2
  obtain ⟨n, M, hI, hW⟩ := _root_.GlobalTheory.SS.WeakNeronEx.exists_weakNeron R K inferInstance A hA.smooth hA.proper hP
  obtain ⟨N, hN, c, hc, hT⟩ := _root_.GlobalTheory.SS.NeutralModel.exists_birLaw R K hS A hA n M hI hW
  obtain ⟨N', hN', hle⟩ := _root_.GlobalTheory.SS.exists_strict_le R K hS A hA N hN
  obtain ⟨G, inst, hG, he, hs⟩ := _root_.GlobalTheory.SS.exists_grpObj_of_strict R K hS A hA N' hN'
  obtain ⟨b1, b2, b3, -, -⟩ := _root_.GlobalTheory.SS.GI.genIso_calculus R K hS
  refine ⟨G, inst, hG, he, c, hc, fun a => hs (a ^ c) ?_⟩
  have e1 : GenIso N' N (𝟙 A) := b1 A N' N hN'.1.1 hle
  have e2 : GenIso N N' (𝟙 A) := (b3 A A N' N (Iso.refl A)).1 e1
  have e3 := b2 A A A N' N N _ _ hN.1 e1 (hT a)
  have e4 := b2 A A A N' N N' _ _ hN.1 e3 e2
  simpa only [Category.id_comp, Category.comp_id] using e4

end GlobalTheory.SS
end

