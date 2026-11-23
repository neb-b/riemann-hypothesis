module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormFiniteFibresBirationalLinearSystem
section
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BirFiniteFibre

open GlobalTheory.Points

theorem aeval_smul_of_isHomogeneous {F K σ : Type} [CommRing F] [CommRing K] [Algebra F K] {d : ℕ}
    {p : MvPolynomial σ F} (hp : p.IsHomogeneous d) (c : K) (y : σ → K) :
    aeval (c • y) p = c ^ d * aeval y p := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hp (mem_support_iff.1 ha)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← this, Finsupp.degree_apply, mul_left_comm]

theorem compactSpace_Y {F : Type} [Field F] (S : LinSys F) (h : S.IsVariety) : CompactSpace S.Y := by
  obtain ⟨n, i, hi, e⟩ := h.proj
  have := isProper_str F n
  have : IsProper S.str := e ▸ inferInstance
  exact ⟨by simpa using QuasiCompact.isCompact_preimage (f := S.str) Set.univ isOpen_univ isCompact_univ⟩

theorem exists_finset_separating {F : Type} [Field F] (S : LinSys F) (h : S.IsVariety) (W : S.Y.Opens)
    (hW : IsAffineOpen W) : ∃ s : Finset Γ(S.Y, W), ∀ (K : Type) [Field K] [Algebra F K] (x x' : S.Pt K),
      ptOf x.1 ∈ W → ptOf x'.1 ∈ W → (∀ a ∈ s, valR x.1 W a = valR x'.1 W a) → x = x' := by
  obtain ⟨n, i, hi, e⟩ := h.proj
  have := isProper_str F n
  have : IsProper S.str := e ▸ inferInstance
  have hle : W ≤ S.str ⁻¹ᵁ ⊤ := le_top
  have hft : (S.str.appLE ⊤ W hle).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) S.str inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ hle
  letI := (S.str.appLE ⊤ W hle).hom.toAlgebra
  obtain ⟨s, hs⟩ : Algebra.FiniteType Γ(Sp F, ⊤) Γ(S.Y, W) := hft
  refine ⟨s, fun K _ _ x x' hx hx' H => Subtype.ext ?_⟩
  have h1 := (le_iff_ptOf_mem _ _).2 hx
  have h2 := (le_iff_ptOf_mem _ _).2 hx'
  refine ext_of_valR hW h1 h2 fun f => ?_
  have hf : f ∈ Algebra.adjoin Γ(Sp F, ⊤) (s : Set Γ(S.Y, W)) := hs ▸ Algebra.mem_top
  induction hf using Algebra.adjoin_induction with
  | mem a ha => exact H a ha
  | algebraMap r =>
    exact (valR_appLE x.1 S.str hle h1 r).trans
      ((congrArg (fun q => valR q ⊤ r) (x.2.trans x'.2.symm)).trans (valR_appLE x'.1 S.str hle h2 r).symm)
  | add a b _ _ ha hb => rw [valR_add _ _ h1, valR_add _ _ h2, ha, hb]
  | mul a b _ _ ha hb => rw [valR_mul _ _ h1, valR_mul _ _ h2, ha, hb]

theorem exists_form_finite_fibres : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → S.BasePointFree → S.Birational → ∃ (d : ℕ) (g : MvPolynomial (Fin S.N) F), g.IsHomogeneous d ∧ g ∉ S.imageIdeal ∧ ∀ (K : Type) [Field K] [Algebra F K] (y : Fin S.N → K), {x : S.Pt K | aeval (S.coords x.1) g ≠ 0 ∧ ∃ c : K, S.coords x.1 = c • y}.Finite := by
  intro F _ S hV hb hB
  classical
  haveI := compactSpace_Y S hV
  haveI := HeightExists.isPrime_imageIdeal hV
  have hcov : ∀ y : S.Y, ∃ W : S.Y.Opens, IsAffineOpen W ∧ y ∈ W := fun y => by
    obtain ⟨W, hW, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
    exact ⟨W, hW, hy⟩
  choose W hW hy using hcov
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set S.Y)) (fun y => (W y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩)
  choose s hs using fun z => exists_finset_separating S hV (W z) (hW z)
  choose d P Q hP hQ hQI _ hval using fun z a => GlobalTheory.T.exists_homogeneous_forms_quotient_birational_system F S hV hb hB (W z) a
  refine ⟨∑ z ∈ t, ∑ a ∈ s z, d z a, ∏ z ∈ t, ∏ a ∈ s z, Q z a, ?_, ?_, fun K _ _ y => ?_⟩
  · exact IsHomogeneous.prod _ _ _ fun z _ => IsHomogeneous.prod _ _ _ fun a _ => hQ z a
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨z, -, hz⟩
    rw [Ideal.IsPrime.prod_mem_iff] at hz
    obtain ⟨a, -, ha⟩ := hz
    exact hQI z a ha
  · have key : ∀ z ∈ t, ∀ a ∈ s z, ∀ x : S.Pt K, ptOf x.1 ∈ W z →
        aeval (S.coords x.1) (∏ z ∈ t, ∏ a ∈ s z, Q z a) ≠ 0 → (∃ c : K, S.coords x.1 = c • y) →
        valR x.1 (W z) a = aeval y (P z a) / aeval y (Q z a) := by
      rintro z hz a ha x hx hg ⟨c, hc⟩
      have h1 : aeval (S.coords x.1) (Q z a) ≠ 0 := by
        rw [map_prod, Finset.prod_ne_zero_iff] at hg
        have := hg z hz
        rw [map_prod, Finset.prod_ne_zero_iff] at this
        exact this a ha
      have h2 := hval z a K x hx
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hb.coords_ne_zero x.1 (hc.trans (zero_smul _ _))
      rw [hc, aeval_smul_of_isHomogeneous (hQ z a)] at h1 h2
      rw [aeval_smul_of_isHomogeneous (hP z a), mul_left_comm] at h2
      rw [eq_div_iff (right_ne_zero_of_mul h1)]
      exact mul_left_cancel₀ (pow_ne_zero _ hc0) h2
    refine (t.finite_toSet.biUnion (t := fun z => {x : S.Pt K | ptOf x.1 ∈ W z ∧
      aeval (S.coords x.1) (∏ z ∈ t, ∏ a ∈ s z, Q z a) ≠ 0 ∧ ∃ c : K, S.coords x.1 = c • y})
      fun z hz => Set.Subsingleton.finite fun x hx x' hx' => ?_).subset fun x hx => ?_
    · exact hs z K x x' hx.1 hx'.1 fun a ha =>
        (key z hz a ha x hx.1 hx.2.1 hx.2.2).trans (key z hz a ha x' hx'.1 hx'.2.1 hx'.2.2).symm
    · obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (ptOf x.1)))
      exact Set.mem_iUnion₂.2 ⟨z, hz, hxz, hx⟩

end GlobalTheory.BirFiniteFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackAlong
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.Pull

theorem tanScal_iff {S S' : Scheme.{0}} (f : S' ⟶ S) {O : Type} [Ring O] (A : Over S) [GrpObj A] (A' : Over S')
    [GrpObj A'] (φ : A'.left ⟶ A.left) (act : GlobalTheory.UPel.HT.OActN O A) (act' : GlobalTheory.UPel.HT.OActN O A')
    (h : IsGrpPullback A' A f φ) (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) (R' : Type) [CommRing R']
    (x : Sp R' ⟶ S') (b : O) (c : R') (v : GlobalTheory.UPel.HT.epsPtR x ⟶ A') (v₀ : GlobalTheory.UPel.HT.epsPtR (x ≫ f) ⟶ A)
    (hv : v₀.left = v.left ≫ φ) :
    GlobalTheory.UPel.HT.IsTanScal act' x b c v ↔ GlobalTheory.UPel.HT.IsTanScal act (x ≫ f) b c v₀ := by
  have one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ A').left ≫ φ :=
    (congrArg (fun z => z.left) (map_one (pushHom h (Over.mk x)))).symm
  have sc : spMap (epsScaleR c) ≫ spMap (algebraMap R' (DualNumber R')) =
      spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have E : (v₀ ≫ act.act b).left = (v ≫ act'.act b).left ≫ φ := by
    rw [Over.comp_left, Over.comp_left, hv, Category.assoc, Category.assoc, hact]
  refine and_congr ?_ ?_
  · rw [one, hv]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · rw [E, hv]
    refine ⟨fun E' => by rw [E']; exact Category.assoc _ _ _,
      fun E' => h.1.hom_ext (E'.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w (v ≫ act'.act b)).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)

theorem kerGen {S S' : Scheme.{0}} {f : S' ⟶ S} (A : Over S) [GrpObj A] (A' : Over S') [GrpObj A']
    (φ : A'.left ⟶ A.left) (h : IsGrpPullback A' A f φ) (P : LB (G2 A).left) (T : Over S') (x : T ⟶ A')
    (ht : ∃ t : ((P.pull (sqMap h.1.w)).pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    ∃ t : (P.pull (lift (snd A (Over.mk (T.hom ≫ f)) ≫ pushPt h.1.w x) (fst A (Over.mk (T.hom ≫ f)))).left).Gen,
      t.IsGen := by
  obtain ⟨t, ht⟩ := ht
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  let Z' : Over S' := Over.mk ((snd A T₀).left ≫ T.hom)
  have eq : (fst A T₀).left ≫ A.hom = Z'.hom ≫ f :=
    (Over.w (fst A T₀)).trans ((Over.w (snd A T₀)).symm.trans (Category.assoc _ _ _).symm)
  let a' : Z' ⟶ A' := Over.homMk (h.1.lift (fst A T₀).left Z'.hom eq) (h.1.lift_snd _ _ _)
  let t' : Z' ⟶ T := Over.homMk (snd A T₀).left rfl
  let u : Over.mk (Z'.hom ≫ f) ⟶ A ⊗ T₀ := Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ (A ⊗ T₀).hom = ((snd A T₀).left ≫ T.hom) ≫ f
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (snd A T₀)).symm)
  have hc : (lift (t' ≫ x) a').left ≫ sqMap h.1.w = u.left ≫ (lift (snd A T₀ ≫ pushPt h.1.w x) (fst A T₀)).left :=
    sqMap_of h.1.w u _ _ _ _ (Over.OverMorphism.ext (by
      show ((snd A T₀).left ≫ x.left) ≫ φ = 𝟙 _ ≫ (snd A T₀).left ≫ x.left ≫ φ
      rw [Category.id_comp, Category.assoc]))
      (Over.OverMorphism.ext (by
        show h.1.lift (fst A T₀).left Z'.hom eq ≫ φ = 𝟙 _ ≫ (fst A T₀).left
        rw [Category.id_comp, h.1.lift_fst]))
  have hψ : (lift a' t').left ≫ (lift (snd A' T ≫ x) (fst A' T)).left = (lift (t' ≫ x) a').left := by
    rw [← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst]
  obtain ⟨t₁, ht₁⟩ := gen_chartPull (chartPullIn P (fun _ : PUnit => sqMap h.1.w) (fun _ => 1)
    (lift (snd A' T ≫ x) (fst A' T)).left) t ht
  refine gen_chartPull (chartPullSame P (fun _ : PUnit => (lift (snd A T₀ ≫ pushPt h.1.w x) (fst A T₀)).left)
    (fun _ => (lift (snd A' T ≫ x) (fst A' T)).left ≫ sqMap h.1.w) (fun _ => 1) (lift a' t').left fun _ => ?_) t₁ ht₁
  rw [← Category.assoc, hψ, hc]
  exact (Category.id_comp _).symm

end GlobalTheory.UPel.HT.Pull

namespace GlobalTheory.UPel.HT.Pull

open GlobalTheory.UPel.HT

theorem exists_objMap : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : GlobalTheory.UPel.HT.Obj b N s), ∃ o' : GlobalTheory.UPel.HT.Obj b N (f ≫ s), Nonempty (GlobalTheory.UPel.HT.ObjMap o' o f) := by
  intro p _ D R _ b N S S' s f o
  have h := isGrpPullback_pullback o.A f
  have hact := OActN.pullback_left f o.A o.act
  have w := h.1.w
  let A' := (Over.pullback f).obj o.A
  let φ := pullback.fst o.A.hom f
  let act' := OActN.pullback f o.A o.act
  let φ₂ := sqMap w
  let P' := o.P.pull φ₂
  let u : Over.mk (A'.hom ≫ f) ⟶ o.A := Over.homMk φ w
  let U : Over.mk ((G2 A').hom ≫ f) ⟶ G2 o.A := lift (pushPt w (fst A' A')) (pushPt w (snd A' A'))
  have pa : ∀ {T : Over S'} (x : T ⟶ A') c, pushPt w (x ≫ act'.act c) = pushPt w x ≫ o.act.act c := fun x c =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have p1 : ∀ (T : Over S'), pushPt w (1 : T ⟶ A') = 1 := fun T => map_one (pushHom h T)
  have hP' : P'.IsLB := pull_isLB o.isLB φ₂

  have hΔ : (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left :=
    sqMap_of w u _ _ _ _ (Over.OverMorphism.ext (by simp [u, φ, pushPt_left])) (Over.OverMorphism.ext (by simp [u, φ, pushPt_left]))
  have hL : LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull φ) :=
    LBIso.chartPull (chartPullOut o.P (fun _ => φ₂) (fun _ => 1) _ (fun _ => _ ≫ φ₂) fun _ => rfl)
      (chartPullOut o.P (fun _ => _) (fun _ => 1) φ (fun _ => _ ≫ φ₂) fun _ => hΔ)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB o.isLB _))
  obtain ⟨hab, hamp, -⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally S S' o.A A' f φ
    _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) o.ab h hL

  have r₁ : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left :=
    sqMap_of w u _ _ _ _ ((p1 A').trans (MonObj.comp_one u).symm) (Over.OverMorphism.ext (by simp [u, φ, pushPt_left]))
  have r₂ : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left :=
    sqMap_of w u _ _ _ _ (Over.OverMorphism.ext (by simp [u, φ, pushPt_left])) ((p1 A').trans (MonObj.comp_one u).symm)
  have sw : (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd o.A o.A) (fst o.A o.A)).left :=
    sqMap_of w U _ _ _ _ (lift_snd _ _).symm (lift_fst _ _).symm
  have ro : ∀ c : D.O, (lift (fst A' A' ≫ act'.act c) (snd A' A')).left ≫ φ₂ =
      φ₂ ≫ (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left := fun c =>
    sqMap_of w U _ _ _ _ (by rw [pa, ← Category.assoc, lift_fst]) (lift_snd _ _).symm
  have ro' : ∀ c : D.O, (lift (fst A' A') (snd A' A' ≫ act'.act c)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act c)).left := fun c =>
    sqMap_of w U _ _ _ _ (lift_fst _ _).symm (by rw [pa, ← Category.assoc, lift_snd])
  have pul : ∀ {Y : Scheme.{0}} (g' : Y ⟶ (G2 A').left) {Y₀ : Scheme.{0}} (k : Y ⟶ Y₀) (g₀ : Y₀ ⟶ (G2 o.A).left), g' ≫ φ₂ = k ≫ g₀ → ChartPull (P'.pull g') (o.P.pull g₀) k :=
    fun g' _ k g₀ e => chartPullLinComb o.P φ₂ (fun _ => g') (fun _ => g₀) (fun _ => 1) k fun _ => e
  refine ⟨{ A := A'
            ab := hab
            act := act'
            P := P'
            isLB := hP'
            rig₁ := ?_
            rig₂ := ?_
            symm := ?_
            ample := hamp o.ample
            kerP := ?_
            rosati := ?_
            lie := ?_
            lieRank := ?_
            eta := fun y => GlobalTheory.ObjPull.secPull h (o.eta y)
            eta_add := fun x y => by rw [o.eta_add, map_mul]
            eta_lin := ?_
            eta_ker := fun x => by rw [o.eta_ker, map_one]
            geom := ?_ },
    ⟨{ φ := φ
       φ₂ := φ₂
       cart := h
       sq := isSquare_sqMap w
       act := hact
       pol := GlobalTheory.PolBaseChange.lbIso_refl hP'
       eta := fun y => GlobalTheory.ObjPull.secPull_left h _ }⟩⟩
  · obtain ⟨t, ht⟩ := o.rig₁
    exact gen_chartPull (pul _ φ _ r₁) t ht
  · obtain ⟨t, ht⟩ := o.rig₂
    exact gen_chartPull (pul _ φ _ r₂) t ht
  · exact LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.P φ₂ φ₂ rfl) (pul _ φ₂ _ sw) o.symm
  · obtain ⟨e, he, hk⟩ := o.kerP
    refine ⟨e, he, fun T x hx => ?_⟩
    have h0 := hk _ (pushPt w x) (kerGen o.A A' φ h o.P T x hx)
    apply (GlobalTheory.ObjPull.pushEquiv h T).injective
    rw [map_pow, map_one]
    exact h0
  · intro c
    exact LBIso.chartPull (pul _ φ₂ _ (ro c)) (pul _ φ₂ _ (ro' _)) (o.rosati c)
  · intro R' _ β x hx v hv
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
      (Category.assoc _ _ _).symm
    have key := fun (c : D.O) (r : R') (v : epsPtR x ⟶ A') =>
      tanScal_iff f o.A A' φ o.act act' h hact R' x c r v (e v) (he v)
    obtain ⟨w₀, hw₀, hv₀⟩ := o.lie R' β (x ≫ f) (by rw [Category.assoc]; exact hx) (e v) ((key _ _ v).1 hv)
    refine ⟨fun i => e.symm (w₀ i), fun i c => (key _ _ _).2 (by rw [MulEquiv.apply_symm_apply]; exact hw₀ i c), ?_⟩
    apply e.injective
    rw [hv₀, map_list_prod, List.map_ofFn]
    simp [Function.comp_def]
  · intro k _ _ x β hx i
    exact (GlobalTheory.LiePull.lieMult_pull _ S S' o.A A' f φ (o.act.toF D) (act'.toF D) h (fun c => hact _) k x _ _).2
      (o.lieRank k (x ≫ f) β (by rw [Category.assoc]; exact hx) i)
  · intro c y
    rw [o.eta_lin]
    apply (GlobalTheory.ObjPull.pushEquiv h _).injective
    apply Over.OverMorphism.ext
    show (GlobalTheory.ObjPull.secPull h (o.eta y ≫ o.act.act c)).left ≫ φ =
      (GlobalTheory.ObjPull.secPull h (o.eta y) ≫ act'.act c).left ≫ φ
    rw [GlobalTheory.ObjPull.secPull_left, Over.comp_left, Over.comp_left, Category.assoc, hact,
      reassoc_of% (GlobalTheory.ObjPull.secPull_left h (o.eta y))]
  · intro k _ _ x β hx
    obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc]; exact hx)
    refine ⟨tateMoveO (GlobalTheory.ObjPull.pushEquiv h (Over.mk x)) (fun c g => ?_) (fun n g g' z hz => ?_) I, fun y => ?_⟩
    · apply Over.OverMorphism.ext
      show (g.left ≫ _) ≫ φ = (g.left ≫ φ) ≫ _
      rw [Category.assoc, hact, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.A A' f φ _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) h hL
        (Over.mk x) n g g' _ _ _ rfl rfl).2 hz
    · rw [tateMoveO_ev]
      exact (MulEquiv.eq_symm_apply _).2 ((GlobalTheory.ObjPull.pushEquiv_secPull h _ _).trans (hI y))

end GlobalTheory.UPel.HT.Pull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.LeviUnitary

open Matrix

section Ring

variable {R : Type} [CommRing R] {n m : ℕ} {ι : Matrix (Fin n) (Fin m) R} {π : Matrix (Fin m) (Fin n) R}

theorem ext_mul (hπ : π * ι = 1) (g h : Matrix (Fin m) (Fin m) R) :
    (1 + ι * (g - 1) * π) * (1 + ι * (h - 1) * π) = 1 + ι * (g * h - 1) * π := by
  have h1 : ι * (g - 1) * π * (ι * (h - 1) * π) = ι * ((g - 1) * (h - 1)) * π := by
    calc _ = ι * (g - 1) * (π * ι) * (h - 1) * π := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hπ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h2 : g * h - 1 = (h - 1) + (g - 1) + (g - 1) * (h - 1) := by noncomm_ring
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, h1, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, add_assoc]

theorem ext_unitary (c : R →+* R) {J : Matrix (Fin n) (Fin n) R} {J₁ : Matrix (Fin m) (Fin m) R} (hπ : π * ι = 1)
    (h1 : J * ι.map c = πᵀ * J₁) (h2 : ιᵀ * J = J₁ * π.map c) {g : Matrix (Fin m) (Fin m) R} (hg : gᵀ * J₁ * g.map c = J₁) :
    (1 + ι * (g - 1) * π)ᵀ * J * (1 + ι * (g - 1) * π).map c = J := by
  have hm : (1 + ι * (g - 1) * π).map c = 1 + ι.map c * (g.map c - 1) * π.map c := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub c),
      Matrix.map_one _ (map_zero c) (map_one c), Matrix.map_one _ (map_zero c) (map_one c)]
  have h3 : π.map c * ι.map c = 1 := by rw [← Matrix.map_mul, hπ, Matrix.map_one _ (map_zero c) (map_one c)]
  have ht : (1 + ι * (g - 1) * π)ᵀ = 1 + πᵀ * (gᵀ - 1) * ιᵀ := by
    simp only [transpose_add, transpose_mul, transpose_sub, transpose_one, Matrix.mul_assoc]
  have e1 : πᵀ * (gᵀ - 1) * ιᵀ * J = πᵀ * ((gᵀ - 1) * J₁) * π.map c := by
    rw [Matrix.mul_assoc _ ιᵀ, h2]; simp only [Matrix.mul_assoc]
  have e2 : J * (ι.map c * (g.map c - 1) * π.map c) = πᵀ * (J₁ * (g.map c - 1)) * π.map c := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1]; simp only [Matrix.mul_assoc]
  have e3 : πᵀ * ((gᵀ - 1) * J₁) * π.map c * (ι.map c * (g.map c - 1) * π.map c) =
      πᵀ * ((gᵀ - 1) * J₁ * (g.map c - 1)) * π.map c := by
    calc _ = πᵀ * ((gᵀ - 1) * J₁) * (π.map c * ι.map c) * (g.map c - 1) * π.map c := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h3, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e4 : (gᵀ - 1) * J₁ + (J₁ * (g.map c - 1) + (gᵀ - 1) * J₁ * (g.map c - 1)) = 0 := by
    have : (gᵀ - 1) * J₁ + (J₁ * (g.map c - 1) + (gᵀ - 1) * J₁ * (g.map c - 1)) = gᵀ * J₁ * g.map c - J₁ := by noncomm_ring
    rw [this, hg, sub_self]
  rw [hm, ht, Matrix.add_mul, Matrix.one_mul, e1, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, e2, e3, add_assoc,
    ← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add, e4]
  simp

end Ring

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  intro h0
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply]
  have h2 := congrArg Matrix.det h1
  rw [det_mul, det_mul, h0, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, det_neg, det_one] at h2
  simp at h2
  exact absurd h2.symm (by simp)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_mul {k l p : ℕ} (A : Matrix (Fin k) (Fin l) E) (A' : Matrix (Fin l) (Fin p) E) :
    incM F (A * A') = incM F A * incM F A' := Matrix.map_mul

theorem incM_conj {k l : ℕ} (A : Matrix (Fin k) (Fin l) E) :
    (incM F A).map (cA σ).toRingHom = incM F (A.map σ) := by
  ext i j
  exact GlobalTheory.LeviTorus.cA_incl σ (A i j)

theorem incM_mulVec {k l : ℕ} (A : Matrix (Fin k) (Fin l) E) (x : Fin l → E) :
    incM F A *ᵥ incV F x = incV F (A *ᵥ x) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [incM, incV, mulVec, dotProduct, map_sum, map_mul]

theorem exists_proj {B : Base F E} (hB : B.IsGood σ) {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {r s r₁ s₁ : ℕ}
    (hW : W.IsSkew σ B r s) (hW₁ : W₁.IsSkew σ B r₁ s₁) {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁) :
    ∃ π : Matrix (Fin d₁) (Fin d) E, π * H'.ι = 1 ∧ W.J * H'.ι.map σ = πᵀ * W₁.J ∧ H'.ιᵀ * W.J = W₁.J * π.map σ ∧
      π *ᵥ H'.x = 0 ∧ π *ᵥ H'.y = 0 := by
  have hσ := GlobalTheory.LeviTorus.sigma_invol hB.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdet : IsUnit W₁.J.det := by
    have h := det_ne_zero_of_hasSig (hW₁.sig w)
    rw [det_smul] at h
    have h' := right_ne_zero_of_mul h
    rw [isUnit_iff_ne_zero]
    intro h0
    apply h'
    have := RingHom.map_det (B.emb w).1 W₁.J
    rw [h0, map_zero] at this
    exact this.symm
  have mm : ∀ {k l : ℕ} (A : Matrix (Fin k) (Fin l) E), (A.map σ).map σ = A := fun A => by
    ext i j; exact hσ _
  have mul : ∀ {k l p : ℕ} (A : Matrix (Fin k) (Fin l) E) (A' : Matrix (Fin l) (Fin p) E),
      (A * A').map σ = A.map σ * A'.map σ := fun A A' => Matrix.map_mul (f := σ.toRingHom)
  have sk : W.J.map σ = -W.Jᵀ := by ext i j; exact hW.skew j i
  have sk₁ : W₁.J.map σ = -W₁.Jᵀ := by ext i j; exact hW₁.skew j i
  set P : Matrix (Fin d₁) (Fin d) E := W₁.J⁻¹ * (H'.ιᵀ * W.J) with hP
  have h2 : H'.ιᵀ * W.J = W₁.J * P := by rw [hP, Matrix.mul_nonsing_inv_cancel_left _ _ hdet]
  have hz : ∀ z : Fin d → E, (∀ u, form σ W.J (H'.ι *ᵥ u) z = 0) → P.map σ *ᵥ z = 0 := by
    intro z hz
    have e1 : (H'.ιᵀ * W.J) *ᵥ (fun i => σ (z i)) = 0 := by
      funext j
      have := hz (Pi.single j 1)
      rw [form, mulVec_single_one] at this
      rw [← mulVec_mulVec]
      exact this
    have e2 : P *ᵥ (fun i => σ (z i)) = 0 := by rw [hP, ← mulVec_mulVec, e1, mulVec_zero]
    funext j
    have := congrArg σ (congrFun e2 j)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [mulVec, dotProduct, map_sum, map_mul, hσ] using this
  refine ⟨P.map σ, ?_, ?_, by rw [mm, h2], hz _ fun u => (hA.orth u).1, hz _ fun u => (hA.orth u).2⟩
  · have : P * H'.ι.map σ = 1 := by rw [hP, Matrix.mul_assoc, hA.gram, Matrix.nonsing_inv_mul _ hdet]
    rw [← mm H'.ι, ← mul, this]
    exact Matrix.map_one _ (map_zero σ) (map_one σ)
  · have := congrArg (fun A => (Matrix.map A σ)ᵀ) h2
    simp only [mul, sk, sk₁, transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg,
      neg_inj] at this
    exact this

theorem exists_isLevi {B : Base F E} (hB : B.IsGood σ) {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {r s r₁ s₁ : ℕ}
    (hW : W.IsSkew σ B r s) (hW₁ : W₁.IsSkew σ B r₁ s₁) {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁)
    (h₁ : UA σ W₁.J) : ∃ m : UA σ W.J, IsLevi H' 1 h₁ m := by
  obtain ⟨π, p1, p2, p3, p4, p5⟩ := exists_proj hB hW hW₁ hA
  have q1 : incM F π * incM F H'.ι = 1 := by
    rw [← incM_mul, p1]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have q2 : incM F W.J * (incM F H'.ι).map (cA σ).toRingHom = (incM F π)ᵀ * incM F W₁.J := by
    rw [incM_conj, ← incM_mul, p2, incM_mul]; rfl
  have q3 : (incM F H'.ι)ᵀ * incM F W.J = incM F W₁.J * (incM F π).map (cA σ).toRingHom := by
    rw [incM_conj, ← incM_mul, ← p3, incM_mul]; rfl
  have hfix : ∀ z, π *ᵥ z = 0 → (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) *ᵥ incV F z = incV F z := by
    intro z hz
    have h0 : incV F (0 : Fin d₁ → E) = 0 := by funext i; exact map_zero _
    rw [add_mulVec, one_mulVec, ← mulVec_mulVec, incM_mulVec, hz, h0, mulVec_zero, add_zero]
  refine ⟨⟨⟨1 + incM F H'.ι * (mat h₁ - 1) * incM F π, 1 + incM F H'.ι * ((h₁.1⁻¹).1 - 1) * incM F π, ?_, ?_⟩, ?_⟩,
    ?_, ?_, ?_⟩
  · rw [ext_mul q1, mat, Units.mul_inv]; simp
  · rw [ext_mul q1, mat, Units.inv_mul]; simp
  · exact ext_unitary (cA σ).toRingHom q1 q2 q3 h₁.2
  · rw [Units.val_one, one_smul]; exact hfix _ p4
  · rw [inv_one, Units.val_one, map_one, one_smul]; exact hfix _ p5
  · show (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) * incM F H'.ι = _
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, q1, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]

end GlobalTheory.LeviUnitary

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleApproxScaled
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace GlobalTheory.EvAdm

theorem exists_rational_rep_scaledInt : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F, ∃ ξ : κ → F,
      r - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a := by
  intro F _ _ κ _ a _ r
  have hd : DenseRange (Pi.map fun (_ : κ) => algebraMap F (FiniteAdeleRing (𝓞 F) F)) :=
    DenseRange.piMap fun _ => PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange (R := 𝓞 F) (K := F)
  have hop : IsOpen {y : κ → FiniteAdeleRing (𝓞 F) F | r - y ∈ GlobalTheory.EvAdm.scaledInt F κ a} :=
    (GlobalTheory.EvAdm.isOpen_scaledInt a).preimage (continuous_const.sub continuous_id)
  have hr : r ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | r - y ∈ GlobalTheory.EvAdm.scaledInt F κ a} := by
    show r - r ∈ GlobalTheory.EvAdm.scaledInt F κ a
    rw [sub_self]
    exact zero_mem _
  obtain ⟨ξ, hξ⟩ := hd.exists_mem_open hop ⟨r, hr⟩
  exact ⟨ξ, hξ⟩

end GlobalTheory.EvAdm
end

