module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.PsiWeightZeroLinearCombination
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOnOfPowOne
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TripleOut

open GlobalTheory.CechPic GlobalTheory.TripleExt

theorem exists_secOn_of_pow_one {X : Scheme.{0}} (L : LB X) (V : X.Opens)
    {σ : ∀ j, Γ(X, V ⊓ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).U j)}
    (hσ : σ ∈ secOn (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)) V) :
    ∃ θ ∈ secOn L V, ∀ j, X.basicOpen (σ j) ≤ X.basicOpen (θ (j 0)) := by
  have h : ∀ i, L.U i ≤ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 1)).U fun _ => i :=
    fun i x hx => Set.mem_iInter.2 fun _ => hx
  have rr : ∀ {A B C : X.Opens} (e : B ≤ A) (e' : C ≤ B) (s : Γ(X, A)),
      resG X e' (resG X e s) = resG X (e'.trans e) s := fun e e' s => by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl
  refine ⟨fun i => resG X (inf_le_inf_left V (h i)) (σ fun _ => i), fun i j => ?_, fun j => ?_⟩
  · have e := congrArg (resG X (inf_le_inf (inf_le_inf_left V (h i)) (h j))) (hσ (fun _ => i) (fun _ => j))
    rw [map_mul, rr, rr, rr] at e
    rw [rr, rr, e]
    congr 1
    simp only [LB.LinComb, Fin.prod_univ_one, zpow_one]
    exact rr _ _ _
  · obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => congrArg j (Subsingleton.elim _ _)⟩
    intro x hx
    rw [Scheme.basicOpen_res]
    exact ⟨inf_le_inf_left V (LB.wchart_le L _ _ 0) (X.basicOpen_le _ hx), hx⟩

theorem mem_basicOpen_of_valF {K : Type} [Field K] {X : Scheme.{0}} (g : Sp K ⟶ X) {U : X.Opens} (f : Γ(X, U))
    (h : valF g U f ≠ 0) (w : Sp K) : g w ∈ X.basicOpen f :=
  (GlobalTheory.Points.le_preimage_basicOpen_iff g (by_contra fun hn => h (dif_neg hn)) f).2 (isUnit_iff_ne_zero.2 h)
    (x := w) trivial

theorem exists_geomPoint {X : Scheme.{0}} (y : X) :
    ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : Sp K ⟶ X), ∀ w, x w = y :=
  ⟨AlgebraicClosure (X.residueField y), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField y) _)) ≫ X.fromSpecResidueField y,
    fun w => by rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]⟩

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J}

theorem hasTheta (Z : ZHOut ρ M U₀ EE) (h : M.HasDiv S.th) : GlobalTheory.Models.HasTheta Z.G Z.L.L := by
  intro z
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  obtain ⟨x₀, hx₀⟩ := h z
  let W : M.Z.Opens := ⟨_, M.isOpen_setOf_div S.th x₀⟩
  obtain ⟨σ, hσ, -, hne⟩ := Z.theta W x₀ fun _ hz => hz
  obtain ⟨θ, hθ, hle⟩ := exists_secOn_of_pow_one Z.L.L _ hσ
  refine ⟨W, hx₀, θ, hθ, fun y hy => ?_⟩
  obtain ⟨K, _, _, x, hx⟩ := exists_geomPoint y
  obtain ⟨g, j, hg, hv⟩ := hne K x (by rintro _ ⟨w, rfl⟩; rw [hx]; exact hy)
  refine ⟨g (IsLocalRing.closedPoint K), j 0, ?_, hle j ?_⟩
  · exact (Scheme.Hom.comp_apply g Z.G.hom _).symm.trans (hg ▸ hx _)
  · exact mem_basicOpen_of_valF g (σ j) hv _

theorem splitFib (Z : ZHOut ρ M U₀ EE) : GlobalTheory.Models.SplitFib Z.G := by
  intro z
  refine ⟨M.Z.residueField z, inferInstance, Algebra.id _, inferInstance, inferInstance, ?_⟩
  have e : Spec.map (CommRingCat.ofHom (algebraMap (M.Z.residueField z) (M.Z.residueField z))) ≫
      M.Z.fromSpecResidueField z = M.Z.fromSpecResidueField z := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have h : ∀ f : Sp (M.Z.residueField z) ⟶ M.Z, f = M.Z.fromSpecResidueField z →
      ∃ E : SplitExt (Sp (M.Z.residueField z)), E.IsGt ((Over.pullback f).obj Z.G) := by
    rintro _ rfl
    exact Z.split z
  exact h _ e

section Cube

variable {B U X : Scheme.{0}} {A : Over B} {A' : Over U} {G : Over X} [GrpObj A] [IsCommMonObj A] [GrpObj A']
  [IsCommMonObj A'] [GrpObj G] [IsCommMonObj G]

omit [IsCommMonObj A] [IsCommMonObj A'] in
theorem pushPt_comp {u : U ⟶ B} {p : A'.left ⟶ A.left} (h : IsGrpPullback A' A u p) {a' : A' ⟶ A'} {a : A ⟶ A}
    (ha : a'.left ≫ p = p ≫ a.left) {T : Over U} (x : T ⟶ A') : pushPt h.1.w (x ≫ a') = pushPt h.1.w x ≫ a :=
  Over.OverMorphism.ext (by
    show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
    rw [Category.assoc, ha, Category.assoc])

theorem adj_pull {u : U ⟶ B} {p : A'.left ⟶ A.left} (h : IsGrpPullback A' A u p) {a' b' : A' ⟶ A'} {a b : A ⟶ A}
    (ha : a'.left ≫ p = p ≫ a.left) (hb : b'.left ≫ p = p ≫ b.left) (c : Pic A.left)
    (H : cubeCls ![fst A A ≫ a, snd A A] c = cubeCls ![fst A A, snd A A ≫ b] c) {T : Over U} (y₁ y₂ : T ⟶ A') :
    cubeCls ![y₁ ≫ a', y₂] (pull p c) = cubeCls ![y₁, y₂ ≫ b'] (pull p c) := by
  let v := lift (pushPt h.1.w y₁) (pushPt h.1.w y₂)
  refine (pull_cubeCls_push h _ _ v (fun i => ?_) c).symm.trans
    ((congrArg (pull v.left) H).trans (pull_cubeCls_push h _ _ v (fun i => ?_) c))
  · fin_cases i
    · exact (pushPt_comp h ha _).trans (by simp [v])
    · simp [v]
  · fin_cases i
    · simp [v]
    · exact (pushPt_comp h hb _).trans (by simp [v])

theorem pull_graph {u : U ⟶ B} {p : A'.left ⟶ A.left} (h : IsGrpPullback A' A u p) {a' : A' ⟶ A'} {a : A ⟶ A}
    (ha : a'.left ≫ p = p ≫ a.left) (c : Pic A.left) :
    pull p (cubeCls ![𝟙 A, a] c) = cubeCls ![𝟙 A', a'] (pull p c) := by
  have h₁ := pull_cubeCls_push h ![𝟙 A', a'] ![𝟙 A, a] (pushPt h.1.w (𝟙 A'))
    (fun i => by
      fin_cases i
      · simp
      · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pushPt_comp h ha _)) c
  have e : (pushPt h.1.w (𝟙 A')).left = p := Category.id_comp _
  rwa [e] at h₁

variable [IsIntegral X] [IsLocallyNoetherian X] (hX : Geo.Tor.IsNormalScheme X) [Nonempty U] {j : U ⟶ X}
  [IsOpenImmersion j] (semi : IsSemiAbelian G) {φ : A'.left ⟶ G.left} (h : IsGrpPullback A' G j φ)
include hX semi h

theorem adj_extend {a' b' : A' ⟶ A'} {a b : G ⟶ G} [IsMonHom a] [IsMonHom b]
    (ha : a'.left ≫ φ = φ ≫ a.left) (hb : b'.left ≫ φ = φ ≫ b.left) (c : Pic G.left)
    (H : ∀ {T : Over U} (y₁ y₂ : T ⟶ A'), cubeCls ![y₁ ≫ a', y₂] (pull φ c) = cubeCls ![y₁, y₂ ≫ b'] (pull φ c)) :
    cubeCls ![fst G G ≫ a, snd G G] c = cubeCls ![fst G G, snd G G ≫ b] c := by
  have := semi.smooth
  have := semi.geomConnected
  have hsm : Smooth (G ⊗ G).hom := by
    show Smooth (pullback.fst G.hom G.hom ≫ G.hom)
    infer_instance
  have hgc : GeometricallyConnected (G ⊗ G).hom := by
    show GeometricallyConnected (pullback.fst G.hom G.hom ≫ G.hom)
    exact GeometricallyConnected.comp _ _
  let T' : Over U := Over.mk (pullback.snd (G ⊗ G).hom j)
  let u : Over.mk (T'.hom ≫ j) ⟶ G ⊗ G := Over.homMk (pullback.fst (G ⊗ G).hom j) pullback.condition
  have hy : ∀ y : G ⊗ G ⟶ G, ∃ y' : T' ⟶ A', pushPt h.1.w y' = u ≫ y := fun y =>
    ⟨Over.homMk (h.1.lift (u ≫ y).left T'.hom (Over.w (u ≫ y))) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  obtain ⟨y₁, hy₁⟩ := hy (fst G G)
  obtain ⟨y₂, hy₂⟩ := hy (snd G G)
  let e : 𝟙_ (Over X) ⟶ G ⊗ G := lift η[G] η[G]
  refine pic_ext X hX j (G ⊗ G).hom e.left u.left T'.hom hsm
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w e)
    (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
  · refine (pull_cubeCls_push h _ _ u (fun i => ?_) _).trans
      ((H y₁ y₂).trans (pull_cubeCls_push h _ _ u (fun i => ?_) _).symm)
    · fin_cases i
      · simp [pushPt_comp h ha, hy₁]
      · simp [hy₂]
    · fin_cases i
      · simp [hy₁]
      · simp [pushPt_comp h hb, hy₂]
  · refine (pull_cubeCls_pre e _ _).trans (Eq.trans ?_ (pull_cubeCls_pre e _ _).symm)
    congr 1
    funext i
    fin_cases i <;> simp [e]

theorem prim_extend {a' : A' ⟶ A'} {a : G ⟶ G} [IsMonHom a] (ha : a'.left ≫ φ = φ ≫ a.left) (c : Pic G.left)
    (hc : pull (eSec G) c = 0) (H : pull φ c = cubeCls ![𝟙 A', a'] (pull φ c)) : c = cubeCls ![𝟙 G, a] c := by
  have := semi.smooth
  have := semi.geomConnected
  refine pic_ext X hX j G.hom (eSec G) φ A'.hom inferInstance
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w η[G]) h.1 _ _
    (H.trans (pull_graph h ha c).symm) ?_
  refine hc.trans (Eq.trans ?_ (pull_cubeCls_pre η[G] _ _).symm)
  refine (cubeCls_one (n := 2) _ hc).symm.trans ?_
  congr 1
  funext i
  fin_cases i <;> simp

end Cube

theorem exists_triple : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Z : ZHOut ρ M U₀ EE) (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (act : OAct (NumberField.RingOfIntegers E) ρ.P.A), S.Over₀ M U₀ → (∀ a, LBIso (cubeLB ρ.P.A ![fst _ _ ≫ act.act a, snd _ _] ρ.P.L) (cubeLB ρ.P.A ![fst _ _, snd _ _ ≫ act.act (H.bar a)] ρ.P.L)) → LBIso ρ.P.L (cubeLB ρ.P.A ![𝟙 _, act.act H.w0] ρ.P.L) → ∃ (act' : OAct (NumberField.RingOfIntegers E) Z.G) (h₂ : _) (h₃ : _), (∀ a, ((Over.pullback Z.u₀).map (act.act a)).left ≫ Z.φ = Z.φ ≫ (act'.act a).left) ∧ (GlobalTheory.Models.AbOpen Z.G → GlobalTheory.Models.Good (SAB.mk (H := H) Z.G Z.semi act' Z.L Z.cub Z.sym h₂ h₃)) := by
  intro hD o Ω _ _ _ _ S ρ M U₀ EE Z E _ _ _ H act hO hadj hprim
  have := (inferInstance : ArithBase o Ω).ft
  have := (inferInstance : ArithBase o Ω).char
  have := M.locallyOfFiniteType_int
  have hfl := M.flat_int (M.s ≫ spMap (algebraMap ℤ o))
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian (M.s ≫ spMap (algebraMap ℤ o))
  have := ρ.P.isAb.comm
  have : Nonempty U₀.toScheme := hO.ne.to_subtype
  have hd : Dense (U₀ : Set M.Z) := U₀.isOpen.dense hO.ne
  obtain ⟨_, _⟩ := ExtUnique.dense_open U₀ hd
  obtain ⟨_, _⟩ := ExtUnique.flat_and_isSeparated_of_isSemiAbelian Z.G Z.semi
  let act₀ := Geo.Tor.OAct.pullback Z.u₀ ρ.P.A act
  obtain ⟨act', hact, -⟩ := ExtUnique.existsUnique_oAct_of_isGrpPullback Z.cart act₀ fun x => by
    obtain ⟨e, he, he'⟩ := grpPullback_iso Z.cart (isGrpPullback_pullback Z.G U₀.ι)
    have := act₀.hom x
    obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.existsUnique_hom_extension_semiAbelian_normal hD M.Z U₀ U₀.ι ⟨hO.normal, _, inferInstance, hfl⟩ inferInstance inferInstance
      inferInstance inferInstance Z.G Z.G Z.semi Z.semi (e.inv ≫ act₀.act x ≫ e.hom) inferInstance
    refine ⟨F, ?_⟩
    rw [← he', Category.assoc, ← ExtUnique.pullback_map_left_fst, hF, ← Category.assoc, ← Category.assoc,
      ← Over.comp_left, ← Over.comp_left, Iso.hom_inv_id_assoc]
  have hp := isGrpPullback_pullback ρ.P.A Z.u₀
  have ha : ∀ x, (act₀.act x).left ≫ pullback.fst ρ.P.A.hom Z.u₀ = pullback.fst ρ.P.A.hom Z.u₀ ≫ (act.act x).left :=
    fun x => ExtUnique.pullback_map_left_fst _ _
  have hc : pull Z.φ (cls Z.L.L Z.L.isLB) = pull (pullback.fst ρ.P.A.hom Z.u₀) (cls ρ.P.L ρ.P.isLB) :=
    (cls_eq_iff (pull_isLB Z.L.isLB _) (pull_isLB ρ.P.isLB _)).2 ⟨Z.w, Z.w_gen⟩
  refine ⟨act', fun b => ?_, ?_, hact, fun h => ⟨h, splitFib Z, hasTheta Z hO.div⟩⟩
  · refine (cls_eq_iff (isLB_cube _ Z.L.isLB) (isLB_cube _ Z.L.isLB)).1 ?_
    rw [cls_cube _ Z.L.isLB, cls_cube _ Z.L.isLB]
    have := act'.hom b
    have := act'.hom (H.bar b)
    have h₀ := (cls_eq_iff (isLB_cube _ ρ.P.isLB) (isLB_cube _ ρ.P.isLB)).2 (hadj b)
    rw [cls_cube _ ρ.P.isLB, cls_cube _ ρ.P.isLB] at h₀
    refine adj_extend hO.normal Z.semi Z.cart (hact b) (hact (H.bar b)) _ fun y₁ y₂ => ?_
    rw [hc]
    exact adj_pull hp (ha b) (ha (H.bar b)) _ h₀ y₁ y₂
  · refine (cls_eq_iff Z.L.isLB (isLB_cube _ Z.L.isLB)).1 ?_
    rw [cls_cube _ Z.L.isLB]
    have := act'.hom H.w0
    have h₀ := (cls_eq_iff ρ.P.isLB (isLB_cube _ ρ.P.isLB)).2 hprim
    rw [cls_cube _ ρ.P.isLB] at h₀
    refine prim_extend hO.normal Z.semi Z.cart (hact H.w0) _
      ((cls_eq_zero_iff (pull_isLB Z.L.isLB _)).2 ⟨Z.L.rig, Z.L.rigGen⟩) ?_
    rw [hc]
    exact (congrArg (pull _) h₀).trans (pull_graph hp (ha H.w0) _)

end GlobalTheory.TripleOut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaPointComplexDegenerationSmall
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem isThetaPt_classical (hL : Laws) (hL2 : Laws2) (hT : ThetaUnifAV) (P : PolAV (Sp ℂ))
    (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin P.g → ℂ) → ℂ) (N : ℕ)
    {I : Type} (x : I → (baseOver (Sp ℂ) ⟶ P.A)) (l : I → u.Λ) (hN : Odd N) (hAH : u.IsAH Hm χ)
    (hθ : u.IsThetaFn Hm χ 1 θ) (h0 : θ ≠ 0) (hx : ∀ i, x i = u.ex (((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ))) :
    IsThetaPt P N x fun i => fnOf (χ (l i) * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm (l i) (l i)) *
      θ ((N : ℂ)⁻¹ • (l i : Fin P.g → ℂ))) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.pos.ne'
  refine ⟨hN, isUnit_natCast_sp hN0, fun q => ⟨⊤, trivial, ?_⟩⟩
  let T : Over (Sp ℂ) := overRes (T := baseOver (Sp ℂ)) ⊤
  haveI : IsIso T.hom := by
    show IsIso ((⊤ : (Sp ℂ).Opens).ι ≫ 𝟙 _)
    rw [Category.comp_id]
    exact inferInstanceAs (IsIso (Sp ℂ).topIso.hom)
  let p : 𝟙_ (Over (Sp ℂ)) ⟶ T := Over.homMk (inv T.hom) (by simp)
  have hp : p ≫ overResι (T := baseOver (Sp ℂ)) ⊤ = 𝟙 _ := by
    ext1
    show inv T.hom ≫ (⊤ : (Sp ℂ).Opens).ι = 𝟙 _
    rw [IsIso.inv_comp_eq]
    rfl
  have htor : ∀ i, x i ^ (N ^ 2) = 1 := fun i => by
    rw [hx]
    refine (ThetaClassical.ex_nsmul u _ _).symm.trans ((u.ker _).2 ?_)
    rw [← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_pow, smul_inv_smul₀ (pow_ne_zero _ hN0)]
    exact (l i).2
  have key := ThetaClassical.isThetaPtOver hL hL2 hT P u Hm χ θ N T p (fun i => overResι ⊤ ≫ x i) l
    hN hAH hθ h0 (fun i => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x i) hp).trans
      ((Category.id_comp _).trans (hx i))))
    (fun i => ThetaClassical.exists_symLift hL P (N ^ 2) _ (by push_cast; rfl) hN.pow (x i) (htor i))
  convert key using 2 with i
  exact ThetaClassical.constFn_top _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_tateIso (D : Datum H) {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La)
    (Q : PolAV (Sp ℂ)) (act : 𝓞 E → (Q.A ⟶ Q.A)) (hact : ∀ c, IsMonHom (act c)) {g : ℕ} (u : HolUnif Q.A Q.L g)
    (P : La →+ (Fin g → ℂ)) (hinj : Function.Injective P) (hker : ∀ z, z ∈ u.Λ ↔ ∃ a, z = P a)
    (hlin : ∀ (c : 𝓞 E) (s : ℂ) a, u.ex (s • P (c • a)) = u.ex (s • P a) ≫ act c)
    (hW : ∀ (k : ℕ) a b (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • P a)) (u.ex ((k : ℂ)⁻¹ • P b)) (unitOn c))
    (ζ : ℕ → ℂˣ) (hp : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hc : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n)
    (f : ℕ → D.La → La) (hf : IsTower D EF ζ f) :
    ∃ I : TateIso D ℂ (baseOver (Sp ℂ) ⟶ Q.A) (fun a x => x ≫ act a) (fun n x x' c => WeilIs Q.A Q.L n x x' (unitOn c)),
      I.ζ = ζ ∧ ∀ (n : ℕ) a, I.ev n a = u.ex ((n : ℂ)⁻¹ • P (f n a)) := by
  let e : (Fin g → ℂ) → (baseOver (Sp ℂ) ⟶ Q.A) := u.ex
  have eadd : ∀ z w, e (z + w) = e z * e w := u.ex_add
  have eker : ∀ z, e z = 1 ↔ ∃ a, z = P a := fun z => (u.ker z).trans (hker z)
  have epow : ∀ z (n : ℕ), e z ^ n = e (n • z) := fun z n => (ThetaClassical.ex_nsmul u z n).symm
  have e0 : e 0 = 1 := (eker 0).2 ⟨0, (map_zero P).symm⟩
  have hn : ∀ n : ℕ, 0 < n → (n : ℂ) ≠ 0 := fun n h => Nat.cast_ne_zero.2 h.ne'
  have sm : ∀ n : ℕ, 0 < n → ∀ a, (n : ℂ)⁻¹ • P (n • a) = P a := fun n h a => by
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (hn n h)]
  have sm' : ∀ n : ℕ, 0 < n → ∀ z : Fin g → ℂ, n • (n : ℂ)⁻¹ • z = z := fun n h z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (hn n h)]
  have md : ∀ n : ℕ, 0 < n → ∀ a b, e ((n : ℂ)⁻¹ • P (a + n • b)) = e ((n : ℂ)⁻¹ • P a) := fun n h a b => by
    rw [map_add (f := _), smul_add, eadd, sm n h, (eker _).2 ⟨b, rfl⟩, _root_.mul_one]
  refine ⟨{ ζ := ζ, ζ_prim := hp, ζ_pow := hc, ev := fun n a => e ((n : ℂ)⁻¹ • P (f n a)), add := fun n a b => ?_,
            lin := fun n c a => ?_, ker := fun n h a => ?_, onto := fun n h x => ⟨fun hx => ?_, ?_⟩,
            tower := fun n m h h' a => ?_, isom := fun n h a b => ?_ }, rfl, fun _ _ => rfl⟩
  · rcases n.eq_zero_or_pos with rfl | h
    · simp only [Nat.cast_zero, inv_zero, zero_smul, e0, _root_.mul_one]
    · obtain ⟨c, hc⟩ := (hf n h).1 a b
      rw [hc, md n h, map_add (f := _), smul_add, eadd]
  · rcases n.eq_zero_or_pos with rfl | h
    · haveI := hact c
      simp only [Nat.cast_zero, inv_zero, zero_smul, e0, MonObj.one_comp]
    · obtain ⟨b, hb⟩ := (hf n h).2.1 c a
      rw [hb, md n h]
      exact hlin c _ _
  · rw [← (hf n h).2.2.1 a, eker]
    refine exists_congr fun b => ⟨fun hb => hinj ?_, fun hb => by rw [hb, sm n h]⟩
    rw [map_nsmul, ← hb, sm' n h]
  · obtain ⟨z, rfl⟩ : ∃ z, e z = x := u.ex_onto x
    rw [epow, eker] at hx
    obtain ⟨b, hb⟩ := hx
    obtain ⟨a, c, rfl⟩ := (hf n h).2.2.2.1 b
    refine ⟨a, ?_⟩
    rw [← md n h _ c, ← hb, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (hn n h)]
  · rintro ⟨a, rfl⟩
    rw [epow, sm' n h]
    exact (eker _).2 ⟨_, rfl⟩
  · obtain ⟨b, hb⟩ := (hf n h).2.2.2.2.1 m h' a
    rw [epow, hb, Nat.cast_mul, mul_inv, mul_comm, mul_smul, sm' m h', md n h]
  · exact hW n _ _ _ h ((hf n h).2.2.2.2.2 a b)

theorem exists_log (T : ℝ) (u : ℂˣ) (hu : ‖(u : ℂ)‖ < Real.exp (-(2 * Real.pi * T))) :
    ∃ w : ℂ, T < w.im ∧ (u : ℂ) = eTwoPi w := by
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have e : (u : ℂ) = eTwoPi (Complex.log u / (2 * Real.pi * Complex.I)) := by
    rw [eTwoPi, mul_div_cancel₀ _ h2, Complex.exp_log u.ne_zero]
  refine ⟨_, ?_, e⟩
  generalize Complex.log u / (2 * Real.pi * Complex.I) = w at e
  rw [e, eTwoPi, Complex.norm_exp, Real.exp_lt_exp] at hu
  simp at hu
  have := Real.pi_pos
  nlinarith

theorem of_steps (hL : Laws) (hL2 : Laws2) (hT : ThetaUnifAV) (hdict : DictSt) (htow : TowerSt) (hty : TypeSt)
    (hobj : ObjSt) (hth : ThetaSt) (htx : TxSt) : AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (A : ArcF D R ℂ), A.ρ = H.rt0 → ∀ (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ x, Summable fun χ => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖) ∧ ∃ o : Full D ℂ, o.ρ = H.rt0 ∧ o.I.ζ (m ^ 2) = A.I.ζ (m ^ 2) ∧ o.Theta m fun x => (A.N.twist β u).tx m (A.N.twQ β u hm (A.q _ x)) := by
  intro E _ _ _ H D R _ _ _ A hρ k β hβ m hm hodd
  letI := H.starRing
  obtain ⟨B, d, hact, hbe, hprim, hth0, hsig⟩ := hdict E H D R A k β hβ
  obtain ⟨f, hf, hrep⟩ := htow E H D R A B d hact
  obtain ⟨g, ty, h, htyp, hh⟩ := hty E H D B (hρ ▸ hsig)
  obtain ⟨-, hbij, hadj, T₁, hT₁⟩ := B.periods_polarised
  obtain ⟨T₂, hT₂⟩ := B.exists_convergence
  have hmem : d.th ∈ B.Theta 1 0 := d.ab.2.2.2.2.2.2.2.1
  obtain ⟨-, hsum, -, hdiff, -⟩ := hT₂ 1 0 d.th hmem
  refine ⟨Real.exp (-(2 * Real.pi * max T₁ T₂)), Real.exp_pos _, fun u hu => ?_⟩
  obtain ⟨w, hw, huw⟩ := exists_log _ u hu
  have hw₁ : T₁ < w.im := (le_max_left _ _).trans_lt hw
  have hw₂ : T₂ < w.im := (le_max_right _ _).trans_lt hw
  have hm2 : 0 < m ^ 2 := pow_pos hodd.pos 2
  have hterm := fun x => htx (𝓞 E) A.N B d H.w0 hprim k β hbe m hm hodd w u huw _ _ (hrep _ hm2 x)
  refine ⟨fun x => ?_, ?_⟩
  · refine (d.eX.toEquiv.summable_iff (f := fun χ : A.N.X => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖)).1 ?_
    exact ((hsum w hw₂ ((m : ℂ)⁻¹ • B.Pw w (f (m ^ 2) x))).mul_left _).congr fun y =>
      (norm_mul _ _).symm.trans (congrArg norm (hterm x y).symm)
  obtain ⟨-, -, hlin, -, hspan, -, -, -, hper⟩ := hT₁ w hw₁
  let P : B.La →+ (Fin g → ℂ) := h.toLinearMap.toAddMonoidHom.comp (B.Pw w)
  obtain ⟨hinj, hdisc, hsp, Hm, hherm, hpos, him⟩ := hper g h P fun _ => rfl
  have hPlin : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i := fun a x i =>
    (congrArg (fun v => h v i) (hlin a x)).trans (hh a _ i)
  obtain ⟨Q, oa, U, Hm', χ, F, hΛ, hpr, hdet, hAH, hΛ', him', hχ, hex, hW⟩ :=
    hobj E H D B.La B.EF g ty P Hm htyp hbij hadj hPlin hinj hdisc hsp hherm hpos him
  let P' : B.La →+ (Fin Q.g → ℂ) := F.toLinearMap.toAddMonoidHom.comp P
  obtain ⟨I, hI, hev⟩ := exists_tateIso D B.EF Q oa.act oa.hom U P' (F.injective.comp hinj)
    (fun z => ⟨hΛ' z, fun ⟨a, ha⟩ => ha ▸ hΛ a⟩) (fun c s a => by
      have := hex c (s • P a)
      rw [map_smul] at this
      refine Eq.trans (congrArg U.ex ?_) this
      refine (map_smul F s _).symm.trans (congrArg F (funext fun i => ?_))
      simp only [Pi.smul_apply, hPlin, smul_eq_mul]
      ring) hW A.I.ζ A.I.ζ_prim A.I.ζ_pow f hf
  have hS : Differentiable ℂ (B.Sum 1 0 d.th w) := fun v =>
    ((hdiff.differentiableAt ((isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)).mem_nhds
      (show T₂ < ((w, v) : ℂ × B.V).1.im from hw₂))).comp v
      ((differentiableAt_const w).prodMk differentiableAt_id) :)
  obtain ⟨Θ, hΘ, hΘ0, hΘp, hΘv⟩ := hth (𝓞 E) B H.w0 hprim d.th hmem w hS Q.g (h.trans F) Hm' hAH.1 hspan him'
  have hne : Θ ≠ 0 := by
    obtain ⟨v, hv⟩ := B.exists_Sum_ne_zero one_ne_zero 0 hth0 (w := w) fun z => (hsum w hw₂ _).of_norm
    exact fun e => hv ((hΘ0 v).1 (congrFun e _))
  have hfn : U.IsThetaFn Hm' χ 1 Θ := ⟨hΘ, fun l z => by
    obtain ⟨l, hl⟩ := l
    obtain ⟨a, rfl⟩ := hΛ' l hl
    rw [pow_one, hχ]
    exact hΘp a z⟩
  refine ⟨⟨Q, oa, hpr, H.rt0, H.sqrt_neg_disc_sq, hdet, I, inferInstance⟩, rfl, congrFun hI _, ?_⟩
  have key := isThetaPt_classical hL hL2 hT Q U Hm' χ Θ m (I.ev (m ^ 2)) (fun x => ⟨F (P (f _ x)), hΛ _⟩) hodd hAH hfn hne
    fun x => by rw [hev, Nat.cast_pow]; rfl
  refine Eq.mp (congrArg (IsThetaPt Q m (I.ev (m ^ 2))) (funext fun x => congrArg fnOf ?_)) key
  rw [hχ, _root_.mul_assoc]
  refine (congrArg (_ * ·) (hΘv _ m hodd.pos.ne')).trans ?_
  rw [← _root_.mul_assoc, AnArc.Sum, ← tsum_mul_left]
  exact (tsum_congr fun y => (hterm x y).symm).trans
    (d.eX.toEquiv.tsum_eq fun χ : A.N.X => (A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ)

theorem exists_full_of_small : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (A : ArcF D R ℂ), A.ρ = H.rt0 → ∀ (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ x, Summable fun χ => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖) ∧ ∃ o : Full D ℂ, o.ρ = H.rt0 ∧ o.I.ζ (m ^ 2) = A.I.ζ (m ^ 2) ∧ o.Theta m fun x => (A.N.twist β u).tx m (A.N.twQ β u hm (A.q _ x)) := fun hV _ _ _ _ _ hT =>
  have hL : Laws := hV.1.1
  have hL2 : Laws2 := hV.1.2.1
  have hF : BrFamSt := _root_.GlobalTheory.Ex.brFam hL hL2
  of_steps hL hL2 hT
    (_root_.GlobalTheory.Ex.Arch.dict_of_val (_root_.GlobalTheory.ActValues.brAct hL) (_root_.GlobalTheory.Ex.Arch.AbVal.valSt hL hF (_root_.GlobalTheory.Ex.Arch.FibEx.fibEx hL hT) _root_.GlobalTheory.Ex.Arch.fibGrp (_root_.GlobalTheory.Ex.Arch.fibCubeSt hL) (_root_.GlobalTheory.Ex.Arch.FibSym.fibSymSt hL)
      (_root_.GlobalTheory.Ex.Arch.FibRos.fibRosSt hL) (_root_.GlobalTheory.Ex.Arch.FibPrim.fibPrim_of_laws hL) _root_.GlobalTheory.Ex.Arch.fibSec (_root_.GlobalTheory.Ex.Arch.fibLie_of_laws hL)))
    (_root_.GlobalTheory.Ex.Arch.towerSt_of _root_.GlobalTheory.Ex.GtValues.points_correspond (_root_.GlobalTheory.WeilValues.weil_eq_values _root_.GlobalTheory.Ex.GtValues.points_correspond hF) _root_.GlobalTheory.Ex.Arch.ptSt (_root_.GlobalTheory.Ex.Arch.qkSt_of_ptSt _root_.GlobalTheory.Ex.Arch.ptSt) _root_.GlobalTheory.Ex.Arch.Wp.wp_eq)
    _root_.GlobalTheory.Ex.Arch.typeSt (_root_.GlobalTheory.Ex.Arch.objSt_of_triple_reframe hL (_root_.GlobalTheory.Ex.Arch.tripleSt_of_laws hL hT) (_root_.GlobalTheory.Ex.Arch.reframe hT)) _root_.GlobalTheory.Ex.Arch.theta_sum_appellHumbert (_root_.GlobalTheory.Ex.Arch.txSt_of_ptSt _root_.GlobalTheory.Ex.Arch.ptSt)

end GlobalTheory.Ex.Arch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemGenusOne
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.RealDimOne

open GlobalTheory.TorsionGenerators NumberField

theorem isPrimitiveRoot_unitOn {k : Type} [CommRing k] {u : kˣ} {M : ℕ} (h : IsPrimitiveRoot u M) :
    IsPrimitiveRoot (unitOn u) M :=
  h.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) unitOn_injective

theorem unitOn_zpow {k : Type} [CommRing k] (u : kˣ) (n : ℤ) : unitOn (u ^ n) = unitOn u ^ n :=
  map_zpow (Units.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toMonoidHom) u n

end GlobalTheory.ZH.RealDimOne
end
end

