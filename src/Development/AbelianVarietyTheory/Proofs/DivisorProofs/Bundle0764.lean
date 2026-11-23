module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0731
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0741
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0745
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0752
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0751
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0748
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLeOfIsCompact
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped ContDiff

namespace GlobalTheory.HeightBound

theorem height_le_of_isCompact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (Q : Set (Lie E a)),
    IsCompact Q → Q ⊆ invSet E a →
    ∃ H : ℝ, ∀ y : GL (Fin a) (Cinf E), toL y.val ∈ Q → GlobalTheory.CuspRep.height y ≤ H := by
  intro E _ _ _ a Q hQ hsub
  let f : Lie E a → Lie E a := fun w => toL ((Matrix.of w)⁻¹)
  have hdetc : Continuous (fun x : Lie E a => (Matrix.of x).det) := by
    simp only [Matrix.det_apply', Matrix.of_apply]
    refine continuous_finsetSum _ fun σ _ => continuous_const.mul (continuous_finsetProd _ fun i _ => ?_)
    exact (continuous_apply i).comp (continuous_apply (σ i))
  have hadj : Continuous (fun x : Lie E a => (Matrix.of x).adjugate) :=
    Continuous.matrix_adjugate (continuous_id : Continuous fun x : Lie E a => x)
  have hf : ContinuousOn f (invSet E a) := by
    intro w hw
    apply ContinuousAt.continuousWithinAt
    have hdet : IsUnit (Matrix.of w).det := (Matrix.isUnit_iff_isUnit_det _).1 hw
    have h1 : ContinuousAt (fun x : Lie E a => Ring.inverse (Matrix.of x).det) w := by
      have := NormedRing.inverse_continuousAt hdet.unit
      rw [hdet.unit_spec] at this
      exact this.comp hdetc.continuousAt
    refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun j => ?_
    simp only [f, toL, Matrix.inv_def, Matrix.smul_apply, Matrix.of_symm_apply, smul_eq_mul]
    exact h1.mul ((continuous_apply j).comp ((continuous_apply i).comp hadj)).continuousAt
  obtain ⟨C1, hC1⟩ := hQ.exists_bound_of_continuousOn (f := fun w : Lie E a => w) continuous_id.continuousOn
  obtain ⟨C2, hC2⟩ := hQ.exists_bound_of_continuousOn (hf.mono hsub)
  refine ⟨1 + C1 + C2, fun y hy => ?_⟩
  have h2 : f (toL y.val) = toL (y⁻¹).val := by
    simp only [f, toL, Equiv.apply_symm_apply, Matrix.coe_units_inv]
  have := hC2 _ hy
  rw [h2] at this
  unfold GlobalTheory.CuspRep.height
  linarith [hC1 _ hy]

end GlobalTheory.HeightBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFixedPullbackRepresentableGlue
section
set_option autoImplicit false
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.EndLoc.HomGlue

theorem reps_iso : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB) (X : Scheme.{0}) (u : HomGlue.Pt A B L M X), (∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z), ∃! c : Z ⟶ X, u.map hL hM c = x) → ∀ (W : S.Opens) (T : Scheme.{0}) (y : HomGlue.Pt A B L M T) (πT : T ⟶ W), y.t = πT ≫ W.ι → (∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ W), x.t = b ≫ W.ι → ∃! c : Z ⟶ T, y.map hL hM c = x) → ∃ e : T ≅ (u.t ⁻¹ᵁ W).toScheme, e.hom ≫ (u.t ∣_ W) = πT := by
  intro S A B _ _ L M hL hM X u hu W T y πT hy hloc
  obtain ⟨c, hc, -⟩ := hu T y
  have hcW : Set.range c ⊆ ((u.t ⁻¹ᵁ W).ι).opensRange := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.opensRange_ι]
    show u.t (c z) ∈ W
    have e : c ≫ u.t = πT ≫ W.ι := by rw [← hy, ← hc]; rfl
    rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
    exact (πT z).2
  let c' := IsOpenImmersion.lift (u.t ⁻¹ᵁ W).ι c (by simpa using hcW)
  have hc' : c' ≫ (u.t ⁻¹ᵁ W).ι = c := IsOpenImmersion.lift_fac _ _ _
  have hx : (u.map hL hM (u.t ⁻¹ᵁ W).ι).t = (u.t ∣_ W) ≫ W.ι := by
    rw [HomGlue.Pt.map_t, morphismRestrict_ι]
  obtain ⟨d, hd, -⟩ := hloc _ (u.map hL hM (u.t ⁻¹ᵁ W).ι) (u.t ∣_ W) hx
  have h1 : c' ≫ d = 𝟙 T := by
    refine (hloc T y πT hy).unique ?_ ?_
    · rw [HomGlue.Pt.map_comp, hd, ← HomGlue.Pt.map_comp, hc', hc]
    · exact HomGlue.Pt.map_id hL hM y
  have h2 : d ≫ c' = 𝟙 _ := by
    have : d ≫ c = (u.t ⁻¹ᵁ W).ι := (hu _ (u.map hL hM (u.t ⁻¹ᵁ W).ι)).unique
      (by rw [HomGlue.Pt.map_comp, hc, hd]) rfl
    rw [← cancel_mono (u.t ⁻¹ᵁ W).ι, Category.assoc, hc', this, Category.id_comp]
  refine ⟨⟨c', d, h1, h2⟩, ?_⟩
  show c' ≫ (u.t ∣_ W) = πT
  rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hc', ← hy, ← hc]
  rfl

theorem wit_of_eq {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {L : LB A.left} {M : LB B.left}
    {Z : Scheme.{0}} {t t' : Z ⟶ S} {f : pullback A.hom t ⟶ B.left} {f' : pullback A.hom t' ⟶ B.left} (h : t = t')
    (hf : ∀ e : pullback A.hom t' ⟶ pullback A.hom t, e ≫ pullback.fst _ _ = pullback.fst _ _ →
      e ≫ pullback.snd _ _ = pullback.snd _ _ → e ≫ f = f') (w : HomGlue.Wit A B L M t f) :
    HomGlue.Wit A B L M t' f' := by
  subst h
  have := hf (𝟙 _) (Category.id_comp _) (Category.id_comp _)
  rw [Category.id_comp] at this
  subst this
  exact w

theorem glue_pts : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB), IsAbelianScheme A → IsAbelianScheme B → Out.Rigidified A L → Out.Rigidified B M → ∀ (Z : Scheme.{0}) (𝒰 : Z.OpenCover) (x : ∀ i, HomGlue.Pt A B L M (𝒰.X i)), (∀ i j (T : Scheme.{0}) (b : T ⟶ 𝒰.X i) (c : T ⟶ 𝒰.X j), b ≫ 𝒰.f i = c ≫ 𝒰.f j → (x i).map hL hM b = (x j).map hL hM c) → ∃ y : HomGlue.Pt A B L M Z, ∀ i, y.map hL hM (𝒰.f i) = x i := by
  intro hiso S A B _ _ _ _ L M hL hM hA hB hrA hrB Z 𝒰 x hx
  obtain ⟨t, f, h⟩ := _root_.GlobalTheory.EndLoc.HomGlue.exists_glue_data S A B L M hL hM Z 𝒰 x hx
  have hw : ∀ i, HomGlue.Wit A B L M (𝒰.f i ≫ t) (HomGlue.pmap A t (𝒰.f i) ≫ f) := by
    intro i
    have hc : pullback.fst A.hom (x i).t ≫ A.hom = (pullback.snd A.hom (x i).t ≫ 𝒰.f i) ≫ t := by
      rw [pullback.condition, Category.assoc, (h i).1]
    refine wit_of_eq (h i).1.symm (fun e e1 e2 => ?_) (x i).wit
    rw [← (h i).2 (pullback.lift _ _ hc) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _), ← Category.assoc]
    congr 1
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, e1, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, e2, pullback.lift_snd]
  refine ⟨⟨t, f, _root_.GlobalTheory.EndLoc.HomGlue.glue_wit hiso S A B L M hL hM hA hB hrA hrB Z 𝒰 t f hw⟩, fun i => ?_⟩
  refine HomGlue.Pt.ext' (h i).1 ?_
  show _ ≫ HomGlue.pmap A t (𝒰.f i) ≫ f = _
  exact (Category.assoc _ _ _).symm.trans ((h i).2 _
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans (pullback.lift_fst _ _ _)))
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ 𝒰.f i) (pullback.lift_snd _ _ _))))))

theorem isSheaf_homFun : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (hL : L.IsLB) (hM : M.IsLB), IsAbelianScheme A → IsAbelianScheme B → Out.Rigidified A L → Out.Rigidified B M → Presieve.IsSheaf Scheme.zariskiTopology (HomGlue.homFun A B L M hL hM) := by
  intro hiso S A B _ _ _ _ L M hL hM hA hB hrA hrB
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y P hP
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hP
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  exact existsUnique_of_exists_of_unique
    (glue_pts hiso S A B L M hL hM hA hB hrA hrB Y 𝒰 x fun i j T b c h => hx i j T b c h)
    fun y y' h h' => _root_.GlobalTheory.EndLoc.HomGlue.Pt.ext_cover S A B L M hL hM Y 𝒰 y y' fun i => (h i).trans (h' i).symm

theorem homFixRep_glue : (∀ (H : Scheme.{0}) (A B : Over H) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsMonHom Φ → IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → (∀ h : H, ∃ W : H.Opens, h ∈ W ∧ LBIso (L.pull (A.hom ⁻¹ᵁ W).ι) ((M.pull Φ.left).pull (A.hom ⁻¹ᵁ W).ι)) → LBIso L (M.pull Φ.left)) → ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → ∀ (Ix : Type) (V : Ix → Scheme.{0}) (j : ∀ i, V i ⟶ S), (∀ i, IsOpenImmersion (j i)) → (∀ s : S, ∃ i, s ∈ Set.range (j i)) → (∀ i, ∃ (A' B' : Over (V i)) (_ : GrpObj A') (_ : GrpObj B') (φA : A'.left ⟶ A.left) (φB : B'.left ⟶ B.left) (R : HomFixRep A' B' (L.pull φA) (M.pull φB)), IsGrpPullback A' A (j i) φA ∧ IsGrpPullback B' B (j i) φB ∧ QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π) → ∃ R : HomFixRep A B L M, QuasiCompact R.π ∧ IsSeparated R.π ∧ LocallyOfFiniteType R.π := by
  intro hiso S A B _ _ _ _ L M hA hB hL hM hrA hrB Ix V j hj hcov hR
  choose A' B' gA gB φA φB R hpA hpB hqc hsep hlft using hR
  have hy : ∀ i, ∃ y : HomGlue.Pt A B L M (R i).H, y.t = (R i).π ≫ j i ∧ ∀ (Z : Scheme.{0})
      (x : HomGlue.Pt A B L M Z) (b : Z ⟶ V i), x.t = b ≫ j i → ∃! c : Z ⟶ (R i).H, y.map hL hM c = x := by
    intro i
    letI := gA i; letI := gB i
    exact _root_.GlobalTheory.EndLoc.HomGlue.localRep_universal S A B L M hL hM (V i) (j i) (A' i) (B' i) (φA i) (φB i) (R i) (hpA i) (hpB i)
  choose y hyt hyu using hy
  let W : Ix → S.Opens := fun i => (j i).opensRange
  have hW : iSup W = ⊤ := by
    refine top_le_iff.1 fun s _ => ?_
    obtain ⟨i, hi⟩ := hcov s
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  let πW : ∀ i, (R i).H ⟶ W i := fun i => (R i).π ≫ (j i).isoOpensRange.hom
  have hπW : ∀ i, πW i ≫ (W i).ι = (R i).π ≫ j i := fun i => by
    simp [πW, W]
  have hloc : ∀ i (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z) (b : Z ⟶ W i), x.t = b ≫ (W i).ι →
      ∃! c : Z ⟶ (R i).H, (y i).map hL hM c = x := by
    intro i Z x b hb
    refine hyu i Z x (b ≫ (j i).isoOpensRange.inv) ?_
    rw [hb, Category.assoc]; simp [W]
  have hrep : (HomGlue.homFun A B L M hL hM).IsRepresentable :=
    GlobalTheory.GenTorsor.isRepresentable_of_cover _ (isSheaf_homFun hiso S A B L M hL hM hA hB hrA hrB) (HomGlue.homProj A B L M hL hM)
      W hW (fun i => (R i).H) y πW (fun i => (hyt i).trans (hπW i).symm) hloc
  set F := HomGlue.homFun A B L M hL hM
  let X := F.reprX
  let u : HomGlue.Pt A B L M X := F.reprx
  have huniv : ∀ (Z : Scheme.{0}) (x : HomGlue.Pt A B L M Z), ∃! c : Z ⟶ X, u.map hL hM c = x := by
    intro Z x
    have key : ∀ c : Z ⟶ X, u.map hL hM c = F.representableBy.homEquiv c := fun c => by
      rw [F.representableBy.homEquiv_eq c]; rfl
    refine ⟨F.representableBy.homEquiv.symm x, ?_, fun c hc => ?_⟩
    · dsimp only; rw [key]; exact F.representableBy.homEquiv.apply_symm_apply x
    · dsimp only at hc; rw [key] at hc; rw [← hc]; exact (F.representableBy.homEquiv.symm_apply_apply c).symm
  obtain ⟨R0, e, he⟩ := _root_.GlobalTheory.EndLoc.HomGlue.homFixRep_of_universal S A B L M hL hM X u huniv
  have hloc' : ∀ i, ∃ e : (R i).H ≅ (u.t ⁻¹ᵁ W i).toScheme, e.hom ≫ (u.t ∣_ W i) = πW i := fun i =>
    reps_iso S A B L M hL hM X u huniv (W i) (R i).H (y i) (πW i) ((hyt i).trans (hπW i).symm) (hloc i)
  choose ei hei using hloc'
  have key : ∀ i, u.t ∣_ W i = (ei i).inv ≫ πW i := fun i => by
    rw [← hei i, Iso.inv_hom_id_assoc]
  have hP : ∀ (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P],
      (∀ i, P (R i).π) → P R0.π := by
    intro P _ hR
    rw [← he]
    refine (MorphismProperty.cancel_left_of_respectsIso P e.hom u.t).2 ?_
    refine IsZariskiLocalAtTarget.of_iSup_eq_top W hW fun i => ?_
    rw [key i]
    refine (MorphismProperty.cancel_left_of_respectsIso P _ _).2 ?_
    exact (MorphismProperty.cancel_right_of_respectsIso P _ _).2 (hR i)
  have : IsZariskiLocalAtTarget @QuasiCompact.{0} := by
    set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
  have : IsZariskiLocalAtTarget @LocallyOfFiniteType.{0} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFiniteType)
  exact ⟨R0, hP @QuasiCompact hqc, hP @IsSeparated hsep, hP @LocallyOfFiniteType hlft⟩

end GlobalTheory.EndLoc.HomGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomomorphismMatrixUniqueFixedPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq

noncomputable section

namespace GlobalTheory.HomFixUniq

theorem mat_unique : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B') (c c' : Fin mA → Fin mB → Γ(Sp R, ⊤)), IsTest A B L M t A' B' φA' φB' Φ' → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c → IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c' → c = c' := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH R _ t A' B' _ _ φA' φB' Φ' c c' hT h₁ h₂
  obtain ⟨hAab, -, hL, hM, -, -, -, -, -, hbA, -⟩ := hH
  obtain ⟨ψA, ψB, α, hψA, hψB, hα, hrig, hmat⟩ := h₁
  obtain ⟨ψA₂, ψB₂, α₂, hψA₂, hψB₂, hα₂, hrig₂, hmat₂⟩ := h₂
  obtain rfl : ψA₂ = ψA := psi_unique _ _ (hψA₂.trans hψA.symm)
  obtain rfl : ψB₂ = ψB := psi_unique _ _ (hψB₂.trans hψB.symm)
  obtain ⟨v, hv⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.ChartFrameTrA.exists_ratio_gen
    (isoLB_cover (L := L) (M := M) hL hM k Φ' ψA₂ ψB₂) hα hα₂
  have v1 : v = 1 := GlobalTheory.T.normalised_isoPowerBundle_ratio_unit_eq_one Rg A B L M k eA eB hAab hL hM R t A' B' φA' φB' Φ' ψA₂ ψB₂ α α₂ v hT hψA hψB hv hrig hrig₂
  have hαe : ∀ p, α.s p = α₂.s p := fun p => by rw [hv p, v1, map_one, _root_.one_mul]
  funext i j
  have hd := GlobalTheory.T.pullback_sections_group_scheme Rg A L k mA bA hbA R t A' φA' ψA₂ hT.1 hψA₂ (fun i => c i j - c' i j) (fun jL x hx => by
    obtain ⟨iM, hiM⟩ : ∃ iM, ((((Φ'.left ≫ ψB₂) ≫ (snd (topS Rg) B).left)).base x) ∈ M.U iM :=
      TopologicalSpace.Opens.mem_iSup.1 (by rw [hM.cover]; trivial)
    refine ⟨(isoLB (L := L) (M := M) k Φ' ψA₂ ψB₂).U (fun _ => iM, jL), inf_le_right,
      ⟨Set.mem_iInter.2 fun _ => hiM, hx⟩, ?_⟩
    have e := (hmat j (fun _ => iM, jL)).symm.trans (hmat₂ j (fun _ => iM, jL))
    have e1 := congrArg Units.val (hαe (fun _ => iM, jL))
    erw [e1] at e
    have e2 := (α₂.s (fun _ => iM, jL)).isUnit.mul_left_cancel e
    simp only [map_sub, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 e2)
  exact sub_eq_zero.1 (congrFun hd i)

end GlobalTheory.HomFixUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMonicPolynomialOfUnitRelation
section
open scoped TensorProduct
open IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.OddLocalNorm

theorem exists_eq_of_finite (O : Type) {S : Type} [CommRing O] [HenselianLocalRing O]
    [Finite (ResidueField O)] [CommRing S] [Algebra O S] [Module.Finite O S]
    (h2 : IsUnit (2 : O)) {m d : S} (hm : IsUnit m) (hd : IsUnit d) :
    ∃ a b : S, m = a * a - d * (b * b) := by
  let T := QuadraticAlgebra S d 0
  haveI : Module.Finite O T := Module.Finite.trans S T
  let I : Ideal T := (maximalIdeal O).map (algebraMap O T)
  have hI : I ≤ (⊥ : Ideal T).jacobson := by
    refine le_sInf fun M hM => Ideal.map_le_iff_le_comap.2 ?_
    haveI := hM.2
    exact (eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := O) M)).ge
  haveI : HenselianRing T I := GlobalTheory.henselianRing_of_finite O I hI
  haveI : Finite (O ⧸ maximalIdeal O) := inferInstanceAs (Finite (ResidueField O))
  haveI : Module.Finite O (T ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O I).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Module.Finite (O ⧸ maximalIdeal O) (T ⧸ I) :=
    Module.Finite.of_restrictScalars_finite O _ _
  haveI : Finite (T ⧸ I) := Module.finite_of_finite (O ⧸ maximalIdeal O)
  have hc : ∀ s : S, starRingEnd T (algebraMap S T s) = algebraMap S T s := by
    intro s
    ext <;> simp [T, starRingEnd_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hcO : (starRingEnd T).comp (algebraMap O T) = algebraMap O T := by
    ext1 r
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply O S T, hc]
  have hcI : I ≤ I.comap (starRingEnd T) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hcO]
    exact Ideal.le_comap_map
  have h2S : IsUnit (2 : S) := by
    simpa only [map_ofNat] using h2.map (algebraMap O S)
  obtain ⟨x, hx⟩ := GlobalTheory.HenselianNorm.exists_norm_eq T I (starRingEnd T)
    (fun x => star_star x) (fun x hx => hcI hx)
    ⟨⟨0, 1⟩, by
      have h : ((⟨0, 1⟩ : T) - starRingEnd T ⟨0, 1⟩) * ((⟨0, 1⟩ : T) - starRingEnd T ⟨0, 1⟩)
          = algebraMap S T (2 * 2 * d) := by
        ext <;> simp [T, starRingEnd_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
        ring
      exact isUnit_of_mul_isUnit_left (h ▸ ((h2S.mul h2S).mul hd).map (algebraMap S T))⟩
    (algebraMap S T m) (hc m) (hm.map _)
  refine ⟨x.re, x.im, ?_⟩
  have := congrArg QuadraticAlgebra.re hx
  simp [T, starRingEnd_apply, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] at this
  linear_combination -this

theorem exists_eq_of_isIntegral (O : Type) {A : Type} [CommRing O] [HenselianLocalRing O]
    [Finite (ResidueField O)] [CommRing A] [Algebra O A]
    (h2 : IsUnit (2 : O)) {m m' d d' : A} (hm : m * m' = 1) (hd : d * d' = 1)
    (im : IsIntegral O m) (im' : IsIntegral O m') (id : IsIntegral O d) (id' : IsIntegral O d') :
    ∃ a b : A, m = a * a - d * (b * b) := by
  let S := Algebra.adjoin O ({m, m', d, d'} : Set A)
  haveI : Module.Finite O S := Algebra.finite_adjoin_of_finite_of_isIntegral (Set.toFinite _) (by
    rintro x (rfl | rfl | rfl | rfl) <;> assumption)
  have h1 : m ∈ S := Algebra.subset_adjoin (by simp)
  have h1' : m' ∈ S := Algebra.subset_adjoin (by simp)
  have h3 : d ∈ S := Algebra.subset_adjoin (by simp)
  have h3' : d' ∈ S := Algebra.subset_adjoin (by simp)
  obtain ⟨a, b, h⟩ := exists_eq_of_finite O h2 (m := (⟨m, h1⟩ : S)) (d := ⟨d, h3⟩)
    (IsUnit.of_mul_eq_one ⟨m', h1'⟩ (Subtype.ext hm)) (IsUnit.of_mul_eq_one ⟨d', h3'⟩ (Subtype.ext hd))
  exact ⟨a, b, congrArg Subtype.val h⟩

end GlobalTheory.OddLocalNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeAndPullOfIsGrpPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.GrpPullbackPol

theorem isAbelianScheme_and_pull_of_isGrpPullback :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S')
      [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ A.left) (L : LB A.left),
      IsGrpPullback A' A f φ → IsAbelianScheme A → L.IsLB → Out.Rigidified A L →
        Out.RelAmple A L →
        IsAbelianScheme A' ∧ (L.pull φ).IsLB ∧ Out.Rigidified A' (L.pull φ) ∧
          Out.RelAmple A' (L.pull φ) := by
  intro S S' f A _ _ A' _ _ φ L h hA hL hr ha
  have hp : IsProper A.hom := hA.proper
  refine ⟨⟨inferInstance, ?_, ?_, ?_⟩, pull_isLB hL φ, PolBaseChange.rigidified_pull h hr, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth
  · exact MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper
  · exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected
  · exact AmpleBaseChange.relAmple_of_isPullback hL ha h.1

end GlobalTheory.GrpPullbackPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGeneratorIsoBundleOfMatrixRelation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.HomFixUniv.CondGen

theorem gs_appLE_self {X Y : Scheme.{0}} (q : Y ⟶ X) (U : X.Opens) (W : Y.Opens) (e : W ≤ q ⁻¹ᵁ U) (z : Y)
    (hz : z ∈ W) (f : Γ(X, U)) : gs (𝟙 Y) z W ((q.appLE U W e).hom f) = gs q z U f := by
  have h1 := gs_res (𝟙 Y) z e hz ((q.app U).hom f)
  have h2 := gs_pull (𝟙 Y) q z U (e hz) f
  rw [Category.id_comp] at h2
  exact h1.trans h2

theorem gs_fsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {n : ℕ} (a : Fin n → Γ(X, U)) :
    gs f y U (∑ i, a i) = ∑ i, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

end GlobalTheory.HomFixUniv.CondGen


open GlobalTheory.HomFixUniv.CondGen in
theorem GlobalTheory.HomFixUniv.isGen_of_matRel : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (R : Type) [CommRing R] (A' B' : Over (Sp R)) (Φ' : A' ⟶ B') (ψA : A'.left ⟶ (topS Rg ⊗ A).left) (ψB : B'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(Sp R, ⊤)) (u : ∀ p, Γ(A'.left, (isoLB (L := L) (M := M) k Φ' ψA ψB).U p)ˣ), GlobalTheory.HomFixUniv.Generates bA ψA A'.hom c → (∀ (j : Fin mB) (p : (Fin 1 → M.ι) × (Fin 1 → L.ι)),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (u p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (c i j) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2)) → (⟨u⟩ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB)).IsGen := by
  intro Rg _ A B _ _ L M k mA mB bA bB R _ A' B' Φ' ψA ψB c u hG hR p p'
  apply unit_ext
  intro z hz
  have hzp : z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p := hz.1
  have hzp' : z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U p' := hz.2
  have hmB : (Φ'.left ≫ ψB) z ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1 :=
    GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1 hzp.1
  have hmB' : (Φ'.left ≫ ψB) z ∈ LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p'.1 :=
    GlobalTheory.HomFixMat.wchart_comp_le M _ _ p'.1 hzp'.1
  have hmA : ψA z ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2 :=
    GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2 hzp.2
  have hmA' : ψA z ∈ LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p'.2 :=
    GlobalTheory.HomFixMat.wchart_comp_le L _ _ p'.2 hzp'.2
  have key : ∀ (q : (Fin 1 → M.ι) × (Fin 1 → L.ι)), z ∈ (isoLB (L := L) (M := M) k Φ' ψA ψB).U q → ∀ j : Fin mB,
      gs (Φ'.left ≫ ψB) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) q.1) ((bB j).f q.1) =
        (gm (𝟙 _) z _ (u q)).val * GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z q.2 j := by
    intro q hq j
    have e := congrArg (gs (𝟙 A'.left) z ((isoLB (L := L) (M := M) k Φ' ψA ψB).U q)) (hR j q)
    refine (gs_appLE_self _ _ _ _ z hq _).symm.trans (e.trans ?_)
    rw [gs_mul _ z _ hq, gs_unit _ z _ hq, gs_fsum _ z _ hq]
    unfold GlobalTheory.HomFixUniv.comb
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_mul _ z _ hq]
    exact congrArg₂ (· * ·) (gs_appLE_self _ _ _ _ z hq _) (gs_appLE_self _ _ _ _ z hq _)
  have tB : ∀ j : Fin mB, gs (Φ'.left ≫ ψB) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1) ((bB j).f p.1) =
      (trF (L := M) (fun _ : Fin 1 => (snd (topS Rg) B).left) (fun _ => (k : ℤ)) (Φ'.left ≫ ψB) z p.1 p'.1).val *
        gs (Φ'.left ≫ ψB) z (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p'.1) ((bB j).f p'.1) :=
    fun j => sec_trans (bB j) (Φ'.left ≫ ψB) z hmB hmB'
  have tA : ∀ i : Fin mA, gs ψA z (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2) ((bA i).f p.2) =
      (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2).val *
        gs ψA z (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p'.2) ((bA i).f p'.2) :=
    fun i => sec_trans (bA i) ψA z hmA hmA'
  have tC : ∀ j : Fin mB, GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z p.2 j =
      (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2).val *
        GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z p'.2 j := by
    intro j
    unfold GlobalTheory.HomFixUniv.comb
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (congrArg (_ * ·) (tA i)).trans (mul_left_comm _ _ _)
  have hg : gm (𝟙 A'.left) z _ ((isoLB (L := L) (M := M) k Φ' ψA ψB).g p p') =
      trF (L := M) (fun _ : Fin 1 => (snd (topS Rg) B).left) (fun _ => (k : ℤ)) (Φ'.left ≫ ψB) z p.1 p'.1 *
        (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2)⁻¹ := by
    show gm (𝟙 A'.left) z _ (res _ _ * (res _ _)⁻¹) = _
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ z _ hz _).trans ?_)
      ((map_inv _ _).trans (congrArg _ ((gm_res _ z _ hz _).trans ?_))))
    · exact (gm_linComb M _ _ (𝟙 A'.left) z p.1 p'.1 hzp.1 hzp'.1).trans (by simp only [trF, Category.id_comp])
    · exact (gm_linComb L _ _ (𝟙 A'.left) z p.2 p'.2 hzp.2 hzp'.2).trans (by simp only [trF, Category.id_comp])
  obtain ⟨j, hj⟩ := hG z p.2 hmA
  refine (gm_res _ z _ hz _).trans (Eq.trans ?_ (map_mul _ _ _).symm)
  rw [hg, gm_res _ z _ hz]
  apply Units.ext
  apply hj.mul_right_cancel
  have e1 := key p hzp j
  have e2 := key p' hzp' j
  have e3 := tB j
  have e4 := tC j
  have hinv := Units.inv_mul (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2)
  rw [e1, e2, e4] at e3
  simp only [Units.val_mul]
  rw [e4]
  set TM := (trF (L := M) (fun _ : Fin 1 => (snd (topS Rg) B).left) (fun _ => (k : ℤ)) (Φ'.left ≫ ψB) z p.1 p'.1).val
  set TL := (trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2).val
  set TLi := ((trF (L := L) (fun _ : Fin 1 => (snd (topS Rg) A).left) (fun _ => (k : ℤ)) ψA z p.2 p'.2)⁻¹).val
  set U' := (gm (𝟙 A'.left) z _ (u p')).val
  set C' := GlobalTheory.HomFixUniv.comb bA ψA A'.hom c z p'.2 j
  linear_combination e3 - (TM * U' * C') * hinv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUniformiserAtIffAdicCompletionIsUnifAtStatement
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Neutral.B1
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUniformiserAt_iff_adicCompletion_isUnifAt : ∀ {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ), IsUniformiserAt K v (x : v.adicCompletion K) ↔ Formalism.L2.Host.IsUnifAt v x := by
  first | exact @GlobalTheory.UnifVal.isUniformiserAt_iff_isUnifAt | exact GlobalTheory.UnifVal.isUniformiserAt_iff_isUnifAt | (intros; apply GlobalTheory.UnifVal.isUniformiserAt_iff_isUnifAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntegersHenselianFiniteResidueStatement
section
open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicIntegers_henselian_finiteResidue : ∀ (v : HeightOneSpectrum ℤ), HenselianLocalRing (v.adicCompletionIntegers ℚ) ∧ Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := by
  first | (exact @GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField) | (exact GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField) | (intros; apply GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField <;> assumption)
end

