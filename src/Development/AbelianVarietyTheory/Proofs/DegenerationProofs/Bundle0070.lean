module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0042

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem nonempty_psiOn_field {K : Type} [Field K] (D : DegPre K) : Nonempty (PsiOn D ⊤) := by
  refine nonempty_psiOn_top D fun χ => (psiUnitOn_univ_iff D χ).2 ?_
  let σ : FractionRing K ≃+* K := (FractionRing.algEquiv K K).toRingEquiv
  let s : Sp K ⟶ (TK K).left := spMap σ.toRingHom
  have h₁ : s ≫ jK K = 𝟙 _ := by
    refine (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun x => ?_)).trans (Spec.map_id (CommRingCat.of K)))
    exact (FractionRing.algEquiv K K).commutes x
  have h₂ : jK K ≫ s = 𝟙 _ := by
    refine (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext fun x => ?_)).trans (Spec.map_id (CommRingCat.of (FractionRing K))))
    exact (FractionRing.algEquiv K K).injective ((FractionRing.algEquiv K K).commutes _)
  obtain ⟨t, ht, vt⟩ := exists_gen D.P.isLB (K' := PUnit) (φ' := fun _ => ((D.c χ).left : Sp K ⟶ _)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (by
      show s ≫ jK K ≫ (D.c χ).left = _
      rw [← Category.assoc, h₁, Category.id_comp]))
    (LB.pullGen D.P.L _ _ (D.psi χ) s) (DVR.pullGen_isGen _ _ _ _ (D.psi_gen χ) s)
  refine ⟨t, ht, corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (val_pull hJ _ _ _).trans ((vt _ _ y J hJ).trans ((val_pull hJ _ _ _).trans ?_))
  exact congrArg (fun q => val (D.psi χ) q y J) ((Category.assoc _ _ _).trans
    ((congrArg (𝟙 _ ≫ ·) h₂).trans (Category.id_comp _)))

theorem exists_isPullDeg_of_val {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK K).left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (D.psi (xe x)) (genMap i.injective) z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ ∧ hD.xe = xe ∧ HEq hD.w w := by
  obtain ⟨ψW⟩ := nonempty_psiOn_field D
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨g, hg⟩ : ∃ g : (TK K).left ⟶ (TW (⊤ : (Sp K₀).Opens)).left, g ≫ (⊤ : (Sp K₀).Opens).ι = jK K ≫ specOf i :=
    ⟨IsOpenImmersion.lift (⊤ : (Sp K₀).Opens).ι (jK K ≫ specOf i) (by
      rw [Scheme.Opens.range_ι]; exact Set.subset_univ _), IsOpenImmersion.lift_fac _ _ _⟩
  have sq : g ≫ (⊤ : (Sp K₀).Opens).ι = genMap i.injective ≫ jK K₀ :=
    hg.trans ((Category.id_comp _).symm.trans (fracMap_sq i.injective))
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK K).left ⟶ (jK K₀ ⁻¹ᵁ ⊤).toScheme, lam ≫ (jK K₀ ⁻¹ᵁ ⊤).ι = genMap i.injective ∧
      lam ≫ (jK K₀ ∣_ ⊤) = g :=
    ⟨(isPullback_morphismRestrict (jK K₀) ⊤).lift _ _ sq,
      (isPullback_morphismRestrict (jK K₀) ⊤).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK K₀) ⊤).lift_fst _ _ _⟩
  have hx : ∀ x, g ≫ (toUnit (TW ⊤) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ (⊤ : (Sp K₀).Opens).ι ≫ (D.c (xe x)).left = (jK K ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) lam).trans (val_pull hJ _ _ _))
    rw [l₁, l₂, hψ x y J J' hJ hJ'] at u
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, ⊤, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, rfl, HEq.rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

theorem pmaps_rig {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
    {D' : DegPre R'} (hD : IsPullDeg φ D D') :
    PMaps hD.w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap φ) :=
  (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
    (rigPull_le (proj hD) (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig

end GlobalTheory.FieldPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelMapTorsionCharactersStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labelMap_torsion_characters : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range, Function.Surjective yy ∧ (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) := by
  first | exact @GlobalTheory.ZH.LabelMap.exists_labelMap | exact GlobalTheory.ZH.LabelMap.exists_labelMap | (intros; apply GlobalTheory.ZH.LabelMap.exists_labelMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNeZeroOfLe
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.OpenPart

theorem le_nonzeroLocus_iff {k K : Type} [CommRing k] [Field K] {X : Scheme.{0}} {p : X ⟶ Sp k} {H : LB X}
    {J : Type} [Fintype J] {s : J → H.Sec} {a : J → k} {φ : H.Sec} (hφ : IsLin p s a φ)
    {x : Sp K ⟶ X} {ψ : k →+* K} (hx : x ≫ p = spMap ψ) {v : J → K} (hv : Crd H s x v) :
    ⊤ ≤ x ⁻¹ᵁ nonzeroLocus φ ↔ ∑ j, ψ (a j) * v j ≠ 0 := by
  have h : Crd H (fun _ : Unit => φ) x (fun _ => ∑ j, ψ (a j) * v j) := by
    obtain ⟨l, c, hl, hv⟩ := hv
    refine ⟨l, c, hl, fun _ => ?_⟩
    beta_reduce
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hφ l, CrdCalc.valR_eq x _ hl, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← CrdCalc.valR_eq, ← CrdCalc.valR_eq,
      GlobalTheory.Points.valR_constFn_of_over p ψ x hx _ hl, hv, mul_left_comm]
  exact (CrdCalc.crd_isUnit_iff () h).symm.trans isUnit_iff_ne_zero

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {M : RatModel o Ω}

theorem TT_le_TT {z z' : M.Z} (h : S.supI M z' ⊆ S.supI M z) : S.TT M z ≤ S.TT M z' :=
  fun _ ha b hb => ha b (AddSubgroup.closure_mono h hb)

theorem isOpen_supI_subset (z : M.Z) : IsOpen {z' | S.supI M z ⊆ S.supI M z'} := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : {z' | S.supI M z ⊆ S.supI M z'} = ⋂ a ∈ S.supI M z, {z' | M.Div S.th a z'} := by
    ext z'
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl
  rw [this]
  exact (Set.toFinite _).isOpen_biInter fun a _ => M.isOpen_setOf_div _ _

theorem supI_subset {U₀ : M.Z.Opens} (h : S.Over₀ M U₀) (z : M.Z) {z' : M.Z} (hz' : z' ∈ U₀) :
    S.supI M z ⊆ S.supI M z' := fun a ha => ⟨ha.1, fun j => by
  rw [div_eq_mul_inv]
  exact RatModel.ringOn_le_O hz' (mul_mem (h.le (S.th_mem j)) (h.th_unit a ha.1))⟩

theorem exists_ne_zero_of_le {T T' : AddSubgroup S.Gam} (h : T' ≤ T) (hT : S.IsoFree T) (hT' : S.IsoFree T')
    {K : Type} [Field K] (ψ : o →+* K) (v : S.J → K) {i : S.J} (hi : ∑ j, ψ (S.proj T 0 j i) * v j ≠ 0) :
    ∃ i, ∑ j, ψ (S.proj T' 0 j i) * v j ≠ 0 := by
  by_contra hn
  push_neg at hn
  apply hi
  rw [← GlobalTheory.ThetaBound.proj_mul_proj S T T' h hT.1 hT' 0 0 fun _ => rfl]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k _ => ?_
  have := congrArg (ψ (S.proj T 0 k i) * ·) (hn k)
  simp only [Finset.mul_sum, mul_zero] at this
  rw [← this]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem le_preimage_G_iff : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (K : Type) [Field K] (x : Sp K ⟶ Q.P.left) (z : M.Z) (ψ : o →+* K) (v : S.J → K), Set.range (x ≫ Q.P.hom) = {z} → (IsClosed ({z} : Set M.Z) ∨ z ∈ U₀) → x ≫ Q.P.hom ≫ M.s = spMap ψ → Crd Q.O1 Q.st x v → (⊤ ≤ x ⁻¹ᵁ Q.G ↔ ∃ i, ∑ j, ψ (S.proj (S.TT M z) 0 j i) * v j ≠ 0) := by
  intro o Ω _ _ _ _ S ρ M U₀ EE hB Q K _ x z ψ v hz hc hψ hv
  have hψ' : x ≫ (Q.P.hom ≫ M.s) = spMap ψ := hψ
  have hxz : Q.P.hom (x (IsLocalRing.closedPoint K)) = z := by
    have : (x ≫ Q.P.hom) (IsLocalRing.closedPoint K) ∈ Set.range (x ≫ Q.P.hom) := ⟨_, rfl⟩
    rw [hz] at this
    exact this
  rw [CrdCalc.top_le_iff]
  simp only [Clos.G, TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨z', -, W, hW, i, φ, hφ, h1, h2⟩
    have h1' : z ∈ W := hxz ▸ h1
    exact exists_ne_zero_of_le (TT_le_TT (hW z h1')) (hB.free _).1 (hB.free _).1 ψ v
      ((le_nonzeroLocus_iff hφ hψ' hv).1 ((CrdCalc.top_le_iff x _).2 h2))
  · intro hi
    obtain ⟨z', hz', hs, hs'⟩ : ∃ z' : M.Z, IsClosed ({z'} : Set M.Z) ∧ S.supI M z' ⊆ S.supI M z ∧
        S.supI M z ⊆ S.supI M z' := by
      rcases hc with hc | hc
      · exact ⟨z, hc, le_rfl, le_rfl⟩
      · have := hB.jac
        obtain ⟨z', h1, h2⟩ := nonempty_inter_closedPoints (Z := (U₀ : Set M.Z)) ⟨z, hc⟩
          U₀.isOpen.isLocallyClosed
        exact ⟨z', h2, supI_subset hB.ov _ hc, supI_subset hB.ov _ h1⟩
    obtain ⟨i, hi⟩ := hi
    obtain ⟨i, hi⟩ := exists_ne_zero_of_le (TT_le_TT hs') (hB.free _).1 (hB.free _).1 ψ v hi
    obtain ⟨φ, hφ, -⟩ := GlobalTheory.SecRatio.existsUnique_isLin (Q.P.hom ≫ M.s) Q.st
      (fun j => S.proj (S.TT M z') 0 j i)
    refine ⟨z', hz', ⟨_, isOpen_supI_subset z'⟩, fun _ h => h, i, φ, hφ, ?_,
      (CrdCalc.top_le_iff x _).1 ((le_nonzeroLocus_iff hφ hψ' hv).2 hi)⟩
    change S.supI M z' ⊆ S.supI M (Q.P.hom (x (IsLocalRing.closedPoint K)))
    rw [hxz]
    exact hs

end GlobalTheory.ZH.OpenPart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalisedMulPullIsoOriginStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalised_mulPull_iso_origin : Laws → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))), rig.IsGen → ∀ (m N : ℕ), N = m ^ 2 → ∀ T : Over S, ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd T P.A).left, (snd T P.A ^ m).left] ![(N : ℤ), -1]), α.IsGen ∧ LB.Gen.Corr P.L _ _ _ _ (LB.pullGen P.L _ _ α (ptSecT P.A 1).left) (LB.mulGen P.L _ _ _ _ (rigT P.A P.L rig T N) (rigT P.A P.L rig T (-1))) := by
  first | exact @GlobalTheory.ThetaReal.exists_normalised_mulPull | exact GlobalTheory.ThetaReal.exists_normalised_mulPull | (intros; apply GlobalTheory.ThetaReal.exists_normalised_mulPull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOperators
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaReal

theorem pt_nsmul {G H : Type} [AddCommGroup G] [Group H] (pt : G → H) (h : ∀ a b, pt (a + b) = pt a * pt b) :
    pt 0 = 1 ∧ ∀ (n : ℕ) a, pt (n • a) = pt a ^ n := by
  have h0 : pt 0 = 1 := by
    have := h 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  refine ⟨h0, fun n a => ?_⟩
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

theorem eStd_nsmul (g M r : ℕ) (a b : Fin g ⊕ Fin g → ZMod M) : eStd g M a (r • b) = r • eStd g M a b := by
  simp only [eStd, Finset.smul_sum, Pi.smul_apply, nsmul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem nsmul_self {κ : Type} (M : ℕ) (a : κ → ZMod M) : M • a = 0 := by
  funext i
  simp

theorem exists_operators (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {g m r N : ℕ}
    (hN : N = m ^ 2) (hm : Odd m) (hu : IsUnit ((r * N : ℕ) : Γ(S, ⊤))) (ze : Γ(S, ⊤)ˣ)
    (pt : (Fin g ⊕ Fin g → ZMod (r * N)) → (baseOver S ⟶ P.A)) (hadd : ∀ a b, pt (a + b) = pt a * pt b)
    (hw : ∀ a b, WeilIs P.A P.L (r * N : ℕ) (pt a) (pt b) (ze ^ (r * N * (eStd g (r * N) a b).val)))
    (U : (Fin g ⊕ Fin g → ZMod (r * N)) → ThetaGrp P.A P.L N (baseOver S))
    (hU : ∀ a, SymLift P.A P.L N N (pt (r • a)) (U a))
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver S) P.A).left, (snd (baseOver S) P.A ^ m).left]
      ![(N : ℤ), -1])} (hα : α.IsGen) {th : LB.Sec (LPow P.A P.L 1 (baseOver S))}
    {s₀ : LB.Sec (LPow P.A P.L N (baseOver S))}
    (hs : IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) N 1 α th s₀) :
    ∃ u : (Fin g ⊕ Fin g → ZMod (r * N)) →
        SecM P.A P.L N (baseOver S) →ₗ[Γ((baseOver S).left, ⊤)] SecM P.A P.L N (baseOver S),
      (∀ a s s', IsActOf P.A P.L N (U a) s s' ↔ u a (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧
      (∀ a, r • a = 0 → ∀ v, u a v = v) ∧
      (∀ a b, ∃ e : ℕ, ∀ v, u a (u b v) = (show Γ((baseOver S).left, ⊤) from ze.val ^ e) • u (a + b) v) ∧
      (∀ a b, r • eStd g _ a b = 0 → ∀ v, u a (u b v) = u (a + b) v) ∧
      ∀ a, (r * m) • a = 0 → u a (SecM.ofSec P.A s₀) = SecM.ofSec P.A s₀ := by
  obtain ⟨ρ, hρ, -⟩ := GlobalTheory.thetaGrp_acts_linearly hL.globalFns S P N (baseOver S)
  obtain ⟨h0, hsm⟩ := pt_nsmul pt hadd
  have hodd : Odd N := hN ▸ hm.pow
  have tors : ∀ a, pt (r • a) ^ N = 1 := fun a => by rw [← hsm, smul_smul, mul_comm N r, nsmul_self, h0]
  have act : ∀ a v, IsActOf P.A P.L N (U a) (SecM.toSec P.A v) (SecM.toSec P.A (ρ (U a) v)) := fun a v =>
    (hρ _ _ _).2 rfl
  have weil : ∀ a b, WeilIs P.A P.L N (pt (r • a)) (pt (r • b))
      (ze ^ (r * N * (r • eStd g (r * N) a b).val)) := fun a b => by
    have h₁ := hw a (r • b)
    rw [eStd_nsmul] at h₁
    have h₂ := (hL.weil S P N (baseOver S)).2.2.2 r (pt a) (pt (r • b))
      (ze ^ (r * N * (r • eStd g (r * N) a b).val)) (by rw [mul_comm]; exact hu)
      (by rw [← hsm, mul_comm N r, nsmul_self, h0]) (tors b)
    rw [hsm r a]
    refine h₂.1 ?_
    rw [← Nat.cast_mul, mul_comm N r]
    exact h₁
  have key : ∀ a b v, ρ (U a) (ρ (U b) v) = (show Γ((baseOver S).left, ⊤) from
      ze.val ^ (r * N * (r • eStd g (r * N) a b).val * ((N + 1) / 2))) • ρ (U (a + b)) v := fun a b v => by
    have := act_act hL.globalFns P.isAb P.isLB hodd (tors b) (hU a) (hU b)
      (by rw [← hadd, ← smul_add, add_comm]; exact hU (a + b)) (weil a b) (act b v) (act a _) (act (a + b) v)
    refine this.trans (congrArg (· • _) ?_)
    rw [pow_mul ze.val]
    exact (Units.val_pow_eq_pow_val _ _).trans (congrArg (· ^ _) (Units.val_pow_eq_pow_val _ _))
  refine ⟨fun a => (ρ (U a)).toLinearMap, fun a => hρ _, fun a ha v => ?_, fun a b => ⟨_, key a b⟩,
    fun a b h v => ?_, fun a ha => (hρ _ _ _).1 ?_⟩
  · have h₁ : SymLift P.A P.L N N 1 (U a) := by
      have := hU a
      rwa [ha, h0] at this
    have := act_act hL.globalFns P.isAb P.isLB hodd (one_pow N) h₁ h₁ (by rw [_root_.mul_one]; exact h₁)
      ((hL.weil S P N (baseOver S)).2.2.1 1 (one_pow N)) (act a v) (act a _) (act a v)
    rw [one_pow, Units.val_one, one_smul] at this
    exact (ρ (U a)).injective this
  · refine (key a b v).trans ?_
    rw [h, ZMod.val_zero, mul_zero, zero_mul, pow_zero]
    exact one_smul _ _
  · obtain ⟨ν, hν⟩ := GlobalTheory.exists_gen_negLB hL.globalFns S P 1 (baseOver S)
    exact isActOf_self hL.globalFns P.isAb P.isLB hν hodd hα hs
      (by rw [← hsm, smul_smul, mul_comm m r, ha, h0]) (tors a) (hU a)

end GlobalTheory.ThetaReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOrderActionDescentFieldExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ArcPull PsiEvenPull

theorem exists_oAct_of_field_extension : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oB : D.P.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oB.act a).left) → ∃ oa : D.OAct O, oa.onB = oB := by
  intro hG K₀ K _ _ i D D' hD O _ _ _ _ oB oa' hx ho
  have gp := pull_grp hD
  have hφ : Function.Injective i := i.injective
  have := FieldBaseChange.flat_spMap i
  have := FieldBaseChange.surjective_spMap i
  have : Epi (spMap i) := Flat.epi_of_flat_of_surjective _
  have cl : ∀ (a : O) y, D.c (a • y) = D.c y ≫ oB.act a := fun a y => by
    obtain ⟨y, rfl⟩ := hD.xe.surjective y
    refine Over.OverMorphism.ext ((cancel_epi (spMap i)).1 ?_)
    have e₁ := hD.c_pr (a • y)
    have e₂ := hD.c_pr y
    rw [oa'.c_lin, Over.comp_left, Category.assoc, hx] at e₁
    refine e₁.symm.trans ((congrArg (_ ≫ ·) (ho a)).trans ?_)
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₂).trans (Category.assoc _ _ _))
  refine ⟨⟨oB, cl, fun a u hu u₀ y y' => ?_⟩, rfl⟩
  obtain ⟨y, rfl⟩ := hD.xe.surjective y
  obtain ⟨y', rfl⟩ := hD.xe.surjective y'
  refine corr_of_val_field_extension _ _ (fracMap hφ) _ _ D.P.isLB _ _ _ _ _ _ _ _ fun z J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
  have := oa'.onB.hom a
  have := oa'.onB.hom (star a)
  have := oB.hom a
  have := oB.hom (star a)
  obtain ⟨u', hu', h₀⟩ := exists_ros hG D'.P.isAb D'.P.isLB _ _ (oa'.onB.rosati a)
  have sq := fracMap_sq hφ
  have hh : (TK K).hom ≫ spMap i = genMap hφ ≫ (TK K₀).hom := (Category.id_comp _).symm.trans sq
  have e := val_corr hJ' (oa'.tau_bal a u' hu' h₀ y y') (𝟙 (TK K).left)
  have v := ros_val hG gp D'.P.isAb D.P.isLB D'.P.isLB hD.w_gen (ho a) (ho (star a)) ⟨hu, u₀⟩ ⟨hu', h₀⟩
    (cP D' (TK K) y) (cP D' (TK K) y') (genMap hφ ≫ D.pt2 (hD.xe y) (hD.xe y'))
    ((cPoint_proj hD _ hh y).trans (by
      rw [Category.assoc, DegPre.pt2, ← Over.comp_left, lift_fst]; rfl))
    ((cPoint_proj hD _ hh y').trans (by
      rw [Category.assoc, DegPre.pt2, ← Over.comp_left, lift_snd]; rfl)) hJ hJ'
  have cs : ∀ (a : O) y, cP D' (TK K) y ≫ oa'.onB.act a = cP D' (TK K) (a • y) := fun a y => by
    rw [cP, cP, oa'.c_lin, Category.assoc]
  rw [cs, cs, ← cPoint_add, ← cPoint_add] at v
  rw [val_mul hJ', val_pull hJ'] at e
  erw [Category.id_comp] at e
  beta_reduce at e
  show val _ (genMap hφ) z J = val _ (genMap hφ) z J
  rw [val_mul hJ, val_pull hJ, v]
  beta_reduce
  rw [← hx, ← hx, tau_val hD _ _ sq hJ hJ', tau_val hD _ _ sq hJ hJ']
  simp only [Category.id_comp]
  have e' := congrArg Additive.ofMul e
  apply Additive.ofMul.injective
  have c₀ : ∀ x, (cP D' (TK K) x).left = D'.xK x := fun _ => rfl
  have c₁ : val₂ u' z J' (cP D' (TK K) y) (cP D' (TK K) y') = val u' (D'.pt2 y y') z J' := rfl
  simp only [ofMul_mul, ofMul_inv, c₀, c₁] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSecOfRefine
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gs_sec_compat {Y Z : Scheme.{0}} {M : LB Y} (φ : M.Sec) (r : Z ⟶ Y) (z : Z) {l l' : M.ι}
    (hl : r z ∈ M.U l) (hl' : r z ∈ M.U l') :
    gs r z (M.U l) (φ.f l) = (gm r z (M.U l ⊓ M.U l') (M.g l l')).val * gs r z (M.U l') (φ.f l') := by
  have hm : r z ∈ M.U l ⊓ M.U l' := ⟨hl, hl'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (φ.compat l l')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem exists_sec_of_refine : ∀ (Y : Scheme.{0}) (M A : LB Y), M.IsLB → A.IsLB →
    ∀ (c : ChartPull M A (𝟙 Y)) (φ : M.Sec), ∃ s : A.Sec, ∀ (l : M.ι) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
      r z ∈ M.U l → gs r z (M.U l) (φ.f l) = gs r z (A.U (c.idx l)) (s.f (c.idx l)) := by
  intro Y M A hM hA c φ
  have cle : ∀ l (y : Y), y ∈ M.U l → y ∈ A.U (c.idx l) := fun l y hy => c.le l hy
  have glue : ∀ i : A.ι, ∃ a : Γ(Y, A.U i), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (l : M.ι),
      r z ∈ A.U i → r z ∈ M.U l →
      gs r z _ a = (gm r z (A.U i ⊓ A.U (c.idx l)) (A.g i (c.idx l))).val * gs r z (M.U l) (φ.f l) := by
    intro i
    let W : M.ι → Y.Opens := fun l => A.U i ⊓ M.U l
    have hW : ∀ l, W l ≤ A.U i ⊓ A.U (c.idx l) := fun l y hy => ⟨hy.1, cle l y hy.2⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ l, Γ(Y, W l), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) l, r z ∈ W l →
        gs r z (W l) (u l) =
          (gm r z (A.U i ⊓ A.U (c.idx l)) (A.g i (c.idx l))).val * gs r z (M.U l) (φ.f l) :=
      ⟨fun l => (Y.presheaf.map (homOfLE (hW l)).op).hom (A.g i (c.idx l)).val *
          (Y.presheaf.map (homOfLE (inf_le_right : W l ≤ M.U l)).op).hom (φ.f l), fun Z r z l hz =>
        (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·) ((gs_res r z _ hz _).trans (gs_unit r z _ (hW l hz) _))
          (gs_res r z _ hz _))⟩
    obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' W (A.U i)
      (fun l => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨l, hl⟩ := exists_chart hM y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨l, hy, hl⟩) u
      (fun l l' => fn_ext (V := W l ⊓ W l') fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y l hy.1, hu _ _ y l' hy.2, gs_sec_compat φ (𝟙 Y) y hy.1.2 hy.2.2, c.g y l l' hy.1.2 hy.2.2,
          ← _root_.mul_assoc, ← Units.val_mul,
          gm_cocycle hA (𝟙 Y) y hy.1.1 (cle l y hy.1.2) (cle l' y hy.2.2)])
    refine ⟨a, fun Z r z l h₁ h₂ => ?_⟩
    have hz : r z ∈ W l := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz a).symm.trans ((congrArg (gs r z (W l)) (ha l)).trans (hu Z r z l hz))
  choose a ha using glue
  refine ⟨⟨a, fun j j' => fn_ext fun y hy => ?_⟩, fun l Z r z hl => ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hM y
    refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
      (gs_unit (𝟙 Y) y _ hy _) (gs_res (𝟙 Y) y _ hy _))).symm)
    rw [ha j _ (𝟙 Y) y l hy.1 hl, ha j' _ (𝟙 Y) y l hy.2 hl,
      ← gm_cocycle hA (𝟙 Y) y hy.1 hy.2 (cle l y hl), Units.val_mul, _root_.mul_assoc]
  · have m := cle l _ hl
    refine Eq.symm ((ha _ Z r z l m hl).trans ?_)
    rw [gm_self hA r z m, Units.val_one, _root_.one_mul]

end GlobalTheory.ZH.UFib
end
end

