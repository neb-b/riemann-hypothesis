module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermEqZeroOfThickenings
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAbelianTorusGeneratorsAtPlace
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0034

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartCokernelLengthLeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianPart_cokernel_length_le : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp), H.P = 0 → H.PL = 0 → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (rm : ℕ), (∀ τ ∈ Emb (O := O) w.bar, eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm) → ∃ cw : NNReal, HasLen v O (htCoker H w.e w.bar) cw ∧ (v (algebraMap O C (p : O)) : ℝ) ^ (((w.n : ℝ) * rm) / ((p : ℝ) - 1)) ≤ cw := by
  first | exact @GlobalTheory.ChF.abelian_coker_bound | exact GlobalTheory.ChF.abelian_coker_bound | (intros; apply GlobalTheory.ChF.abelian_coker_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CommGroupCoboundaryRelationIdentity
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AddCurve

namespace GlobalTheory.TangentCob

section Schemes
variable {X Y : Scheme.{0}}

theorem top_le_stalk_iff (f : Y ⟶ X) (y : Y) (U : X.Opens) :
    ⊤ ≤ (Y.fromSpecStalk y ≫ f) ⁻¹ᵁ U ↔ f y ∈ U := by
  refine (top_le_iff_cpt (A := Y.presheaf.stalk y) _ U).trans ?_
  rw [Scheme.Hom.comp_apply,
    show Y.fromSpecStalk y (cpt (Y.presheaf.stalk y)) = y from Scheme.fromSpecStalk_closedPoint]

theorem valR_stalk (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    valR (A := Y.presheaf.stalk y) (Y.fromSpecStalk y ≫ f) U a = gs f y U a := by
  rw [gs_eq f y U h]
  exact (GlobalTheory.HolHom.valR_comp (A := Y.presheaf.stalk y) _ f U a).trans
    (GlobalTheory.FormalValue.valR_fromSpecStalk y (f ⁻¹ᵁ U) h _)

theorem exists_unit (p : Y ⟶ X) (e : Γ(Y, ⊤)) (he : e * e = 0) (U : X.Opens) (a : Γ(X, U)) :
    ∃ u : Γ(Y, p ⁻¹ᵁ U)ˣ, ∀ y, p y ∈ U →
      (gm (𝟙 Y) y (p ⁻¹ᵁ U) u).val = 1 + gs (𝟙 Y) y ⊤ e * gs p y U a := by
  let e' : Γ(Y, p ⁻¹ᵁ U) := (Y.presheaf.map (homOfLE (le_top : p ⁻¹ᵁ U ≤ ⊤)).op).hom e
  have he' : e' * e' = 0 := by rw [← map_mul, he, map_zero]
  let b : Γ(Y, p ⁻¹ᵁ U) := (p.app U).hom a
  refine ⟨⟨1 + e' * b, 1 - e' * b, by linear_combination (-(b * b)) * he', by linear_combination (-(b * b)) * he'⟩,
    fun y hy => ?_⟩
  have hy' : (𝟙 Y : Y ⟶ Y) y ∈ p ⁻¹ᵁ U := hy
  rw [← gs_unit _ y _ hy']
  show gs (𝟙 Y) y (p ⁻¹ᵁ U) (1 + e' * b) = _
  rw [gs_add _ y _ hy', gs_mul _ y _ hy', gs_res _ y _ hy', gs_pull (𝟙 Y) p y U hy, Category.id_comp,
    gs_eq _ y _ hy', map_one, map_one]

theorem commGroup_coboundary_relation_identity {G : Type} [CommGroup G] {a b c d f g u v : G} (h : a * v = b * u) (h₁ : c * d = f)
    (h₂ : g * a = f) : g * u = c ^ (1 : ℤ) * b ^ (-1 : ℤ) * (d * v) := by
  rw [zpow_one, zpow_neg, zpow_one, _root_.mul_mul_mul_comm, h₁, ← h₂, _root_.mul_assoc, _root_.mul_left_comm a,
    h, inv_mul_cancel_left]

theorem exists_isGen (L : LB X) (hL : L.IsLB) (m p : Y ⟶ X) (e : Γ(Y, ⊤)) (he : e * e = 0) (H : ∀ j, Γ(X, L.U j))
    (hmp : ∀ (y : Y) (U : X.Opens), p y ∈ U → m y ∈ U)
    (h : ∀ (y : Y) (j j' : L.ι), p y ∈ L.U j → p y ∈ L.U j' → gs m y (L.U j ⊓ L.U j') (L.g j j').val =
      gs p y (L.U j ⊓ L.U j') (L.g j j').val *
        (1 + gs (𝟙 Y) y ⊤ e * (gs p y (L.U j) (H j) - gs p y (L.U j') (H j')))) :
    ∃ c : LB.Gen (LB.LinComb L (K := Fin 2) ![m, p] ![1, -1]), c.IsGen := by
  choose u hu using fun j => exists_unit p e he (L.U j) (H j)
  have h0 : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![m, p] j → m y ∈ L.U (j 0) :=
    fun j y hy => LB.wchart_le L ![m, p] j 0 hy
  have h1 : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![m, p] j → p y ∈ L.U (j 1) :=
    fun j y hy => LB.wchart_le L ![m, p] j 1 hy
  let s : ∀ j : Fin 2 → L.ι, Γ(Y, LB.wchart L ![m, p] j)ˣ := fun j =>
    res (show LB.wchart L ![m, p] j ≤ m ⁻¹ᵁ (L.U (j 0) ⊓ L.U (j 1)) from
      fun y hy => ⟨h0 j y hy, hmp y _ (h1 j y hy)⟩) (pullU m _ (L.g (j 0) (j 1))) *
    res (show LB.wchart L ![m, p] j ≤ p ⁻¹ᵁ L.U (j 1) from fun y hy => h1 j y hy) (u (j 1))
  have hs : ∀ (j : Fin 2 → L.ι) (y : Y), y ∈ LB.wchart L ![m, p] j → gm (𝟙 Y) y _ (s j) =
      gm m y _ (L.g (j 0) (j 1)) * gm (𝟙 Y) y _ (u (j 1)) := fun j y hy => by
    have hy' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L ![m, p] j := hy
    rw [map_mul, gm_res _ y _ hy', gm_res _ y _ hy',
      gm_pull (𝟙 Y) m y (L.U (j 0) ⊓ L.U (j 1)) ⟨h0 j y hy, hmp y _ (h1 j y hy)⟩, Category.id_comp]
  refine ⟨⟨s⟩, fun j j' => unit_ext fun y hy => ?_⟩
  have hy' : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L ![m, p] j ⊓ LB.wchart L ![m, p] j' := hy
  refine ((gm_res _ y _ hy' _).trans (hs j y hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L ![m, p] ![1, -1] (𝟙 Y) y j j' hy.1 hy.2) ((gm_res _ y _ hy' _).trans (hs j' y hy.2)))).symm)
  have a0 := h0 j y hy.1
  have a1 := h1 j y hy.1
  have b0 := h0 j' y hy.2
  have b1 := h1 j' y hy.2
  have key : gm m y _ (L.g (j 1) (j' 1)) * gm (𝟙 Y) y _ (u (j' 1)) =
      gm p y _ (L.g (j 1) (j' 1)) * gm (𝟙 Y) y _ (u (j 1)) := by
    apply Units.ext
    have hee : gs (𝟙 Y) y ⊤ e * gs (𝟙 Y) y ⊤ e = 0 := by
      rw [← gs_mul (𝟙 Y) y ⊤ trivial, he, gs_eq (𝟙 Y) y ⊤ trivial, map_zero, map_zero]
    rw [Units.val_mul, Units.val_mul, hu _ y a1, hu _ y b1, ← gs_unit m y (L.U (j 1) ⊓ L.U (j' 1)) ⟨hmp y _ a1, hmp y _ b1⟩,
      ← gs_unit p y (L.U (j 1) ⊓ L.U (j' 1)) ⟨a1, b1⟩, h y _ _ a1 b1]
    linear_combination (gs p y (L.U (j 1) ⊓ L.U (j' 1)) (L.g (j 1) (j' 1)).val *
      (gs p y (L.U (j 1)) (H (j 1)) - gs p y (L.U (j' 1)) (H (j' 1))) * gs p y (L.U (j' 1)) (H (j' 1))) * hee
  have c1 := gm_cocycle hL m y a0 b0 (hmp y _ b1)
  have c2 := gm_cocycle hL m y a0 (hmp y _ a1) (hmp y _ b1)
  rw [Fin.prod_univ_two]
  exact commGroup_coboundary_relation_identity key c1 c2

end Schemes

variable {k : Type} [CommRing k] {B : Over (Sp k)}

theorem exists_alg (D : Type) [CommRing D] [Algebra k D] {S : Type} [CommRing S] (r : Sp S ⟶ (algOver k D ⊗ B).left) :
    ∃ (_ : Algebra k S) (φ : D →ₐ[k] S) (r' : algOver k S ⟶ algOver k D ⊗ B), r'.left = r ∧
      r' ≫ fst _ _ = algOverHom φ ∧ ∀ d : D, φ d =
        valR (r ≫ (fst (algOver k D) B).left) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of D)).inv.hom d) := by
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (R := CommRingCat.of D) (S := CommRingCat.of S) (r ≫ (fst (algOver k D) B).left)
  letI : Algebra k S := (ψ.hom.comp (algebraMap k D)).toAlgebra
  refine ⟨this, ⟨ψ.hom, fun _ => rfl⟩, Over.homMk r ?_, rfl, Over.OverMorphism.ext hψ.symm, fun d => ?_⟩
  · rw [← Over.w (fst (algOver k D) B), ← Category.assoc]
    erw [← hψ]
    exact (Spec.map_comp _ _).symm
  · erw [← hψ]
    have := GlobalTheory.HolHom.valR_spMap ψ.hom (𝟙 (Sp D)) ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of D)).inv.hom d)
    rw [Category.comp_id, GlobalTheory.HolHom.valR_eq (𝟙 (Sp D)) ⊤ le_top] at this
    refine Eq.trans ?_ this.symm
    refine congrArg ψ.hom ?_
    simp [GlobalTheory.HolHom.evalHom, Scheme.Hom.appLE]

end GlobalTheory.TangentCob

namespace GlobalTheory
open TangentCob

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsAbelianTorusGeneratorsAtPlaceStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelian_torus_generators_at_place : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (α : ℤ_[p] ⊗[ℤ] OE) (b : Module.Basis (Fin w.n) ℤ_[p] w.Ow), (∀ k, (b k : ℤ_[p] ⊗[ℤ] OE) = w.e * α ^ (k : ℕ)) → ∀ (rp rm : ℕ) (W : Fin w.n → Fin rp → Fin d → O), (∀ j, EigB ρG ((t j : Emb (O := O) w.e) : OE →+* O) (W j)) → (∀ τ ∈ Emb (O := O) w.bar, eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm) → ∃ (h : ℕ) (ψ : Fin h → Fin d → O), h ≤ rp + rm ∧ (∀ l j, Pdiv.ChartF.res (W j) (ψ l) ∈ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W j) (s k))) ∧ ∃ f : htCoker H w.e w.bar →ₗ[O] ((LinearMap.range (LinearMap.pi fun y : Fin w.n × Fin rp => (LinearMap.proj y.2).comp (Pdiv.ChartF.res (W y.1))) : Submodule O (Fin w.n × Fin rp → O)) ⧸ (Submodule.span O (Set.range fun q : Fin w.n × Fin h => fun y : Fin w.n × Fin rp => tauExt ((t y.1 : Emb (O := O) w.e) : OE →+* O) α ^ (q.1 : ℕ) * Pdiv.ChartF.res (W y.1) (ψ q.2) y.2)).comap (Submodule.subtype _)), Function.Surjective f := by
  first | exact @GlobalTheory.ChF.GenAtPlace.exists_generators | exact GlobalTheory.ChF.GenAtPlace.exists_generators | (intros; apply GlobalTheory.ChF.GenAtPlace.exists_generators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalTorusCharacterLiftToLaw
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF.Lift

section Subst
variable {R : Type} [CommRing R] {m n d e : ℕ}

private theorem hasSub (a : Fin m → Fin d → PS R n e) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) :
    MvPowerSeries.HasSubst (fun q : Fin m × Fin d => a q.1 q.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => ha q.1 q.2)

private noncomputable def subA (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) : PS R m d →ₐ[R] PS R n e :=
  MvPowerSeries.substAlgHom (hasSub a ha)

private theorem subA_apply (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d) : subA a ha f = sub a f := by
  unfold subA sub
  rw [MvPowerSeries.coe_substAlgHom]

private theorem sub_sub {n' e' : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (b : Fin n → Fin e → PS R n' e')
    (hb : ∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) (f : PS R m d) :
    sub b (sub a f) = sub (fun i j => sub b (a i j)) f := by
  unfold sub
  rw [MvPowerSeries.subst_comp_subst_apply (hasSub a ha) (hasSub b hb)]

private theorem sub_X (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (i : Fin m) (j : Fin d) :
    sub a (MvPowerSeries.X (i, j)) = a i j := by
  unfold sub
  rw [MvPowerSeries.subst_X (hasSub a ha)]

private theorem const_sub (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSub a ha) (fun q => ha q.1 q.2) hf

private theorem ev_eq_sub (a : Fin m → Pt R n d) (f : PS R m d) : ev a f = sub a f := rfl

private theorem addOf_pt (F : Fin d → PS R 2 d) :
    addOf F (pt R (n := 2) d 0) (pt R (n := 2) d 1) = F := by
  funext i
  unfold addOf ev
  have h : (fun q : Fin 2 × Fin d => (![pt R (n := 2) d 0, pt R (n := 2) d 1] : Fin 2 → Pt R 2 d) q.1 q.2) =
      MvPowerSeries.X := by
    funext ⟨a, b⟩
    fin_cases a <;> rfl
  rw [h, MvPowerSeries.subst_self]
  rfl

private theorem const_one (φ : Fin d → PS R n e) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) :
    ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![φ] : Fin 1 → Fin d → PS R n e) i j) = 0 := by
  intro i j
  fin_cases i
  exact hφ j

private theorem const_pt (k : Fin n) : ∀ j, MvPowerSeries.constantCoeff (pt R d k j) = 0 := by
  intro j
  simp [pt]

private theorem isSum_comp (F : Fin d → PS R 2 d) (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0)
    (F' : Fin e → PS R 2 e) (hF' : ∀ j, MvPowerSeries.constantCoeff (F' j) = 0)
    (J : Fin e → PS R 1 d) (hJ : IsHomF F F' J) (φ φ' ψ : PS R 1 d →ₐ[R] R) (h : IsSum F φ φ' ψ) :
    IsSum F' (φ.comp (subA ![J] (const_one J hJ.1))) (φ'.comp (subA ![J] (const_one J hJ.1)))
      (ψ.comp (subA ![J] (const_one J hJ.1))) := by
  obtain ⟨Φ, h0, h1, h2⟩ := h
  have hb : ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff
      ((![fun i => ev (n := 2) ![pt R d 0] (J i), fun i => ev (n := 2) ![pt R d 1] (J i)] :
        Fin 2 → Fin e → PS R 2 d) i j) = 0 := by
    intro i j
    fin_cases i
    · exact const_sub _ (const_one _ (const_pt 0)) _ (hJ.1 j)
    · exact const_sub _ (const_one _ (const_pt 1)) _ (hJ.1 j)
  refine ⟨Φ.comp (subA _ hb), fun f => ?_, fun f => ?_, fun f => ?_⟩
  · simp only [AlgHom.comp_apply, subA_apply]
    rw [← h0, ev_eq_sub _ f, ev_eq_sub _ (sub _ f), sub_sub _ (const_one _ (const_pt 0)) _ hb,
      sub_sub _ (const_one J hJ.1) _ (const_one _ (const_pt 0))]
    congr 2
    funext i j
    fin_cases i
    exact sub_X _ hb 0 j
  · simp only [AlgHom.comp_apply, subA_apply]
    rw [← h1, ev_eq_sub _ f, ev_eq_sub _ (sub _ f), sub_sub _ (const_one _ (const_pt 1)) _ hb,
      sub_sub _ (const_one J hJ.1) _ (const_one _ (const_pt 1))]
    congr 2
    funext i j
    fin_cases i
    exact sub_X _ hb 1 j
  · simp only [AlgHom.comp_apply, subA_apply]
    rw [← h2, ev_eq_sub _ f, ev_eq_sub _ (sub _ f), sub_sub _ (const_one _ hF') _ hb,
      sub_sub _ (const_one J hJ.1) _ (const_one _ hF)]
    congr 2
    funext i j
    fin_cases i
    exact (hJ.2 j).symm

private theorem isCh_sum (F : Fin d → PS R 2 d) (u : PS R 1 d) (hu : IsCh F u) (φ φ' ψ : PS R 1 d →ₐ[R] R)
    (h : IsSum F φ φ' ψ) : ψ u = φ u * φ' u := by
  obtain ⟨Φ, h0, h1, h2⟩ := h
  have h3 := hu.2
  rw [addOf_pt] at h3
  rw [← h2, ← h0, ← h1, h3, map_mul]

end Subst

theorem exists_char_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d r : ℕ) (F : FGLaw O d), FH p F.F → ∀ (J : Fin d → PS O 1 r) (A' : Matrix (Fin r) (Fin d) O), IsHomF (gmF O r) F.F J → A' * lin J = 1 → ∀ i : Fin r, ∃ u : PS O 1 d, IsCh F.F u ∧ (lin J)ᵀ *ᵥ dl u = Pi.single i 1 := by
  intro p _ C _ _ _ v O _ _ hv _ _ d r F hFH J A' hJ hA i
  obtain ⟨⟨Gl, hGl⟩, hch, -⟩ := GlobalTheory.ChF.gmLaw_chars_mul O r
  obtain ⟨hchi, hdl⟩ := hch i
  have hFHG : FH p Gl.F := hGl ▸ _root_.GlobalTheory.ChF.fh_gmF p C v O hv r
  rw [← hGl] at hJ hchi
  obtain ⟨instF, hsF, h0F, hkF⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv d F
  obtain ⟨instG, hsG, h0G, hkG⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv r Gl
  obtain ⟨hchain, -, -⟩ := GlobalTheory.ChF.chain_rule_lin O r d J hJ.1
  have hsurj := GlobalTheory.ChF.sub_surjective_of_lin_leftInverse O d r J A' hJ.1 hA
  let j : (PS O 1 r →ₐ[O] O) →+ (PS O 1 d →ₐ[O] O) :=
    { toFun := fun φ => φ.comp (subA ![J] (const_one J hJ.1))
      map_zero' := by
        refine AlgHom.ext fun f => ?_
        rw [AlgHom.comp_apply, subA_apply, h0F, h0G, (hchain f).2]
      map_add' := fun φ φ' =>
        (hsF _ _ _).1 (isSum_comp Gl.F Gl.const F.F F.const J hJ φ φ' _ ((hsG _ _ _).2 rfl)) }
  have hj : ∀ φ f, j φ f = φ (sub ![J] f) := fun φ f => by
    show φ (subA ![J] (const_one J hJ.1) f) = _
    rw [subA_apply]
  have hinj : Function.Injective j := by
    intro φ φ' h
    refine AlgHom.ext fun g => ?_
    obtain ⟨f, rfl⟩ := hsurj g
    rw [← hj, ← hj, h]
  have hunit : IsUnit (1 + MvPowerSeries.X ((0 : Fin 1), i) : PS O 1 r) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, hchi.1]
    exact isUnit_one
  let χ : (PS O 1 r →ₐ[O] O) → Cˣ := fun φ => ((hunit.map φ).map (algebraMap O C)).unit
  have hχ : ∀ φ, (χ φ : C) = algebraMap O C (φ (1 + MvPowerSeries.X ((0 : Fin 1), i))) := fun φ => rfl
  have hχm : ∀ a b, χ (a + b) = χ a * χ b := by
    intro a b
    apply Units.ext
    rw [Units.val_mul, hχ, hχ, hχ, isCh_sum Gl.F _ hchi a b _ ((hsG _ _ _).2 rfl), map_mul]
  obtain ⟨κ, hκm, hκ0, hκj⟩ := GlobalTheory.CharExt.exists_extension _ _ j hinj C p (Fact.out : p.Prime).ne_zero χ hχm
  obtain ⟨u, hu, huκ⟩ := _root_.GlobalTheory.ChF.exists_isCh_of_tors p C v O hv d F hFH (fun φ => (κ φ : C))
    (by
      rintro φ φ' ψ ⟨k, hk⟩ ⟨k', hk'⟩ hs
      rw [(hsF _ _ _).1 hs, hκm φ φ' ⟨k, (hkF _ _).2 hk⟩ ⟨k', (hkF _ _).2 hk'⟩, Units.val_mul])
    (by
      intro φ hφ
      have : φ = 0 := AlgHom.ext fun f => by rw [hφ, h0F]
      show (κ φ : C) = 1
      rw [this, hκ0, Units.val_one])
  refine ⟨u, hu, ?_⟩
  have heq : sub ![J] u - (1 + MvPowerSeries.X ((0 : Fin 1), i)) = 0 := by
    apply (_root_.GlobalTheory.ChF.mem_span_mulF_of_killed_and_eq_zero_of_tors p C v O hv r Gl hFHG).2
    rintro φ ⟨k, hk⟩
    have h1 : p ^ k • φ = 0 := (hkG _ _).2 hk
    have h2 : p ^ k • j φ = 0 := by rw [← map_nsmul, h1, map_zero]
    have h3 := huκ (j φ) ⟨k, (hkF _ _).1 h2⟩
    rw [map_sub, sub_eq_zero]
    apply hv.hom_inj
    rw [← hj, h3, ← hχ, ← hκj φ ⟨k, h1⟩]
  rw [← (hchain u).1, sub_eq_zero.1 heq, hdl]

end GlobalTheory.ChF.Lift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsTorusExtensionPointsOfUniformisation
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem kills_mono {R : Type} [CommRing R] {I : Ideal R} {k l : ℕ} (hkl : k ≤ l) {S : Type} [CommRing S]
    [Algebra R S] (h : Kills I k S) : Kills I l S :=
  fun t ht => h t (Ideal.pow_le_pow_right (by omega) ht)

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I}
  {A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : Out.UnifPre I D A G) (S : Type) [CommRing S] [Algebra R S]

private theorem qRel_mono {k l : ℕ} (hkl : k ≤ l) {z y} (h : QRel (U.gt k) S z y) : QRel (U.gt l) S z y := by
  induction l, hkl using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact GlobalTheory.ChF.qRel_succ R I D A G U n S z y ih

private theorem iRel_mono {k l : ℕ} (hkl : k ≤ l) {χ z} (h : IRel (U.gt k) S χ z) : IRel (U.gt l) S χ z := by
  induction l, hkl using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact _root_.GlobalTheory.ChF.iRel_succ R I D A G U n S χ z ih

private def qFun (h : ∃ k, Kills I k S) (z : sp (R₀ := R) S ⟶ G) : sp (R₀ := R) S ⟶ D.toPre.P.A :=
  (((qRel_existsUnique_mul_nat R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).1 z).exists.choose

private theorem qFun_spec (h : ∃ k, Kills I k S) (z : sp (R₀ := R) S ⟶ G) :
    QRel (U.gt h.choose) S z (qFun U S h z) :=
  (((qRel_existsUnique_mul_nat R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).1 z).exists.choose_spec

private theorem qFun_eq (h : ∃ k, Kills I k S) {k : ℕ} {z y} (hq : QRel (U.gt k) S z y) : qFun U S h z = y :=
  (((qRel_existsUnique_mul_nat R I _ _ G (U.gt (max h.choose k))).1 S
    (kills_mono (le_max_left _ _) h.choose_spec)).1 z).unique
    (qRel_mono U S (le_max_left _ _) (qFun_spec U S h z)) (qRel_mono U S (le_max_right _ _) hq)

private def iFun (h : ∃ k, Kills I k S) (χ : Multiplicative D.toPre.X →* Sˣ) : sp (R₀ := R) S ⟶ G :=
  (((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).1 χ).exists.choose

private theorem iFun_spec (h : ∃ k, Kills I k S) (χ : Multiplicative D.toPre.X →* Sˣ) :
    IRel (U.gt h.choose) S χ (iFun U S h χ) :=
  (((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).1 χ).exists.choose_spec

private theorem iFun_eq (h : ∃ k, Kills I k S) {k : ℕ} {χ z} (hq : IRel (U.gt k) S χ z) : iFun U S h χ = z :=
  (((GlobalTheory.irel_points R I _ _ G (U.gt (max h.choose k))).1 S
    (kills_mono (le_max_left _ _) h.choose_spec)).1 χ).unique
    (iRel_mono U S (le_max_left _ _) (iFun_spec U S h χ)) (iRel_mono U S (le_max_right _ _) hq)

end

private def ptExt {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : Out.DegData R I}
    {A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : Out.UnifPre I D A G) : PtExt I G D.toPre.P.A D.toPre.X where
  q S _ _ h := MonoidHom.mk' (qFun U S h) fun z z' => qFun_eq U S h
    (((qRel_existsUnique_mul_nat R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).2 _ _ _ _
      (qFun_spec U S h z) (qFun_spec U S h z'))
  i S _ _ h := MonoidHom.mk' (iFun U S h) fun χ χ' => iFun_eq U S h
    (((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).2.1 _ _ _ _
      (iFun_spec U S h χ) (iFun_spec U S h χ'))
  q_nat S _ _ S' _ _ φ h h' z := qFun_eq U S' h'
    ((qRel_existsUnique_mul_nat R I _ h.choose G (U.gt h.choose)).2 S S' φ _ _ (qFun_spec U S h z))
  i_nat S _ _ S' _ _ φ h h' χ := iFun_eq U S' h'
    ((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).2 S S' φ _ _ (iFun_spec U S h χ))
  i_inj S _ _ h χ χ' e := by
    have e' : iFun U S h χ = iFun U S h χ' := e
    exact ((GlobalTheory.irel_points R I _ h.choose G (U.gt h.choose)).1 S h.choose_spec).2.2 _ _ _
      (iFun_spec U S h χ) (e' ▸ iFun_spec U S h χ')
  exact S _ _ h z := by
    have key := _root_.GlobalTheory.ChF.qRel_one_iff_exists_iRel R I _ h.choose G (U.gt h.choose) S h.choose_spec z
    constructor
    · intro e
      have e' : qFun U S h z = 1 := e
      obtain ⟨χ, hχ⟩ := key.1 (e' ▸ qFun_spec U S h z)
      exact ⟨χ, iFun_eq U S h hχ⟩
    · rintro ⟨χ, e⟩
      have e' : iFun U S h χ = z := e
      exact qFun_eq U S h (key.2 ⟨χ, e' ▸ iFun_spec U S h χ⟩)
  lift S _ _ h S' _ _ ρ σ h1 h2 y hy := by
    obtain ⟨z, hz, hq⟩ := GlobalTheory.T.abelianPart_lift_square_zero_unit_point R I _ h.choose G (U.gt h.choose) S h.choose_spec S' ρ σ h1 h2 y hy
    exact ⟨z, hz, qFun_eq U S h hq⟩

theorem exists_ptExt_of_unif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegData R I) (A : Out.PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : Out.UnifPre I D A G), ∃ E : PtExt I G D.toPre.P.A D.toPre.X, ∀ (OE : Type) [CommRing OE] [StarRing OE] [Module OE D.toPre.X] (io : Out.RingAct G OE) (oD : D.OAct OE) (oA : A.OAct OE), U.OLinear OE oD oA io → ∀ (a : OE) (S : Type) [CommRing S] [Algebra R S] (h : ∃ k, Kills I k S), (∀ z, E.q S h (z ≫ io.act a) = E.q S h z ≫ oD.onB.act a) ∧ ∀ χ χ', (∀ x, χ' (Multiplicative.ofAdd x) = χ (Multiplicative.ofAdd (star a • x))) → E.i S h χ ≫ io.act a = E.i S h χ' := by
  intro R _ _ I D A G _ _ U
  refine ⟨ptExt U, ?_⟩
  intro OE _ _ _ io oD oA hL a S _ _ h
  have key := qRel_iRel_equivariant R I D A G U OE io oD oA hL h.choose a S
  refine ⟨fun z => qFun_eq U S h (key.1 _ _ (qFun_spec U S h z)), fun χ χ' e => ?_⟩
  exact (iFun_eq U S h (key.2 _ _ _ e (iFun_spec U S h χ))).symm

end GlobalTheory.ChF
end
end

