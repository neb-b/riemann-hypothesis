module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2208
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2235
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2394
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.LinearRestriction.ResPullUVal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2301
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2238
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2333
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassicalPointNormPsiCoordinateExpNegQuadratic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TestAtPt

theorem norm_psi_coord : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (ev : R →+* OO p) (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε → ∀ (l : u.Lab) α s, PsiCoord D.toPre α s → ‖(ev s : PadicAlgCl p)‖ = Real.exp (-l.q (ε α)) := by
  intro o' Ω _ _ _ S ρ M U₀ EE FinalForm R _ _ _ G _ _ gm D A U p _ y₀ ev u ε hBC l α s hs
  obtain ⟨ev₀, _, hD, bc, -, -, hx, hev, -⟩ := hBC
  have hs' : PsiCoord D.toPre (hD.xe (ε α)) s := by rw [hx]; exact hs
  obtain ⟨w, hw⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD (ε α) s hs'
  obtain ⟨j, hj, hv⟩ := GlobalTheory.Poinc.valF_psi_of_psiCoord u.V u.D.toPre (ε α) _ hw
  have hq := l.q_eq (ε α) j hj
  rw [hv] at hq
  have unit_norm : ∀ v : u.Vˣ, ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (v : u.V))‖ = 1 := by
    intro v
    have h1 := (u.norm_le _).2 ⟨(v : u.V), rfl⟩
    have h2 := (u.norm_le _).2 ⟨((v⁻¹ : u.Vˣ) : u.V), rfl⟩
    have hm : algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (v : u.V)) *
        algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ((v⁻¹ : u.Vˣ) : u.V)) = 1 := by
      rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
    have hn := congrArg norm hm
    rw [norm_mul, norm_one] at hn
    nlinarith [norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) (v : u.V))),
      norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ((v⁻¹ : u.Vˣ) : u.V)))]
  rw [map_mul, map_mul, norm_mul, unit_norm w, _root_.one_mul, hev] at hq
  exact hq

end GlobalTheory.Poinc.TestAtPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreProductCoordinateIndependent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem specMap_contravariant_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp [spMap, ← Spec.map_comp]

theorem Near.closed_product_unique : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (Ω : Type) [Field Ω] (κ : ResidueField R →+* Ω) (s s' : Sp Ω ⟶ M.S) (a b c c' : Sp Ω ⟶ N.U.left) (x y : Over.mk s ⟶ G') (x' y' : Over.mk s' ⟶ G'), s ≫ M.π = spMap (κ.comp (residue R)) → s' ≫ M.π = spMap (κ.comp (residue R)) → N.Pt s a x.left → N.Pt s b y.left → N.Pt s c (x * y).left → N.Pt s' a x'.left → N.Pt s' b y'.left → N.Pt s' c' (x' * y').left → c = c' := by
  intro R _ _ _ M G' _ E N fU l hl1 hl2 hsurj Ω _ κ s s' a b c c' x y x' y' hs hs' ha hb hc ha' hb' hc'
  obtain ⟨Ω₁, _, io₁, ca, cb, hca, hcb, hcc⟩ := GlobalTheory.T.closedFibre_embedding_mul_image_eq_of_field_point R M G' E N fU l hl1 hl2 Ω κ s a b c x y hs ha hb hc
  obtain ⟨Ω₂, _, io₂, ca', cb', hca', hcb', hcc'⟩ :=
    GlobalTheory.T.closedFibre_embedding_mul_image_eq_of_field_point R M G' E N fU l hl1 hl2 Ω κ s' a b c' x' y' hs' ha' hb' hc'
  obtain ⟨Ω₃, _, j₁, j₂, hj⟩ := _root_.GlobalTheory.exists_common_field_extension Ω Ω₁ Ω₂ io₁ io₂
  have : Mono E.j := by haveI := E.imm; infer_instance

  let g₁ : Over.mk (spMap ((j₁.comp io₁).comp κ)) ⟶ Over.mk (spMap (io₁.comp κ)) :=
    Over.homMk (spMap j₁) (by simp only [Over.mk_hom, specMap_contravariant_comp_ringHom])
  let g₂ : Over.mk (spMap ((j₁.comp io₁).comp κ)) ⟶ Over.mk (spMap (io₂.comp κ)) :=
    Over.homMk (spMap j₂) (by simp only [Over.mk_hom, specMap_contravariant_comp_ringHom, hj])
  have hg₁ : g₁.left = spMap j₁ := rfl
  have hg₂ : g₂.left = spMap j₂ := rfl
  have e₁ : spMap j₁ ≫ spMap io₁ = spMap (j₁.comp io₁) := specMap_contravariant_comp_ringHom _ _
  have e₂ : spMap j₂ ≫ spMap io₂ = spMap (j₁.comp io₁) := by rw [specMap_contravariant_comp_ringHom, hj]
  have hA : g₁ ≫ ca = g₂ ≫ ca' := by
    ext1
    rw [← cancel_mono E.j]
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hca, hca']
    rw [hg₁, hg₂, reassoc_of% e₁, reassoc_of% e₂]
  have hB : g₁ ≫ cb = g₂ ≫ cb' := by
    ext1
    rw [← cancel_mono E.j]
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hcb, hcb']
    rw [hg₁, hg₂, reassoc_of% e₁, reassoc_of% e₂]
  have hC : g₁ ≫ (ca * cb) = g₂ ≫ (ca' * cb') := by
    rw [MonObj.comp_mul, MonObj.comp_mul, hA, hB]
  have hfU : spMap (j₁.comp io₁) ≫ c ≫ fU = spMap (j₁.comp io₁) ≫ c' ≫ fU := by
    have := congrArg (fun g => g.left ≫ E.j) hC
    simp only [Over.comp_left, Over.homMk_left, Category.assoc, hcc, hcc'] at this
    rw [hg₁, hg₂, reassoc_of% e₁, reassoc_of% e₂] at this
    exact this

  have hlies : ∀ (t : Sp Ω ⟶ M.S) (d : Sp Ω ⟶ N.U.left) (z : Sp Ω ⟶ G'.left), t ≫ M.π = spMap (κ.comp (residue R)) →
      N.Pt t d z → d ≫ N.U.hom = spMap (κ.comp (residue R)) := by
    rintro t d z ht ⟨x₀, h₁, h₂, -⟩
    rw [← h₁, Category.assoc, pullback.condition, ← Category.assoc, h₂, ht]
  have hco : ∀ d : Sp Ω ⟶ N.U.left, d ≫ N.U.hom = spMap (κ.comp (residue R)) →
      (spMap (j₁.comp io₁) ≫ d) ≫ N.U.hom = spMap (((j₁.comp io₁).comp κ).comp (residue R)) := by
    intro d hd
    rw [Category.assoc, hd, specMap_contravariant_comp_ringHom]
  have key := _root_.GlobalTheory.Mum.ClosedFibreInj.closedFibre_inj R M G' E N fU l hl1 hl2 hsurj Ω₃ ((j₁.comp io₁).comp κ) (spMap (j₁.comp io₁) ≫ c)
    (spMap (j₁.comp io₁) ≫ c') (hco c (hlies s c _ hs hc)) (hco c' (hlies s' c' _ hs' hc'))
    (by simpa only [Category.assoc] using hfU)
  exact GlobalTheory.T.spMap_field_ext_cancel Ω Ω₃ (j₁.comp io₁) N.U.left c c' key

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreValueEqUnitMulLeadingFourierTerm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.RedVal

theorem commGroup_fourFactor_exponents_cancel_pow {M : Type} [CommGroup M] (a b c d : M) (k : ℕ) :
    a ^ ((k:ℤ)-1) * b ^ (1:ℤ) * c ^ (-1:ℤ) * d ^ (1:ℤ) * (b ^ (-1:ℤ) * c ^ (1:ℤ) * a ^ (1:ℤ) * d ^ (-1:ℤ)) = a ^ k := by
  rw [zpow_sub_one]; simp only [zpow_neg, zpow_one, zpow_natCast]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow]
  abel

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem gs_pow' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) (n : ℕ) :
    gs f y U (a ^ n) = gs f y U a ^ n := by
  simp only [gs_eq f y U h, map_pow]

theorem gs_sum' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {Ix : Type} (s : Finset Ix)
    (a : Ix → Γ(X, U)) : gs f y U (∑ i ∈ s, a i) = ∑ i ∈ s, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs_eq f y U h, map_sum]

theorem sval_zero_of_van {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
    {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') {k : ℕ} (a : D'.X) (b : D.SecB k (hD.xe a))
    (b' : D'.SecB k a) (hb : PullB hD a b b') (I : Ideal R) (e : ℕ) (hv : VanMod I b e) {Z : Scheme.{0}}
    (r : Z ⟶ D'.P.A.left) (h' : Z ⟶ pullback D.P.A.hom (thick R I e))
    (hh : h' ≫ pullback.fst D.P.A.hom (thick R I e) = r ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))
    (z : Z) {J₁ : (Z ⟶ D'.P.A.left) → D'.P.L.ι} (hJ₁ : Good D'.P.L z J₁) : sval b' r z J₁ = 0 := by
  obtain ⟨J', hJ'⟩ := GlobalTheory.TorusCoord.exists_good' D.P.isLB z
  have E := hb Z r z (fun κ => J' ((r ≫ D'.famφB a κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
    (fun κ => J₁ (r ≫ D'.famφB a κ)) (fun κ => hJ' _) (fun κ => hJ₁ _)
  have h0 : gs (r ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) z
      (LB.wchart D.P.L (D.famφB (hD.xe a))
        (fun κ => J' ((r ≫ D'.famφB a κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ))))
      (b.f (fun κ => J' ((r ≫ D'.famφB a κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))) = 0 := by
    rw [← hh]
    by_cases hm : (h' ≫ pullback.fst D.P.A.hom (thick R I e)) z ∈ LB.wchart D.P.L (D.famφB (hD.xe a))
        (fun κ => J' ((r ≫ D'.famφB a κ) ≫ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)))
    · exact (gs_pull h' _ z _ hm _).symm.trans ((congrArg (gs h' z _) (hv _)).trans (gs_zero' _ _ _))
    · unfold gs
      exact dif_neg hm
  rw [h0] at E
  exact (Units.mul_right_eq_zero _).1 E.symm

theorem expand_eval {W : Type} [CommRing W] [IsDomain W] {I : Ideal W} {D : DegData W I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing W)))} {G : Over (Spec (CommRingCat.of W))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {k : ℕ} (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α)
    (hX : U.ExpandsAt 0 k σ f) {Z : Scheme.{0}} (g : Z ⟶ (thickObj W I 0 G).left) (z : Z)
    {J₁ : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι} {J₂ : (Z ⟶ G.left) → U.LG.L.ι}
    (hJ₁ : Good D.toPre.P.L z J₁) (hJ₂ : Good U.LG.L z J₂) (x : D.toPre.X)
    (hv : ∀ a, a ≠ x → sval (f a) (g ≫ (U.gt 0).pG.left) z J₁ = 0) :
    (gm g z _ ((U.w 0).s (fun _ => J₁ (g ≫ (U.gt 0).pG.left),
        fun _ => J₂ ((g ≫ (fstG I 0 G).left) ≫ 𝟙 G.left)))).val ^ k *
      sval σ (g ≫ (fstG I 0 G).left) z J₂ =
    sval (f x) (g ≫ (U.gt 0).pG.left) z J₁ * (val ((U.gt 0).t x) g z J₁).val := by
  obtain ⟨S, hS0, hS⟩ := hX
  let p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι) :=
    (fun _ => J₁ (g ≫ (U.gt 0).pG.left), fun _ => J₂ ((g ≫ (fstG I 0 G).left) ≫ 𝟙 G.left))
  let j₁ : Fin 1 → U.LG.L.ι := fun _ => J₂ ((g ≫ (fstG I 0 G).left) ≫ 𝟙 G.left)
  let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun a κ => J₁ ((g ≫ (U.gt 0).pG.left) ≫ D.toPre.famφB a κ)
  let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun a κ => J₁ (g ≫ D.toPre.Oφ (U.gt 0).pG a κ)
  have hcoh : CohAll D.toPre.P.L
      (Sum.elim (fun _ : PUnit.{1} => (U.gt 0).pG.left)
        (Sum.elim (fun a : S × Fin 4 => (U.gt 0).pG.left ≫ D.toPre.famφB a.1.1 a.2)
          (fun a : S × Fin 4 => D.toPre.Oφ (U.gt 0).pG a.1.1 a.2)))
      (Sum.elim (fun _ => p.1 PUnit.unit)
        (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
    have key : ∀ i, (Sum.elim (fun _ => p.1 PUnit.unit)
        (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) i =
        J₁ (g ≫ (Sum.elim (fun _ : PUnit.{1} => (U.gt 0).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt 0).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt 0).pG a.1.1 a.2))) i) := by
      rintro (_ | (_ | _))
      · rfl
      · simp only [Sum.elim_inl, Sum.elim_inr, jf, Category.assoc]
      · rfl
    intro a b e
    rw [key a, key b, e]
  have E := hS p j₁ jf jt rfl hcoh
  have hA : g z ∈ (LB.div (D.toPre.P.L.pull (U.gt 0).pG.left) (U.LG.L.pull (fstG I 0 G).left)).U p :=
    ⟨mem_pull.2 (hJ₁ (g ≫ (U.gt 0).pG.left)), mem_pull.2 (hJ₂ ((g ≫ (fstG I 0 G).left) ≫ 𝟙 G.left))⟩
  have hB : g z ∈ (fstG I 0 G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁ :=
    hJ₂.mem (fun _ : Fin 1 => 𝟙 G.left) (g ≫ (fstG I 0 G).left)
  have hC : ∀ a, g z ∈ (U.gt 0).pG.left ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB a) (jf a) := fun a =>
    hJ₁.mem (D.toPre.famφB a) (g ≫ (U.gt 0).pG.left)
  have hD' : ∀ a, g z ∈ LB.wchart D.toPre.P.L (D.toPre.Oφ (U.gt 0).pG a) (jt a) := fun a =>
    hJ₁.mem (D.toPre.Oφ (U.gt 0).pG a) g
  have hm : g z ∈ U.expW 0 p j₁ S jf jt := by
    refine ⟨⟨hA, hB⟩, ?_⟩
    exact Finset.inf_induction (p := fun V : (thickObj W I 0 G).left.Opens => g z ∈ V) trivial
      (fun _ h₁ _ h₂ => ⟨h₁, h₂⟩) (fun a _ => ⟨hC a, hD' a⟩)
  have E' := congrArg (gs g z (U.expW 0 p j₁ S jf jt)) E
  rw [gs_mul g z _ hm, gs_pow' g z _ hm, gs_unit g z _ hm, gm_res g z _ hm, gs_res g z _ hm, gs_sum' g z _ hm] at E'
  erw [gs_pull g (fstG I 0 G).left z _ hB] at E'
  refine E'.trans ?_
  have hterm : ∀ a : S, gs g z (U.expW 0 p j₁ S jf jt)
      (((thickObj W I 0 G).left.presheaf.map (homOfLE (U.expW_le_f 0 p j₁ jf jt a.2)).op).hom
        (((U.gt 0).pG.left.app _).hom ((f a.1).f (jf a.1))) *
        (res (U.expWeight_le_chart_weight 0 p j₁ jf jt a.2) (((U.gt 0).t a.1).s (jt a.1))).val) =
      sval (f a.1) (g ≫ (U.gt 0).pG.left) z J₁ * (val ((U.gt 0).t a.1) g z J₁).val := fun a => by
    rw [gs_mul g z _ hm, gs_res g z _ hm, gs_unit g z _ hm]
    erw [gm_res g z (U.expWeight_le_chart_weight 0 p j₁ jf jt a.2) hm, gs_pull g (U.gt 0).pG.left z _ (hC a.1)]
    rfl
  rw [Finset.sum_congr rfl (fun a _ => hterm a)]
  rw [Finset.sum_attach S (fun a => sval (f a) (g ≫ (U.gt 0).pG.left) z J₁ * (val ((U.gt 0).t a) g z J₁).val)]
  refine Finset.sum_eq_single x (fun b _ hb => by rw [hv b hb, zero_mul]) (fun hx => ?_)
  have h0 : sval (f x) (g ≫ (U.gt 0).pG.left) z J₁ = 0 :=
    (gs_pull g (U.gt 0).pG.left z _ (hC x) _).symm.trans ((congrArg (gs g z _) (hS0 x hx _)).trans (gs_zero' _ _ _))
  rw [h0, zero_mul]

theorem closedFibre_val : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (Y : Ext D.toPre) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (Z : Scheme.{0}) (p' : Z ⟶ T.G.left) (y : Z ⟶ Y.H.left) (g : Z ⟶ (thickObj W (maximalIdeal W) 0 T.G).left) (ξ' : GtPt T.D'.toPre (Over.mk (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0))), g ≫ (fstG (maximalIdeal W) 0 T.G).left = p' → GlobalTheory.TorusCoord.IsPointOf (T.U.gt 0) g ξ' → IsPullPt T.hD (𝟙 Z) (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)) ξ' → ∀ (k : ℕ) (u : Wˣ) (z : Z) J J', Good C.P.L.L z J → Good D.toPre.P.L z J' → ∃ c : (Z.presheaf.stalk z)ˣ, ∀ (α : D.toPre.X) (b : D.toPre.SecB k α) (τ : SecK D.toPre.P.L Y.q.left k) (F : IntFam (maximalIdeal R) D.toPre k) (σ : SecK C.P.L.L T.β k), IsTermOf Y b τ → F.Lead α b → T.ExpBy u σ F → sval σ p' z J = c.val * sval τ y z J' := by
  intro R _ _ _ _ D C Y W _ _ _ T Z p' y g ξ' hg hpt hpull k u z J J' hJ hJ'
  subst hg
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.TorusCoord.exists_good' T.D'.toPre.P.isLB z
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.TorusCoord.exists_good' T.U.LG.isLB z
  set Fm := T.hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf T.φ) with hFm
  set r := g ≫ (T.U.gt 0).pG.left with hr
  set p' := g ≫ (fstG (maximalIdeal W) 0 T.G).left with hp'
  let Gw : (Z ⟶ T.D'.toPre.P.A.left) → (Z.presheaf.stalk z)ˣ := fun f => gw T.hD.w f z (J' (f ≫ Fm)) (J₁ f)
  let W0 := gm g z _ ((T.U.w 0).s (fun _ => J₁ (g ≫ (T.U.gt 0).pG.left), fun _ => J₂ (p' ≫ 𝟙 T.G.left)))
  let uG : Γ(T.G.left, ⊤)ˣ := Units.map
    (T.G.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom).toMonoidHom u
  refine ⟨gm p' z ⊤ uG * gw T.ℓ p' z (J (p' ≫ T.β)) (J₂ p') ^ k * (W0 ^ k)⁻¹ * (Gw r ^ k)⁻¹, ?_⟩
  intro α b τ F σ hτ hL hE
  obtain ⟨x, rfl⟩ := T.hD.xe.surjective α
  obtain ⟨σ', f', hC, hP, hX⟩ := hE

  have hb' : ξ'.b.left = r := hpt.1
  have hq : (Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)).b.left = y ≫ Y.q.left := by
    have h := (Y.rep.1 (Over.mk (y ≫ Y.H.hom)) Y.H (Over.homMk y rfl) (𝟙 _)).1
    rw [Category.comp_id] at h
    exact h
  have hrF : r ≫ Fm = y ≫ Y.q.left := by
    have h := hpull.1
    rw [hb'] at h
    exact h.trans ((Category.id_comp _).trans hq)
  haveI := T.loc
  have hmm : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal W ^ (0 + 1)).comap T.φ := by
    simp only [zero_add, pow_one]
    intro a ha
    exact (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit T.φ a hu)
  let qm : R ⧸ maximalIdeal R ^ (0 + 1) →+* W ⧸ maximalIdeal W ^ (0 + 1) := Ideal.quotientMap _ T.φ hmm
  have hsq : thick W (maximalIdeal W) 0 ≫ specOf T.φ =
      Spec.map (CommRingCat.ofHom qm) ≫ thick R (maximalIdeal R) 0 := by
    simp only [thick, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have hcond : (r ≫ Fm) ≫ D.toPre.P.A.hom = (g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫
      Spec.map (CommRingCat.ofHom qm)) ≫ thick R (maximalIdeal R) 0 := by
    have e1 : Fm ≫ D.toPre.P.A.hom = T.D'.toPre.P.A.hom ≫ specOf T.φ := by
      rw [hFm, Category.assoc, pullback.condition, ← Category.assoc]
      congr 1
      exact Over.w T.hD.e.hom
    have e2 : r ≫ T.D'.toPre.P.A.hom =
        g ≫ (thickObj W (maximalIdeal W) 0 T.G).hom ≫ thick W (maximalIdeal W) 0 := by
      rw [hr, Category.assoc, Over.w (T.U.gt 0).pG]; rfl
    rw [Category.assoc, e1, ← Category.assoc, e2, Category.assoc, Category.assoc, hsq, Category.assoc,
      Category.assoc]
  let h' := pullback.lift (r ≫ Fm) _ hcond
  have hh : h' ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0) =
      r ≫ T.hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf T.φ) := pullback.lift_fst _ _ _
  have hvan : ∀ a, a ≠ x → sval (f' a) r z J₁ = 0 := fun a ha =>
    sval_zero_of_van T.hD a (F.f (T.hD.xe a)) (f' a) (hP a) (maximalIdeal R) 0
      (hL.2 _ (fun e => ha (T.hD.xe.injective e))) r h' hh z hJ₁
  have E1 := expand_eval T.U.toUnifPre σ' f' (hX 0) g z hJ₁ hJ₂ x hvan
  have E2 := hC Z p' z J J₂ hJ hJ₂
  have E3 := hτ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl) z J' hJ'
  have E4 := hP x Z r z (fun κ => J' ((r ≫ T.D'.toPre.famφB x κ) ≫ Fm)) (fun κ => J₁ (r ≫ T.D'.toPre.famφB x κ))
    (fun κ => hJ' _) (fun κ => hJ₁ _)
  rw [hL.1] at E4
  have E4' : sval b (y ≫ Y.q.left) z J' = (∏ κ, Gw (r ≫ T.D'.toPre.famφB x κ) ^ DegPre.famε k κ).val *
      sval (f' x) r z J₁ := by
    have hfam : ∀ κ, (r ≫ Fm) ≫ D.toPre.famφB (T.hD.xe x) κ = (r ≫ T.D'.toPre.famφB x κ) ≫ Fm := fun κ => by
      have e := GlobalTheory.ExpGTrans.famφB_pull T.hD x κ
      rw [← hFm] at e
      exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) e.symm).trans (Category.assoc _ _ _).symm)
    rw [sval_of b (y ≫ Y.q.left) z J' (fun κ => J' ((r ≫ T.D'.toPre.famφB x κ) ≫ Fm)) (fun κ => by
      rw [← hrF, hfam])]
    rw [← hrF]
    exact E4
  have E5 : val ((T.U.gt 0).t x) g z J₁ = val (ξ'.s x) (𝟙 Z) z J₁ := by
    rw [val_corr hJ₁ (hpt.2 x) (𝟙 Z), val_pull hJ₁, Category.id_comp]
  obtain ⟨hψ, hM⟩ := hpull.2 x
  have E6 := ReciprocityTheory.ChartRestriction.G.Out.OLinPf.ILin.val_maps _ T.hD.w _ DegPre.gtε _ (𝟙 Z) hψ _ _ hM (𝟙 Z) z J₁ J' hJ₁ hJ'
  have hO := (GlobalTheory.TorusCoord.comp_eq_of_left ξ'.b (𝟙 T.D'.toPre.P.A) (𝟙 Z) r (by rw [hb']; simp)).1 x
  have Gprod : (∏ κ, Gw (r ≫ T.D'.toPre.famφB x κ) ^ DegPre.famε k κ) *
      (∏ κ, Gw (𝟙 Z ≫ DegPre.gtφT _ _ ξ'.b x κ) ^ DegPre.gtε κ) = Gw r ^ k := by
    simp only [hO, Fin.prod_univ_four]
    simp only [DegPre.famφB, DegPre.Oφ, DegPre.famε, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Over.id_left, Category.comp_id]
    exact commGroup_fourFactor_exponents_cancel_pow _ _ _ _ k
  have E3' : sval τ y z J' = sval b (y ≫ Y.q.left) z J' *
      (val ((Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)).s (T.hD.xe x)) (𝟙 Z) z J').val := E3
  have E6' : val ((Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)).s (T.hD.xe x)) (𝟙 Z) z J' =
      (∏ κ, Gw (𝟙 Z ≫ DegPre.gtφT _ _ ξ'.b x κ) ^ DegPre.gtε κ) * val ((T.U.gt 0).t x) g z J₁ := by
    rw [E5]
    exact (congrArg (fun q => val ((Y.Φ (Over.mk (y ≫ Y.H.hom)) (Over.homMk y rfl)).s (T.hD.xe x)) q z J')
      (Category.comp_id (𝟙 Z)).symm).trans E6
  have hu : gs p' z ⊤ (scal T.G.hom u.val) = (gm p' z ⊤ uG).val := gs_unit p' z ⊤ trivial uG
  have hW : ((W0 ^ k)⁻¹ : (Z.presheaf.stalk z)ˣ).val * W0.val ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, Units.inv_mul]
  have hG : ((Gw r ^ k)⁻¹ : (Z.presheaf.stalk z)ˣ).val *
      ((∏ κ, Gw (r ≫ T.D'.toPre.famφB x κ) ^ DegPre.famε k κ).val *
        (∏ κ, Gw (𝟙 Z ≫ DegPre.gtφT _ _ ξ'.b x κ) ^ DegPre.gtε κ).val) = 1 := by
    rw [← Units.val_mul, Gprod, Units.inv_mul]
  rw [E2, hu, E3', E4', E6']
  simp only [Units.val_mul]
  linear_combination (-((gm p' z ⊤ uG).val * (gw T.ℓ p' z (J (p' ≫ T.β)) (J₂ p') ^ k).val *
      ((W0 ^ k)⁻¹ : (Z.presheaf.stalk z)ˣ).val * sval (f' x) r z J₁ * (val ((T.U.gt 0).t x) g z J₁).val)) * hG -
    ((gm p' z ⊤ uG).val * (gw T.ℓ p' z (J (p' ≫ T.β)) (J₂ p') ^ k).val * sval σ' p' z J₂) * hW +
    ((gm p' z ⊤ uG).val * (gw T.ℓ p' z (J (p' ≫ T.β)) (J₂ p') ^ k).val *
      ((W0 ^ k)⁻¹ : (Z.presheaf.stalk z)ˣ).val) * E1

end GlobalTheory.Mum.RedVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementCovers
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverCommon

theorem exists_cover_dominating_two : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V₁ V₂ : Cover Y), ∃ (V : Cover Y) (π₁ : V.X ⟶ V₁.X) (π₂ : V.X ⟶ V₂.X), π₁ ≫ V₁.p = V.p ∧ π₂ ≫ V₂.p = V.p ∧ Lies V V₁ π₁ ∧ Lies V V₂ π₂ := by
  intro F _ _ Y V₁ V₂
  obtain ⟨G, _, _, g, k, _, _, hk⟩ := _root_.GlobalTheory.Mean4O.CommonGen.exists_common F Y V₁ V₂
  obtain ⟨W, a, k', ha, hW, hk'⟩ := _root_.GlobalTheory.Mean4O.NormCoverFin.exists_cover F Y V₁ V₂ G g k hk
  obtain ⟨W', b, c, hb, hc, hW', hV⟩ := GlobalTheory.T.cover_dominating_pair F Y W V₂ k' hk'
  obtain ⟨e, he₁, he₂⟩ := hW
  obtain ⟨e', he₁', he₂'⟩ := hW'
  refine ⟨W', b ≫ a, c, by rw [Category.assoc, ha, hb], hc, ⟨e' ≫ e, ?_, ?_⟩, hV⟩
  · rw [Category.assoc, he₁, ← Category.assoc, he₁', Category.assoc]
  · rw [Category.assoc, he₂, he₂']

end GlobalTheory.CoverCommon
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedDominatingDvrClosedFibrePointIsTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem trait_at_closed_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), α ≫ G.hom = t ≫ M.gp → ∀ (W : G.left.Opens) (hWa : IsAffineOpen W) (x : G.left) (hx : x ∈ W), M.π (G.hom x) = closedPoint R → ∀ (F : Type) [Field F] (β : Γ(Y, α ⁻¹ᵁ W) →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V → ∀ (h1 : ∀ c, β ((α.app W).hom c) ∈ V), (∀ c, (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom c) = 0 → β ((α.app W).hom c) ∈ V.nonunits) → ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : IsLocalRing T) (lam : Γ(G.left, W) →+* T) (g : V →+* T) (φ : R →+* T), GlobalTheory.LN.CDvr T ∧ Function.Injective g ∧ IsLocalHom g ∧ (∀ c, g ⟨β ((α.app W).hom c), h1 c⟩ = lam c) ∧ Function.Injective φ ∧ IsLocalHom φ ∧ (Spec.map (CommRingCat.ofHom lam) ≫ hWa.fromSpec ≫ G.hom) ≫ M.π = spMap φ := by
  intro R _ _ _ _ M G Y α t hαt W hWa x hx hxc F _ β V hV h1 hnu
  haveI := hV
  let T := AdicCompletion (maximalIdeal V) V
  let g : V →+* T := algebraMap V T
  have hg : Function.Injective g := GlobalTheory.algebraMap_adicCompletion_injective_of_dvr V
  let f : G.left ⟶ Sp R := G.hom ≫ M.π
  let ρ : R →+* Γ(G.left, W) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ W le_top).hom
  let lam : Γ(G.left, W) →+* T := g.comp ((β.comp (α.app W).hom).codRestrict V h1)
  let φ : R →+* T := lam.comp ρ
  let ψ : FractionRing R →+* F :=
    β.comp ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫ t.appLE ⊤ (α ⁻¹ᵁ W) le_top).hom
  have key : ∀ r, β ((α.app W).hom (ρ r)) = ψ (algebraMap R (FractionRing R) r) := by
    intro r
    have hc : ∀ {a b : Y ⟶ Sp R} (_ : a = b), a.appLE ⊤ (α ⁻¹ᵁ W) le_top = b.appLE ⊤ (α ⁻¹ᵁ W) le_top := by
      rintro _ _ rfl; rfl
    have e1 : f.appLE ⊤ W le_top ≫ α.app W = (α ≫ f).appLE ⊤ (α ⁻¹ᵁ W) le_top := by
      rw [Scheme.Hom.app_eq_appLE]; exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    have e2 : α ≫ f = t ≫ jK R := by
      simp only [f]; rw [reassoc_of% hαt, M.gp_π]
    have e4 : (t ≫ jK R).appLE ⊤ (α ⁻¹ᵁ W) le_top = (jK R).appTop ≫ t.appLE ⊤ (α ⁻¹ᵁ W) le_top :=
      Scheme.Hom.comp_appLE t (jK R) ⊤ (α ⁻¹ᵁ W) le_top
    have e3 : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ W le_top ≫ α.app W =
        CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
          t.appLE ⊤ (α ⁻¹ᵁ W) le_top := by
      rw [e1, hc e2, e4, ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]
    change β (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ W le_top ≫ α.app W).hom r) =
      β ((CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv ≫
          t.appLE ⊤ (α ⁻¹ᵁ W) le_top).hom r)
    rw [e3]
  have hφi : Function.Injective φ := by
    intro a b hab
    have h2 : ((β.comp (α.app W).hom).codRestrict V h1) (ρ a) = ((β.comp (α.app W).hom).codRestrict V h1) (ρ b) := hg hab
    have h3 : β ((α.app W).hom (ρ a)) = β ((α.app W).hom (ρ b)) := congrArg Subtype.val h2
    rw [key, key] at h3
    exact IsFractionRing.injective R (FractionRing R) (ψ.injective h3)
  haveI : CharZero T := charZero_of_injective_ringHom hφi
  refine ⟨T, inferInstance, inferInstance, inferInstance, lam, g, φ,
    ⟨inferInstance, inferInstance, inferInstance⟩, hg, inferInstance, fun c => rfl, hφi, ?_, ?_⟩
  · constructor
    intro r hu
    by_contra hr
    have hrm : r ∈ maximalIdeal R := hr
    have hres : (G.left.residue x).hom ((G.left.presheaf.germ W x hx).hom (ρ r)) = 0 := by
      have hb : x ∉ G.left.basicOpen (ρ r) := by
        intro hxb
        have e := Scheme.basicOpen_appLE f W ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)
        rw [basicOpen_eq_of_affine (R := CommRingCat.of R) r] at e
        have h4 := ((show G.left.basicOpen (ρ r) = _ from e).le hxb).2
        have h7 : r ∉ PrimeSpectrum.asIdeal (f x) := h4
        have h6 : f x = closedPoint R := hxc
        rw [h6] at h7
        exact h7 hrm
      rw [Scheme.mem_basicOpen _ _ _ hx] at hb
      exact (IsLocalRing.residue_eq_zero_iff _).2 hb
    have h5 := hnu (ρ r) hres
    have h6 : ((β.comp (α.app W).hom).codRestrict V h1) (ρ r) ∈ maximalIdeal V :=
      (ValuationSubring.coe_mem_nonunits_iff (a := ⟨_, h1 (ρ r)⟩)).mp h5
    exact h6 (isUnit_of_map_unit g _ hu)
  · simp only [Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Sp R)) hWa le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp, ← Spec.map_comp]
    rfl

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeLineBundleIsoOfAppellHumbertAdjointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeLineBundle_iso_of_appellHumbert_adjoint : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (N : LB A.left), N.IsLB → Out.RelAmple A N → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ (f f' : A ⟶ A) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), IsMonHom f → IsMonHom f' → (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f') → (∀ z w, hermForm Hm (F z) w = hermForm Hm z (F' w)) → LBIso (cubeLB A ![fst A A ≫ f, snd A A] M) (cubeLB A ![fst A A, snd A A ≫ f'] M) := by
  first | (exact @GlobalTheory.AdjPullFrame.lbIso_cubeLB_of_adjoint) | (exact GlobalTheory.AdjPullFrame.lbIso_cubeLB_of_adjoint) | (intros; apply GlobalTheory.AdjPullFrame.lbIso_cubeLB_of_adjoint  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftHomAffinePairStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smoothLift_hom_affinePair : ∀ (D D' : Data) (Λ : Lift D) (Λ' : Lift D') (σ : D.R →+* D'.R) (φ : D'.X ⟶ D.X) (φ₀ : D'.X₀ ⟶ D.X₀) (hφ : φ ≫ D.s = D'.s ≫ spMap σ) (m : IsMor D.κ D.t D'.κ D'.t σ φ₀), φ₀ ≫ D.i = D'.i ≫ φ → ∀ p : Pair φ, ∃ θ : Λ.L.obj (Opposite.op p.1.2) ⟶ m.obj (Λ'.L.obj (Opposite.op p.1.1)), ∀ a, θ.φ (Λ.e (Opposite.op p.1.2) a) = Λ'.e (Opposite.op p.1.1) (secPull D.s D'.s p a) := by
  first | exact @GlobalTheory.PDForm.exists_lift_pair_hom | exact GlobalTheory.PDForm.exists_lift_pair_hom | (intros; apply GlobalTheory.PDForm.exists_lift_pair_hom <;> assumption)
end

