module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmTypeEigenMultiplicityOfDensePrimes
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2971
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2127
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.QkExtExistsG

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendsAbelianPartOfIsPullDeg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep

noncomputable section

namespace GlobalTheory.USep

def chartPullCompOf {X Y Y' : Scheme.{0}} (L : LB X) (g : Y ⟶ X) (h : Y' ⟶ Y) (k : Y' ⟶ X) (e : h ≫ g = k) :
    ChartPull (L.pull k) (L.pull g) h where
  idx J := J
  le J y hy := by
    subst e
    exact mem_pull.2 (by simpa using mem_pull.1 hy)
  g y J J' hj hj' := by
    subst e
    have hj₁ : h y ∈ (L.pull g).U J := mem_pull.2 (by simpa using mem_pull.1 hj)
    have hj₁' : h y ∈ (L.pull g).U J' := mem_pull.2 (by simpa using mem_pull.1 hj')
    refine (gm_pull_g L (h ≫ g) (𝟙 _) y J J' hj hj').trans ?_
    refine Eq.trans ?_ (gm_pull_g L g h y J J' hj₁ hj₁').symm
    rw [Category.id_comp]

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Spec.map_comp]

theorem descAt_of_isPullDeg : ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] (ρ : V →+* V₁)
    (Q : DegPre V) (D : DegPre V₁), IsPullDeg ρ Q D → D.P.g = Q.P.g ∧ ∀ (K : Type) [Field K] (ev : V₁ →+* K)
    (k₀ : Subfield K), DescAt D ev k₀ → DescAt Q (ev.comp ρ) k₀ := by
  intro V V₁ _ _ _ _ ρ Q D p
  have gp := pull_grp p
  refine ⟨H1.dim_unique _ D.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback gp.1 Q.P.smoothDim)
    (eSec D.P.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V₁)), ?_⟩
  intro K _ ev k₀ hd
  obtain ⟨B₀, i₁, i₂, M₀, c₀, B', i₃, π₁, π₀, w, c', hab, hM, h₁, h₀, hw, hc⟩ := hd
  have hL : LBIso (Q.P.L.pull (π₁ ≫ (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)))) (M₀.pull π₀) :=
    LBIso.trans (pull_isLB Q.P.isLB _) (pull_isLB D.P.isLB _) (pull_isLB hM _)
      (LBIso.chartPull (chartPullCompOf Q.P.L _ π₁ _ rfl) (chartPullPull D.P.L π₁)
        (LBIso.symm ⟨p.w, p.w_gen⟩)) ⟨w, hw⟩
  obtain ⟨w', hw'⟩ := hL
  refine ⟨B₀, i₁, i₂, M₀, fun a => c₀ (p.xe.symm a), B', i₃, π₁ ≫ (p.e.hom.left ≫ pullback.fst Q.P.A.hom (specOf ρ)),
    π₀, w', fun a => c' (p.xe.symm a), hab, hM, ?_, h₀, hw', fun a => ⟨(hc _).1, ?_, (hc _).2.2⟩⟩
  · exact (h₁.comp gp).congr (spMap_comp_ringHom ρ ev).symm rfl
  · have e₁ := (hc (p.xe.symm a)).2.1
    have e₂ := p.c_pr (p.xe.symm a)
    rw [AddEquiv.apply_symm_apply] at e₂
    rw [← Category.assoc, e₁, Category.assoc, e₂, ← Category.assoc, spMap_comp_ringHom]

end GlobalTheory.USep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantConditionSpreadsFromGeometricPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpreadOnePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

noncomputable def defect (H : Host E) (p q : ℕ) {R : Type} [CommRing R] {n : ℕ}
    (M : 𝓞 E →+* Module.End R (Fin n → R)) (r : R) (a : 𝓞 E) : R :=
  2 * r * LinearMap.trace R _ (M a) - ((p + q) * r * ((Algebra.intTrace ℤ (𝓞 E) a : ℤ) : R) +
    (p - q) * ((Algebra.intTrace ℤ (𝓞 E) (H.rt * a) : ℤ) : R))

theorem map_defect (H : Host E) (p q : ℕ) {R K : Type} [CommRing R] [CommRing K] {n : ℕ}
    (M : 𝓞 E →+* Module.End R (Fin n → R)) (r : R) (f : R →+* K) (M' : 𝓞 E →+* Module.End K (Fin n → K))
    (hM : ∀ a c, f ∘ M a c = M' a (f ∘ c)) (a : 𝓞 E) :
    f (defect H p q M r a) = 2 * f r * LinearMap.trace K _ (M' a) - ((p + q) * f r *
      ((Algebra.intTrace ℤ (𝓞 E) a : ℤ) : K) + (p - q) * ((Algebra.intTrace ℤ (𝓞 E) (H.rt * a) : ℤ) : K)) := by
  rw [defect, ← GlobalTheory.TraceSpread.map_trace f (M a) (M' a) (hM a)]
  simp only [map_sub, map_mul, map_add (f := _), map_natCast, map_intCast, map_ofNat]

theorem eq_zero_of_map (H : Host E) (p q : ℕ) {R : Type} [CommRing R] [IsDomain R] (hQ : ℚ →+* R) {n : ℕ}
    (M : 𝓞 E →+* Module.End R (Fin n → R))
    (hM : ∀ (K : Type) [Field K] (f : R →+* K), ∃ M' : 𝓞 E →+* Module.End K (Fin n → K), ∀ a c, f ∘ M a c = M' a (f ∘ c))
    (r : R) (hr : r ^ 2 = -(H.d : R)) (a : 𝓞 E) {K : Type} [Field K] (f : R →+* K)
    (hf : f (defect H p q M r a) = 0) : defect H p q M r a = 0 := by
  letI : Algebra ℚ R := hQ.toAlgebra
  let L := AlgebraicClosure (FractionRing R)
  let emb : R →+* L := (algebraMap (FractionRing R) L).comp (algebraMap R (FractionRing R))
  have hemb : Function.Injective emb :=
    (algebraMap (FractionRing R) L).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero L := ((RingHom.charZero_iff (emb.comp hQ).injective).1 inferInstance)
  obtain ⟨ML, hML⟩ := hM L emb
  have hs : emb r ∈ integralClosure ℚ L := by
    have h2 : (emb r) ^ 2 = algebraMap ℚ L (-(H.d : ℚ)) := by
      rw [← map_pow, hr]; simp
    exact IsIntegral.of_pow (by norm_num : 0 < 2) (h2 ▸ isIntegral_algebraMap)
  have hφ : ∀ φ : E →+* L, φ (a : E) ∈ integralClosure ℚ L := fun φ =>
    (Algebra.IsIntegral.isIntegral (R := ℚ) (a : E)).map φ.toRatAlgHom
  have hint : emb (defect H p q M r a) ∈ integralClosure ℚ L := by
    rw [map_defect H p q M r emb ML hML a, GlobalTheory.TraceSpread.trace_eq_sum]
    have h2 : (2 : L) ∈ integralClosure ℚ L := by
      simpa using Subalgebra.natCast_mem (integralClosure ℚ L) 2
    refine Subalgebra.sub_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ h2 hs)
      (Subalgebra.sum_mem _ fun φ _ => Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (hφ φ)))
      (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.add_mem _
        (Subalgebra.natCast_mem _ _) (Subalgebra.natCast_mem _ _)) hs) (Subalgebra.intCast_mem _ _))
        (Subalgebra.mul_mem _ (Subalgebra.sub_mem _ (Subalgebra.natCast_mem _ _) (Subalgebra.natCast_mem _ _))
          (Subalgebra.intCast_mem _ _)))
  have hR : IsIntegral ℚ (defect H p q M r a) :=
    (isIntegral_algHom_iff emb.toRatAlgHom hemb).1 hint
  by_contra h0
  exact (hR.isUnit h0).map f |>.ne_zero hf

end GlobalTheory.SpreadOnePoint

namespace GlobalTheory.SpreadOnePoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem detCond_iff_defect {H : Host E} (D : Datum H) {A : Type} [CommRing A] (G : Over (Sp A)) [GrpObj G]
    [IsCommMonObj G] (act : OAct (𝓞 E) G) (d : ℕ) (hd : SmoothOfRelativeDimension d G.hom) (r : A)
    (v : Fin d → (epsR (Localization.Away r) ⟶
      (Over.pullback (spMap (algebraMap A (Localization.Away r)))).obj G)) (hv : IsLieBasis v) :
    ∃ M : 𝓞 E →+* Module.End (Localization.Away r) (Fin d → Localization.Away r),
      (∀ (K : Type) [Field K] (f : Localization.Away r →+* K),
        ∃ M' : 𝓞 E →+* Module.End K (Fin d → K), ∀ a c, f ∘ M a c = M' a (f ∘ c)) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (f : Localization.Away r →+* K) (ρ : A),
        (f (algebraMap A _ ρ)) ^ 2 = -(H.d : K) →
        (DetCond D act (spMap (f.comp (algebraMap A _))) (f (algebraMap A _ ρ)) ↔
          ∀ a, f (defect H D.p D.q M (algebraMap A _ ρ) a) = 0) := by
  let R := Localization.Away r
  let j : Sp R ⟶ Sp A := spMap (algebraMap A R)
  haveI : SmoothOfRelativeDimension d ((Over.pullback j).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback (IsPullback.of_hasPullback _ _) hd
  have hs : Smooth ((Over.pullback j).obj G).hom := SmoothOfRelativeDimension.smooth d _
  obtain ⟨act', hact'⟩ := GlobalTheory.DetExtend.exists_oAct_pullback j act
  obtain ⟨M, hM⟩ := GlobalTheory.exists_lie_coordinates_lieMult_iff (𝓞 E) R _ act' d v hs hv
  refine ⟨M, fun K _ f => (hM K f).imp fun M' h => h.1, ?_⟩
  intro K _ _ _ f ρ hρ
  obtain ⟨M', hc, e⟩ := hM K f
  have hx : spMap (f.comp (algebraMap A R)) = spMap f ≫ j := by
    rw [← Spec.map_comp]; rfl
  have hpull : ∀ τ N, LieMult act (spMap (f.comp (algebraMap A R))) τ N ↔
      Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = N := by
    intro τ N
    rw [hx, ← GlobalTheory.LiePull.lieMult_pull (𝓞 E) _ _ G _ j (pullback.fst _ _) act act'
      (isGrpPullback_pullback G j) (fun c => by rw [hact']; exact pullback.lift_fst _ _ _) K (spMap f) τ N, e]
  unfold DetCond
  simp only [hpull]
  rw [GlobalTheory.TraceSpread.finrank_iff_trace H D.p D.q M' _ hρ]
  refine forall_congr' fun x => ?_
  rw [map_defect H D.p D.q M _ f M' hc x, sub_eq_zero]

theorem detCond_of_point : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (act : OAct (𝓞 E) G) (ρ : A), IsAbelianScheme G → ρ ^ 2 = -(H.d : A) → Nonempty (ℚ →+* A) → ∀ (K₀ : Type) [Field K₀] [IsAlgClosed K₀] (g₀ : A →+* K₀), DetCond D act (spMap g₀) (g₀ ρ) → ∀ (K : Type) [Field K] [IsAlgClosed K] (g : A →+* K), DetCond D act (spMap g) (g ρ) := by
  intro E _ _ _ H D A _ _ _ G _ _ act ρ hG hρ hQ' K₀ _ _ g₀ h₀ K _ _ g
  obtain ⟨hQ⟩ := hQ'
  have := hG.smooth
  have := hG.geomConnected
  have hc : ConnectedSpace G.left := (GlobalTheory.GroupConn.connectedSpace_group _ G).1
  obtain ⟨x⟩ : Nonempty G.left := inferInstance
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected G.hom x
  have cz : ∀ (F : Type) [Field F] (f : A →+* F), CharZero F := fun F _ f =>
    (RingHom.charZero_iff (f.comp hQ).injective).1 inferInstance
  have key : ∀ (K₁ : Type) [Field K₁] [IsAlgClosed K₁] (g₁ : A →+* K₁) (K₂ : Type) [Field K₂] [IsAlgClosed K₂]
      (g₂ : A →+* K₂) (r : A), g₁ r ≠ 0 → g₂ r ≠ 0 →
      (∃ v : Fin d → (epsR (Localization.Away r) ⟶
        (Over.pullback (spMap (algebraMap A (Localization.Away r)))).obj G), IsLieBasis v) →
      DetCond D act (spMap g₁) (g₁ ρ) → DetCond D act (spMap g₂) (g₂ ρ) := by
    intro K₁ _ _ g₁ K₂ _ _ g₂ r h₁ h₂ ⟨v, hv⟩ hdet
    haveI := cz K₁ g₁
    haveI := cz K₂ g₂
    have hr0 : r ≠ 0 := fun e => h₁ (by rw [e, map_zero])
    haveI : IsDomain (Localization.Away r) :=
      IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hr0)
    obtain ⟨M, hM, hiff⟩ := detCond_iff_defect D G act d hd r v hv
    let f₁ : Localization.Away r →+* K₁ := IsLocalization.Away.lift r (isUnit_iff_ne_zero.2 h₁)
    let f₂ : Localization.Away r →+* K₂ := IsLocalization.Away.lift r (isUnit_iff_ne_zero.2 h₂)
    have e₁ : f₁.comp (algebraMap A _) = g₁ := IsLocalization.lift_comp _
    have e₂ : f₂.comp (algebraMap A _) = g₂ := IsLocalization.lift_comp _
    have v₁ : f₁ (algebraMap A _ ρ) = g₁ ρ := by rw [← RingHom.comp_apply, e₁]
    have v₂ : f₂ (algebraMap A _ ρ) = g₂ ρ := by rw [← RingHom.comp_apply, e₂]
    have hρ₁ : (f₁ (algebraMap A _ ρ)) ^ 2 = -(H.d : K₁) := by rw [v₁, ← map_pow, hρ]; simp
    have hρ₂ : (f₂ (algebraMap A _ ρ)) ^ 2 = -(H.d : K₂) := by rw [v₂, ← map_pow, hρ]; simp
    have hρR : (algebraMap A (Localization.Away r) ρ) ^ 2 = -(H.d : Localization.Away r) := by
      rw [← map_pow, hρ]; simp
    have h := (hiff K₁ f₁ ρ hρ₁).1 (by rw [e₁, v₁]; exact hdet)
    have h' := (hiff K₂ f₂ ρ hρ₂).2 fun a => by
      rw [eq_zero_of_map H D.p D.q ((algebraMap A _).comp hQ) M hM _ hρR a f₁ (h a), map_zero]
    rwa [e₂, v₂] at h'
  let L := AlgebraicClosure (FractionRing A)
  let gen : A →+* L := (algebraMap (FractionRing A) L).comp (algebraMap A (FractionRing A))
  have hgen : Function.Injective gen :=
    (algebraMap (FractionRing A) L).injective.comp (IsFractionRing.injective A (FractionRing A))
  obtain ⟨r₀, hr₀, v₀⟩ := GlobalTheory.LieLoc.lie_locally_free A G d hd ⟨RingHom.ker g₀, RingHom.ker_isPrime g₀⟩
  have h₀r : g₀ r₀ ≠ 0 := fun e => hr₀ (RingHom.mem_ker.2 e)
  have hgr₀ : gen r₀ ≠ 0 := fun e => h₀r (by rw [hgen (e.trans (map_zero gen).symm), map_zero])
  have hdg := key K₀ g₀ L gen r₀ h₀r hgr₀ v₀ h₀
  obtain ⟨r, hr, v⟩ := GlobalTheory.LieLoc.lie_locally_free A G d hd ⟨RingHom.ker g, RingHom.ker_isPrime g⟩
  have hg : g r ≠ 0 := fun e => hr (RingHom.mem_ker.2 e)
  have hgr : gen r ≠ 0 := fun e => hg (by rw [hgen (e.trans (map_zero gen).symm), map_zero])
  exact key L gen K g r hgr hg v hdg

end GlobalTheory.SpreadOnePoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferenceInvariantLiftsIsWeightZeroCechCocycle
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiffCoc

theorem rsT_rsT {Z : Scheme.{0}} {O₀ T : Z.Opens} (s : Γ(Z, O₀)) (hT : T ≤ O₀) (O : Z.Opens) (hO : O ≤ T) :
    rsT (rsT s T) O = rsT s O := by
  unfold rsT
  rw [dite_eq_left hT, dite_eq_left hO, dite_eq_left (hO.trans hT)]
  simp [resG]

theorem rsT_add {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) (hO : O ≤ O₀) :
    rsT (s + t) O = rsT s O + rsT t O := by
  unfold rsT
  rw [dite_eq_left hO, dite_eq_left hO, dite_eq_left hO, map_add (f := _)]

theorem rsT_sub {Z : Scheme.{0}} {O₀ : Z.Opens} (s t : Γ(Z, O₀)) (O : Z.Opens) (hO : O ≤ O₀) :
    rsT (s - t) O = rsT s O - rsT t O := by
  unfold rsT
  rw [dite_eq_left hO, dite_eq_left hO, dite_eq_left hO, map_sub]

theorem isLift_mono {R : Type} [CommRing R] {G : Over (Sp R)} {D : R → R} {W W' : G.left.Opens} (h : W' ≤ W)
    {d : Fld G.left} (hd : IsLift G D W d) : IsLift G D W' d :=
  ⟨⟨fun O hO => hd.1.1 O (hO.trans h), fun O hO => hd.1.2.1 O (hO.trans h),
    fun O O' h' hO => hd.1.2.2 O O' h' (hO.trans h)⟩, fun O hO => hd.2 O (hO.trans h)⟩

theorem diff_isCoc : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (d : J → Fld Y.H.left), (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) → (∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f))) → ∃ z : Fin n → C1 (fun i => Y.q.left ⁻¹ᵁ V i), (∀ a, IsCoc _ (z a)) ∧ (∀ a i i', IsWt Y 0 _ (z a i i')) ∧ ∀ i i' (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' → ∀ f, d i W f - d i' W f = ∑ a, rsT (z a i i') W * dd a W f := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd D J V d hlift hwt
  have hsm : Smooth Y.H.hom := (GlobalTheory.isSemiAbelian_of_isGt _ _ _ Y.isGt).smooth
  have hl : ∀ i i', Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ Y.q.left ⁻¹ᵁ V i := fun i i' =>
    (inf_le_left : Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ≤ Y.q.left ⁻¹ᵁ V i)
  have hr : ∀ i i', Y.q.left ⁻¹ᵁ (V i ⊓ V i') ≤ Y.q.left ⁻¹ᵁ V i' := fun i i' =>
    (inf_le_right : Y.q.left ⁻¹ᵁ V i ⊓ Y.q.left ⁻¹ᵁ V i' ≤ Y.q.left ⁻¹ᵁ V i')
  have hex : ∀ i i', ∃ h : Fin n → Γ(Y.H.left, Y.q.left ⁻¹ᵁ (V i ⊓ V i')), (∀ a, IsWt Y 0 _ (h a)) ∧
      ∀ (O' : Y.H.left.Opens), O' ≤ Y.q.left ⁻¹ᵁ (V i ⊓ V i') → ∀ f,
        d i O' f - d i' O' f = ∑ a, rsT (h a) O' * dd a O' f := fun i i' =>
    GlobalTheory.VertCoeff.lifts_sub_eq_sum_invFields R Dd.toPre O oa Y n v dd hdd (V i ⊓ V i') D (d i) (d i')
      (isLift_mono (hl i i') (hlift i)) (isLift_mono (hr i i') (hlift i'))
      (fun α V' hV' f hf => hwt i α V' (fun x hx => (hV' hx).1) f hf)
      (fun α V' hV' f hf => hwt i' α V' (fun x hx => (hV' hx).2) f hf)
  choose h hw hh using hex
  refine ⟨fun a i i' => h i i' a, fun a i j k => ?_, fun a i i' => hw i i' a, fun i i' W hW f => hh i i' W hW f⟩

  let U : J → Y.H.left.Opens := fun i => Y.q.left ⁻¹ᵁ V i
  let T := U i ⊓ U j ⊓ U k
  have hij : T ≤ Y.q.left ⁻¹ᵁ (V i ⊓ V j) :=
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) : T ≤ U i ⊓ U j)
  have hjk : T ≤ Y.q.left ⁻¹ᵁ (V j ⊓ V k) :=
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right : T ≤ U j ⊓ U k)
  have hik : T ≤ Y.q.left ⁻¹ᵁ (V i ⊓ V k) :=
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right : T ≤ U i ⊓ U k)
  let c : Fin n → Γ(Y.H.left, T) := fun b =>
    rsT (h i j b) T + rsT (h j k b) T - rsT (h i k b) T
  have hc : ∀ O, O ≤ T → ∀ f, ∑ b, rsT (c b) O * dd b O f = 0 := by
    intro O hO f
    have e : ∀ b, rsT (c b) O = rsT (h i j b) O + rsT (h j k b) O - rsT (h i k b) O := fun b => by
      simp only [c]
      rw [rsT_sub _ _ _ hO, rsT_add _ _ _ hO, rsT_rsT _ hij _ hO, rsT_rsT _ hjk _ hO, rsT_rsT _ hik _ hO]
    simp only [e, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [← hh i j O (hO.trans hij) f, ← hh j k O (hO.trans hjk) f, ← hh i k O (hO.trans hik) f]
    ring
  have h0 := _root_.GlobalTheory.InvCoefUniq.coef_eq_zero R Y.H hsm n v dd hdd T c hc a
  simp only [c] at h0
  exact (sub_eq_zero.1 h0)

end GlobalTheory.DiffCoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfMumfordBundleTorsionPresentations
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PresRigid

open GlobalTheory.CechPic GlobalTheory.SiegLev GlobalTheory.SiegRigid GlobalTheory.ZM

theorem eq_of_field_of_ample {S : Scheme.{0}} {A : Over S} [GrpObj A] (c : CechPic.Pic A.left)
    {K : Type} [Field K] [IsAlgClosed K] {A' : Over (Sp K)} [GrpObj A'] (hA' : IsAbelianScheme A') {z : Sp K ⟶ S}
    {φ φ' : A'.left ⟶ A.left} (h : IsGrpPullback A' A z φ) (h' : IsGrpPullback A' A z φ')
    {M : LB A'.left} (hM : M.IsLB) (hamp : Out.RelAmple A' M) (hMc : cls M hM = pull φ' c)
    (hc : pull φ c = pull φ' c) {N : ℕ} (hN : 3 ≤ N) (hNK : (N : K) ≠ 0)
    (hfix : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp K) (x : Over.mk t ⟶ A'), x ^ N = 1 →
      x.left ≫ φ = x.left ≫ φ') : φ = φ' := by
  obtain ⟨σ, hσ, e⟩ := exists_aut h h'
  have := hA'.comm
  have key := serreAmple K A' hA' M hM hamp N hN hNK σ hσ
    (by rw [hMc, ← pull_comp, e, hc]) fun Ω _ _ t x hx => by
      apply Over.OverMorphism.ext
      apply h'.1.hom_ext
      · rw [Over.comp_left, Category.assoc, e]
        exact hfix Ω t x hx
      · rw [Over.w, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

theorem cls_diag_lam_pull {S S' : Scheme.{0}} {G : Over S} {H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj H]
    [IsCommMonObj H] {f : S' ⟶ S} {φ : H.left ⟶ G.left} (hp : IsGrpPullback H G f φ) {L : LB G.left} (hL : L.IsLB)
    (h₁ : ((abelian₂ G L).pull (lift (𝟙 G) (𝟙 G)).left).IsLB)
    (h₂ : ((abelian₂ H (L.pull φ)).pull (lift (𝟙 H) (𝟙 H)).left).IsLB) : cls _ h₂ = pull φ (cls _ h₁) := by
  have hL' := pull_isLB hL φ
  have hΛ : (abelian₂ G L).IsLB := LB.isLB_linComb hL _ _
  have hΛ' : (abelian₂ H (L.pull φ)).IsLB := LB.isLB_linComb hL' _ _
  have c₁ : cls _ hΛ = lam (cls L hL) (fst G G) (snd G G) := cls_cube_two hL _ _ hΛ
  have c₂ : cls _ hΛ' = lam (cls _ hL') (fst H H) (snd H H) := cls_cube_two hL' _ _ hΛ'
  have c₃ : lam (cls L hL) (pushHom hp H (𝟙 H)) (pushHom hp H (𝟙 H)) = lam (pull φ (cls L hL)) (𝟙 H) (𝟙 H) := by
    simp only [lam, ← map_mul, ← map_one (pushHom hp H)]
    simp only [← pull_comp]
    rfl
  have c₄ : pull (pushHom hp H (𝟙 H)).left (lam (cls L hL) (𝟙 G) (𝟙 G)) =
      lam (cls L hL) (pushHom hp H (𝟙 H)) (pushHom hp H (𝟙 H)) := by
    rw [pull_lam, Category.comp_id]
  have c₅ : (pushHom hp H (𝟙 H)).left = φ := Category.id_comp φ
  rw [cls_pull hΛ, cls_pull hΛ', c₁, c₂, pull_lam, pull_lam, lift_fst, lift_snd, lift_fst, lift_snd, cls_pull hL,
    ← c₃, ← c₄]
  exact congrArg (fun q => pull q _) c₅

theorem diag_square {S S' : Scheme.{0}} {A : Over S'} {B : Over S} {φ : A.left ⟶ B.left}
    {φ₂ : (A ⊗ A).left ⟶ (B ⊗ B).left} (hs : IsSquare φ φ₂) :
    (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (𝟙 B) (𝟙 B)).left := by
  have a₁ := congrArg (fun q => q.left) (lift_fst (𝟙 B) (𝟙 B))
  have a₂ := congrArg (fun q => q.left) (lift_snd (𝟙 B) (𝟙 B))
  have b₁ := congrArg (fun q => q.left) (lift_fst (𝟙 A) (𝟙 A))
  have b₂ := congrArg (fun q => q.left) (lift_snd (𝟙 A) (𝟙 A))
  simp only [Over.comp_left, Over.id_left] at a₁ a₂ b₁ b₂
  apply pullback.hom_ext
  · show (_ ≫ _) ≫ (fst B B).left = (_ ≫ _) ≫ (fst B B).left
    rw [Category.assoc, hs.1, ← Category.assoc, b₁, Category.assoc, a₁]; simp
  · show (_ ≫ _) ≫ (snd B B).left = (_ ≫ _) ≫ (snd B B).left
    rw [Category.assoc, hs.2, ← Category.assoc, b₂, Category.assoc, a₂]; simp

theorem eq_of_lam_of_torsion : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V] (D : DegPre V) {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (P : LB (G2 B).left), P.IsLB → ∀ (t : Sp V ⟶ S) (a₁ a₂ : D.P.A.left ⟶ B.left) (aa₁ aa₂ : (G2 D.P.A).left ⟶ (G2 B).left), IsGrpPullback D.P.A B t a₁ → IsGrpPullback D.P.A B t a₂ → IsSquare a₁ aa₁ → IsSquare a₂ aa₂ → LBIso (abelian₂ D.P.A D.P.L) (P.pull aa₁) → LBIso (abelian₂ D.P.A D.P.L) (P.pull aa₂) → ∀ n : ℕ, 3 ≤ n → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F], (∀ x : TF (R := V) F ⟶ D.P.A, x ^ n = 1 → x.left ≫ a₁ = x.left ≫ a₂) → a₁ = a₂ := by
  intro V _ _ _ D S B _ _ P hP t a₁ a₂ aa₁ aa₂ g₁ g₂ s₁ s₂ w₁ w₂ n hn F _ _ _ hfix
  have hab := D.P.isAb
  have hL := D.P.isLB
  have hΛ : (abelian₂ D.P.A D.P.L).IsLB := LB.isLB_linComb hL _ _
  have hN := pull_isLB hΛ (lift (𝟙 D.P.A) (𝟙 D.P.A)).left
  have hcls : ∀ (a : D.P.A.left ⟶ B.left) (aa : (G2 D.P.A).left ⟶ (G2 B).left), IsSquare a aa →
      LBIso (abelian₂ D.P.A D.P.L) (P.pull aa) →
      cls _ hN = pull a (pull (lift (𝟙 B) (𝟙 B)).left (cls P hP)) := by
    intro a aa s w
    rw [cls_pull hΛ, (cls_eq_iff hΛ (pull_isLB hP aa)).2 w, cls_pull hP, ← pull_comp, ← pull_comp, diag_square s]
  let ψ : D.P.A.left ⟶ D.P.A.left := g₂.1.lift a₁ D.P.A.hom g₁.1.w
  have e₁ : ψ ≫ a₂ = a₁ := g₂.1.lift_fst _ _ _
  have e₂ : ψ ≫ D.P.A.hom = D.P.A.hom := g₂.1.lift_snd _ _ _
  have hψ : IsGrpPullback D.P.A D.P.A (𝟙 _) ψ :=
    IsGrpPullback.cancel g₂ (by rw [Category.id_comp, e₁]; exact g₁) (by rw [e₂, Category.comp_id])
  have hψc : pull ψ (cls _ hN) = cls _ hN := by
    refine Eq.trans ?_ (hcls a₁ aa₁ s₁ w₁).symm
    rw [hcls a₂ aa₂ s₂ w₂, ← pull_comp, e₁]
  let j : Sp F ⟶ Sp V := DegPre.jFR (R := V) F
  have hp := isGrpPullback_pullback D.P.A j
  have := hab.smooth
  have := hab.proper
  have := hab.geomConnected
  have habF : IsAbelianScheme ((Over.pullback j).obj D.P.A) :=
    { comm := Functor.isCommMonObj_obj
      smooth := by change Smooth (pullback.snd D.P.A.hom j); infer_instance
      proper := by change IsProper (pullback.snd D.P.A.hom j); infer_instance
      geomConnected := by change GeometricallyConnected (pullback.snd D.P.A.hom j); infer_instance }
  have : CharZero (FractionRing V) := IsFractionRing.charZero_of_isFractionRing V
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing V) F).injective
  have hnF : (n : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have e' : pullback.fst D.P.A.hom j ≫ ψ = pullback.fst D.P.A.hom j := by
    have := habF.comm
    have hL' := pull_isLB hL (pullback.fst D.P.A.hom j)
    obtain ⟨w, hw⟩ := (cls_eq_iff hL' hL').1 rfl
    have ha' : Out.RelAmple ((Over.pullback j).obj D.P.A) (D.P.L.pull (pullback.fst D.P.A.hom j)) :=
      relAmple_pull hp.1 hL hL' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) D.P.ample
    have hamp := GlobalTheory.EighthPowerFactor.relAmple_diag_lam habF hL'
      (exists_gen_theta_of_isAbelianScheme F _ habF _ hL') ha'
    have hM := pull_isLB (LB.isLB_linComb hL' _ _ : (abelian₂ ((Over.pullback j).obj D.P.A) _).IsLB)
      (lift (𝟙 ((Over.pullback j).obj D.P.A)) (𝟙 ((Over.pullback j).obj D.P.A))).left
    refine eq_of_field_of_ample (cls _ hN) habF ((hp.comp hψ).congr (Category.comp_id _) rfl) hp hM hamp
      (cls_diag_lam_pull hp hL hN hM) (by rw [pull_comp, hψc]) hn hnF fun Ω _ _ x y hy => ?_
    obtain ⟨e, rfl⟩ : ∃ e : F →+* Ω, x = spMap e := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
    obtain ⟨y₀, hy₀⟩ := GlobalTheory.TorsRat.torsion_point_rational F Ω e _ habF n (IsUnit.mk0 _ hnF) y hy
    have : Epi (spMap e) := Flat.epi_of_flat_of_surjective (spMap e)
    have hw₀ : y₀ ≫ ((Over.pullback j).obj D.P.A).hom = 𝟙 _ := by
      rw [← cancel_epi (spMap e), ← Category.assoc, ← hy₀, Over.w y, Category.comp_id]
      rfl
    let y₁ : Over.mk (𝟙 (Sp F)) ⟶ (Over.pullback j).obj D.P.A := Over.homMk y₀ hw₀
    let u : Over.mk (spMap e) ⟶ Over.mk (𝟙 (Sp F)) := Over.homMk (spMap e) (Category.comp_id _)
    have hyu : y = u ≫ y₁ := Over.OverMorphism.ext hy₀
    have hy₁ : y₁ ^ n = 1 := by
      apply Over.OverMorphism.ext
      have h1 : u ≫ y₁ ^ n = u ≫ 1 := by rw [MonObj.comp_pow, ← hyu, hy, MonObj.comp_one]
      exact (cancel_epi (spMap e)).1 (congrArg (fun q => q.left) h1)
    have hy₂ : pushHom hp (Over.mk (𝟙 (Sp F))) y₁ ^ n = 1 := by rw [← map_pow, hy₁, map_one]
    let v : TF (R := V) F ⟶ Over.mk ((Over.mk (𝟙 (Sp F))).hom ≫ j) := Over.homMk (𝟙 _) (by simp [j])
    have hx := hfix (v ≫ pushHom hp (Over.mk (𝟙 (Sp F))) y₁) (by rw [← MonObj.comp_pow, hy₂, MonObj.comp_one])
    have hxl : (v ≫ pushHom hp (Over.mk (𝟙 (Sp F))) y₁).left = y₀ ≫ pullback.fst D.P.A.hom j := Category.id_comp _
    rw [hxl] at hx
    rw [hy₀, Category.assoc, Category.assoc]
    congr 1
    apply g₂.1.hom_ext
    · rw [Category.assoc, Category.assoc, e₁, ← Category.assoc, hx]
    · rw [Category.assoc, Category.assoc, e₂, Category.assoc]
  have hd := ReciprocityTheory.ChartRestriction.G.DVR.GC.isDominant_jFR (V := V) F
  have : IsDominant (pullback.fst D.P.A.hom j) := by
    refine ⟨?_⟩
    rw [DenseRange, Scheme.Pullback.range_fst]
    exact hd.denseRange.preimage D.P.A.hom.isOpenMap
  have : IsReduced D.P.A.left := GlobalTheory.isReduced_of_smooth_of_isReduced D.P.A.hom
  have key : ψ = 𝟙 _ :=
    ext_of_isDominant_of_isSeparated D.P.A.hom (e₂.trans (Category.id_comp _).symm) (pullback.fst D.P.A.hom j)
      (e'.trans (Category.comp_id _).symm)
  rw [← e₁, key, Category.id_comp]

end GlobalTheory.PresRigid

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisionPointPairOverAlgClosed
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

theorem exists_qk_over_cF : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k →
    ∀ (y : D.X) (x : TF (R := V) F ⟶ D.P.A), x ^ k = DegPre.cF D F y → ∃ p : QkPt D F k, p.y = y ∧ p.g.b = x := by
  intro V _ _ D hB F _ _ _ k hk y x hx
  obtain ⟨J, hJ⟩ := good_pt D.P.isLB (default : PrimeSpectrum F)
  exact exists_qk_over (F := F) hJ hB hk y x hx

end GlobalTheory.UCanon
end
end

