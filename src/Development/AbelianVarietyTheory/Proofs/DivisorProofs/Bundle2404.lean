module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.TorsionZeroCountTwist
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitRedCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb

theorem sec_eq_of_inj {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {s s' : LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (hinj : ∀ W : Y.Opens, Function.Injective (h.app W).hom)
    (H : ∀ y J, Good L y J → sval s (𝟙 Y' ≫ h) y J = sval s' (𝟙 Y' ≫ h) y J) : s = s' := by
  have e : ∀ j, s.f j = s'.f j := fun j => by
    refine hinj _ (fn_ext fun y hy => ?_)
    choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)
    have hJ' : Good L y J := hJ
    have hy' : (𝟙 Y' ≫ h) y ∈ LB.wchart L φ j := hy
    have m := hJ'.mem φ (𝟙 Y' ≫ h)
    refine (gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)
    exact (sec_trans s _ y hy' m).trans ((congrArg _ (H y J hJ')).trans (sec_trans s' _ y hy' m).symm)
  cases s
  cases s'
  congr
  exact funext e

end GlobalTheory.Mum.SecEmb

namespace GlobalTheory.Mum.SecEmb

theorem traitRed_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (C C' : LabCover D) (Sc : Secs C.toModif C.G C.P.L.L C.α) (h : C'.S ⟶ C.S) (β : C'.G.left ⟶ C.G.left),
    h ≫ C.π = C'.π → IsGrpPullback C'.G C.G h β → LBIso C'.P.L.L (C.P.L.L.pull β) →
    ∀ σ : Fin (Sc.N + 1) → SecK C.P.L.L β Sc.k, (∀ i, Agree C.P.L.L (σ i) (Sc.s i)) →
    ∀ θ₀ : SecK C.P.L.L β 1, Agree C.P.L.L θ₀ Sc.θ →
    ∃ θ : C'.P.L.L.Sec, GlobalTheory.Mum.SecEmb.TraitRed C'.toModif C'.G σ θ Sc.Y Sc.j Sc.O := by
  intro R _ _ _ _ D C C' Sc h β hπ hpb hiso σ hσ θ₀ hθ₀
  have hL : C.P.L.L.IsLB := C.P.L.isLB
  obtain ⟨θ₁, hθ₁⟩ := exists_sec hL (φ := fun _ : Fin 1 => β) (ε := fun _ => ((1 : ℕ) : ℤ))
    (φ' := fun _ : PUnit => β) (ε' := fun _ => 1) (fun U _ g => by simp) θ₀
  obtain ⟨w, hw⟩ := hiso
  refine ⟨DVR.secOfIso (u := w) θ₁ hw C'.P.L.isLB (LB.isLB_pull hL β), ?_⟩
  intro W _ _ _ hW φ ξ hφ hloc hξ
  obtain ⟨W', _, _, _, io, G'', _, β'', σ'', θ'', κ, e, hW', hio, hfin, hG'', hκ, he, hσ'', hθ'', hfib⟩ :=
    Sc.trait W hW φ (ξ ≫ h) hφ hloc (by rw [Category.assoc, hπ]; exact hξ)
  obtain ⟨β', hβ'1, hβ'2⟩ : ∃ β' : G''.left ⟶ C'.G.left, β' ≫ β = β'' ∧ β' ≫ C'.G.hom = G''.hom ≫ spMap io ≫ ξ :=
    ⟨hpb.1.lift β'' (G''.hom ≫ spMap io ≫ ξ) (by rw [hG''.1.w]; simp), hpb.1.lift_fst _ _ _, hpb.1.lift_snd _ _ _⟩
  subst hβ'1

  have hρ : Function.Injective ((algebraMap W' (FractionRing W')).comp (io.comp φ)) :=
    (IsFractionRing.injective W' (FractionRing W')).comp (hio.comp hφ)
  obtain ⟨ga, -, hga⟩ := Modif.factor_gp R C.toModif (FractionRing W') _ (jK W' ≫ spMap io ≫ ξ ≫ h) hρ (by
    rw [Category.assoc, Category.assoc, Category.assoc, hπ, hξ]
    simp only [jK, spMap, ← Spec.map_comp]
    rfl)

  have : Smooth C.G.hom := C.semi.smooth
  have : Flat G''.hom := MorphismProperty.of_isPullback (P := @Flat) hG''.1 inferInstance

  have hgen : ∀ (Z : Scheme.{0}) (r : Z ⟶ pullback G''.hom (jK W')), ∃ q : Z ⟶ C.A.A.left,
      q ≫ C.α = r ≫ pullback.fst G''.hom (jK W') ≫ β' ≫ β := fun Z r => by
    refine ⟨C.α_cart.1.lift (r ≫ pullback.fst G''.hom (jK W') ≫ β' ≫ β)
      (r ≫ pullback.snd G''.hom (jK W') ≫ spMap ga) ?_, C.α_cart.1.lift_fst _ _ _⟩
    have w₁ := hG''.1.w
    simp only [Category.assoc] at w₁ ⊢
    rw [w₁, ← hga, pullback.condition_assoc]

  have key : ∀ {n : ℕ} (a : SecK C.P.L.L (β' ≫ β) n) (b : SecK C.P.L.L β n) (c : SecK C.P.L.L C.α n),
      Agree C.P.L.L a c → Agree C.P.L.L b c → ∀ (Z : Scheme.{0}) (r : Z ⟶ G''.left) (z : Z) (J), Good C.P.L.L z J →
        sval a r z J = sval b (r ≫ β') z J := by
    intro n a b c ha hb
    have e₁ : a = ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec b β' := by
      refine sec_eq_of_inj hL (GlobalTheory.ExpInt.generic_app_injective G'') fun y J hJ => ?_
      rw [ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ]
      obtain ⟨q, hq⟩ := hgen _ (𝟙 _)
      have hq' : q ≫ C.α = (𝟙 _ ≫ pullback.fst G''.hom (jK W')) ≫ β' ≫ β := by rw [hq]; simp
      refine (ha _ _ q hq'.symm y J hJ).trans (hb _ _ q ?_ y J hJ).symm
      rw [hq']; simp
    intro Z r z J hJ
    rw [e₁, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ]
  have hv : ∀ i (Z : Scheme.{0}) (r : Z ⟶ G''.left) (z : Z) (J), Good C.P.L.L z J →
      sval (σ'' i) r z J = sval (σ i) (r ≫ β') z J := fun i => key _ _ _ (hσ'' i) (hσ i)
  have hvθ := key _ _ _ hθ'' hθ₀
  refine ⟨W', inferInstance, inferInstance, inferInstance, io, G'', inferInstance, β', κ, e, hW', hio, hfin,
    IsGrpPullback.cancel hpb (by rw [Category.assoc]; exact hG'') hβ'2, hκ, he, ?_⟩
  intro Ω _ p p' y hp hy
  obtain ⟨⟨hs, hproj⟩, hnz⟩ := hfib Ω p p' y hp hy
  have hnzi : ∀ (x : Sp Ω) i, p' x ∈ nonzeroLocus (σ'' i) ↔ (p' ≫ β') x ∈ nonzeroLocus (σ i) := fun x i => by
    choose J hJ using fun ψ : Sp Ω ⟶ C.G.left => exists_chart hL (ψ x)
    rw [GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, hv i _ _ _ _ hJ]
  have ht : ⨆ i, nonzeroLocus (GlobalTheory.secPull (σ i) (p' ≫ β')) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hs.ge (Set.mem_univ x))
    rw [GlobalTheory.nonzeroLocus_secPull] at hi
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
    rw [GlobalTheory.nonzeroLocus_secPull]
    exact (hnzi x i).1 hi
  refine ⟨⟨ht, ?_⟩, fun x hx => ?_⟩
  · rw [← hproj]
    refine GlobalTheory.ProjSpace.toProj_eq_of_locally hs ht fun x => ?_
    obtain ⟨c, hc⟩ := exists_chart hL ((p' ≫ β' ≫ β) x)
    have m₁ : x ∈ (LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β' ≫ β) (fun _ => (Sc.k : ℤ))) p').U
        (fun _ => fun _ => c) :=
      mem_pull.2 (Set.mem_iInter.2 fun _ => by simpa using hc)
    have m₂ : x ∈ (LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β) (fun _ => (Sc.k : ℤ))) (p' ≫ β')).U
        (fun _ => fun _ => c) :=
      mem_pull.2 (Set.mem_iInter.2 fun _ => by simpa using hc)
    refine ⟨(LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β' ≫ β) (fun _ => (Sc.k : ℤ))) p').U (fun _ => fun _ => c) ⊓
      (LB.pull (LB.LinComb C.P.L.L (fun _ : Fin 1 => β) (fun _ => (Sc.k : ℤ))) (p' ≫ β')).U (fun _ => fun _ => c),
      ⟨m₁, m₂⟩, _, inf_le_left, _, inf_le_right, 1, fun j => ?_⟩
    rw [_root_.one_mul]
    refine fn_ext fun z hz => ?_
    have hz' : (p' ≫ β' ≫ β) z ∈ C.P.L.L.U c := by
      have := Set.mem_iInter.1 (mem_pull.1 hz.1) 0
      simpa using this
    obtain ⟨J, hJ, eJ⟩ := exists_good C.P.L.L hL z (fun _ : PUnit => p' ≫ β' ≫ β) (fun _ => c)
      (fun _ _ _ => rfl) (fun _ => hz')
    rw [gs_res _ _ _ hz, gs_res _ _ _ hz]
    refine (GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull _ _) (σ j) (𝟙 _) z _ hz.2).trans
      (Eq.trans ?_ (GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull _ _) (σ'' j) (𝟙 _) z _ hz.1).symm)
    rw [Category.id_comp, Category.id_comp]
    exact (sval_of (σ j) (p' ≫ β') z J (fun _ => c) (fun _ => by rw [Category.assoc]; exact eJ ⟨⟩)).symm.trans
      ((hv j _ _ _ _ hJ).symm.trans (sval_of (σ'' j) p' z J (fun _ => c) (fun _ => eJ ⟨⟩)))
  · have h₁ := hnz x hx
    choose J hJ using fun ψ : Sp Ω ⟶ C.G.left => exists_chart hL (ψ x)
    rw [GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, hvθ _ _ _ _ hJ] at h₁
    refine DVR.nonzeroLocus_secOfIso w θ₁ hw C'.P.L.isLB (LB.isLB_pull hL β) ?_
    rw [GlobalTheory.TwistZero.mem_nonzeroLocus_iff _ _ _ hJ, hθ₁ _ _ _ _ hJ]
    exact h₁

end GlobalTheory.Mum.SecEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitScalarCancelOfIsField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.CancelField

theorem isIso_jK {R : Type} [CommRing R] [IsDomain R] (hR : IsField R) : IsIso (jK R) := by
  have hb : Function.Bijective (algebraMap R (FractionRing R)) :=
    ⟨IsFractionRing.injective R (FractionRing R), IsFractionRing.surjective_iff_isField.2 hR⟩
  have : IsIso (CommRingCat.ofHom (algebraMap R (FractionRing R))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  infer_instance

theorem isIso_gp {R : Type} [CommRing R] [IsDomain R] (M : Modif R) (hR : IsField R) : IsIso M.gp := by
  haveI := isIso_jK hR
  haveI := M.integral
  haveI := M.proper
  haveI := M.dominant
  haveI : IsClosedImmersion M.gp :=
    isClosedImmersion_of_comp_eq_id (M.π ≫ inv (jK R)) M.gp (by rw [← Category.assoc, M.gp_π, IsIso.hom_inv_id])
  haveI : Surjective M.gp := ⟨by
    have h1 := M.gp.isClosedEmbedding.isClosed_range
    have h2 := M.gp.denseRange
    exact Set.range_eq_univ.1 (h1.closure_eq ▸ h2.closure_range)⟩
  exact isIso_of_isClosedImmersion_of_surjective M.gp

theorem sval_comp {X Y₀ Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (p : Z ⟶ Y) (r : Y ⟶ Y₀) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    sval s (p ≫ r) z J = (p.stalkMap z).hom (sval s r (p z) (fun ψ => J (p ≫ ψ))) := by
  have hJ' : Good L (p z) (fun ψ => J (p ≫ ψ)) := fun ψ => hJ (p ≫ ψ)
  rw [sval_of s (p ≫ r) z J (fun k => J (p ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp p r z _ (hJ'.mem φ r) _

theorem scal_cancel {W : Type} [CommRing W] [IsDomain W] {Y : Scheme.{0}} (f : Y ⟶ Sp W) [Flat f] (y : Y) {b : W}
    (hb : b ≠ 0) {u v : Y.presheaf.stalk y}
    (h : gs (𝟙 Y) y ⊤ (scal f b) * u = gs (𝟙 Y) y ⊤ (scal f b) * v) : u = v := by
  set c : Γ(Sp W, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b with hc
  have e1 : gs (𝟙 Y) y ⊤ (scal f b) = (f.stalkMap y).hom (gs (𝟙 (Sp W)) (f y) ⊤ c) := by
    have := gs_pull (𝟙 Y) f y ⊤ trivial c
    rw [Category.id_comp] at this
    refine this.trans ?_
    have := gs_comp f (𝟙 (Sp W)) y ⊤ trivial c
    rwa [Category.comp_id] at this
  have hc0 : c ≠ 0 := by
    intro h0
    apply hb
    have hi : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom :=
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of W)).inv).1
    exact hi (h0.trans (map_zero _).symm)
  have he0 : gs (𝟙 (Sp W)) (f y) ⊤ c ≠ 0 := by
    rw [gs_eq (𝟙 (Sp W)) (f y) ⊤ trivial]
    intro h0
    apply hc0
    have hi := germ_injective_of_isIntegral (Sp W) (U := (𝟙 (Sp W)) ⁻¹ᵁ ⊤) (f y) trivial
    have := hi (h0.trans (map_zero _).symm)
    exact this
  letI := (f.stalkMap y).hom.toAlgebra
  haveI : Module.Flat _ (Y.presheaf.stalk y) := Flat.stalkMap f y
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Y.presheaf.stalk y) (mem_nonZeroDivisors_of_ne_zero he0)
  apply hreg
  simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  rw [← e1]
  exact h

end GlobalTheory.Mum.CancelField

namespace GlobalTheory.Mum


open GlobalTheory.Mum.CancelField in
theorem cancel_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (σ : SecK C.P.L.L T.β k) (s : SecK C.P.L.L C.α k) (b : W) (c : FractionRing R), IsField R → b ≠ 0 → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom b) * sval σ p z J = gs p z ⊤ (scal T.G.hom b) * (gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J)) → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ z J, Good C.P.L.L z J → sval σ p z J = gs p' z ⊤ (scal C.A.A.hom c) * sval s p' z J := by
  intro R _ _ _ _ D C W _ _ _ T k σ s b c hR hb H Z p p' hp z J hJ
  haveI : IsIso C.α := C.α_cart.1.isIso_fst_of_isIso (isIso_gp C.toModif hR)
  haveI : Smooth C.G.hom := C.semi.smooth
  haveI : Flat C.G.hom := inferInstance
  haveI : Flat T.G.hom := MorphismProperty.of_isPullback (P := @Flat) T.cart.1 inferInstance
  obtain ⟨q, hq⟩ : ∃ q : T.G.left ⟶ C.A.A.left, q ≫ C.α = T.β := ⟨T.β ≫ inv C.α, by simp⟩
  have key : ∀ y J', Good C.P.L.L y J' → sval σ (𝟙 _) y J' = gs q y ⊤ (scal C.A.A.hom c) * sval s q y J' := by
    intro y J' hJ'
    exact scal_cancel T.G.hom y hb (H _ (𝟙 _) q (by rw [hq, Category.id_comp]) y J' hJ')
  obtain rfl : p' = p ≫ q := (cancel_mono C.α).1 (by rw [Category.assoc, hq]; exact hp.symm)
  have hJ' : Good C.P.L.L (p z) (fun ψ => J (p ≫ ψ)) := fun ψ => hJ (p ≫ ψ)
  have e1 := sval_comp σ p (𝟙 _) z J hJ
  rw [Category.comp_id] at e1
  rw [e1, sval_comp s p q z J hJ, gs_comp p q z ⊤ trivial, ← map_mul, key (p z) _ hJ']

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslatedCubicalBundleClosedFibreUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.TranslateLevel
open GlobalTheory.UU

section Iso
variable {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {τ : X ⟶ X} {τ' : X' ⟶ X'}

theorem exists_translate (h : τ' ≫ F = F ≫ τ) (w₁ : LB.Iso L' (L.pull F)) (hw₁ : w₁.IsGen) :
    ∃ w : LB.Iso (L'.pull τ') ((L.pull τ).pull F), w.IsGen ∧
      ∀ (Y : Scheme.{0}) (r : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι), τ (F (r y)) ∈ L.U j → τ' (r y) ∈ L'.U k →
        gw w r y (fun _ => j) (fun _ => k) = gw w₁ (r ≫ τ') y j k := by
  have e : ∀ x : X', F (τ' x) = τ (F x) := fun x => congrArg (fun g => g x) h
  have le : ∀ (j : L.ι) (k : L'.ι), ((L.pull τ).pull F).U (fun _ _ => j) ⊓ (L'.pull τ').U (fun _ => k) ≤
      τ' ⁻¹ᵁ ((L.pull F).U (fun _ => j) ⊓ L'.U k) := fun j k x hx =>
    ⟨mem_pull.2 (by rw [e]; exact mem_pull.1 (mem_pull.1 hx.1)), mem_pull.1 hx.2⟩
  let w : LB.Iso (L'.pull τ') ((L.pull τ).pull F) :=
    ⟨fun p => res (le (p.1 PUnit.unit PUnit.unit) (p.2 PUnit.unit))
      (pullU τ' _ (w₁.s (fun _ => p.1 PUnit.unit PUnit.unit, p.2 PUnit.unit)))⟩
  have key : ∀ (Y : Scheme.{0}) (r : Y ⟶ X') (y : Y) (j : L.ι) (k : L'.ι), τ (F (r y)) ∈ L.U j → τ' (r y) ∈ L'.U k →
      gw w r y (fun _ => j) (fun _ => k) = gw w₁ (r ≫ τ') y j k := fun Y r y j k hj hk => by
    have hm : r y ∈ ((L.pull τ).pull F).U (fun _ _ => j) ⊓ (L'.pull τ').U (fun _ => k) :=
      ⟨mem_pull.2 (mem_pull.2 hj), mem_pull.2 hk⟩
    exact (gm_res r y (le j k) hm _).trans (gm_pull r τ' y _ (@le j k (r y) hm) _)
  refine ⟨w, (isGen_iff w).2 fun Y r y j j' k k' hj hj' hk hk' => ?_, key⟩
  have a := (isGen_iff w₁).1 hw₁ Y (r ≫ τ') y (j PUnit.unit) (j' PUnit.unit) (k PUnit.unit) (k' PUnit.unit)
    (by show F (τ' (r y)) ∈ _; rw [e]; exact mem_pull.1 hj) (by show F (τ' (r y)) ∈ _; rw [e]; exact mem_pull.1 hj')
    ((mem_pull (F := τ')).1 hk) ((mem_pull (F := τ')).1 hk')
  rw [Category.assoc, h, ← Category.assoc] at a
  refine (key Y r y _ _ (mem_pull.1 hj) (mem_pull.1 hk)).trans (a.trans ?_)
  exact congrArg₂ (· * ·) (congrArg₂ (· * ·) (gm_pull_g L τ (r ≫ F) y j j' hj hj').symm
    (congrArg (·⁻¹) (gm_pull_g L' τ' r y k k' hk hk').symm))
    (key Y r y _ _ (mem_pull.1 hj') (mem_pull.1 hk')).symm

end Iso

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']


omit [IsCommMonObj G] in
theorem left_translate (a : 𝟙_ (Over S) ⟶ G) {T : Over S} (x : T ⟶ G) :
    x.left ≫ ((toUnit G ≫ a) * 𝟙 G).left = ((toUnit T ≫ a) * x).left := by
  rw [← Over.comp_left, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]


set_option maxHeartbeats 1000000 in
theorem exists_translate_pull {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
    (Q P : CP G) (P₁ : CP G') (a : 𝟙_ (Over S) ⟶ G) (a' : 𝟙_ (Over S') ⟶ G') (ha : a'.left ≫ F = f ≫ a.left)
    (h2 : a' ^ 2 = 1) (hP : P.L.L = Q.L.L.pull ((toUnit G ≫ a) * 𝟙 G).left)
    (hs : ∀ (T : Over S) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → Q.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good Q.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val Q.sym ((toUnit T ≫ a) * x).left z J * (val Q.sym (toUnit T ≫ a).left z J)⁻¹)
    (hc : ∀ (T : Over S) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → Q.L.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good Q.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV Q.c z J x y ((toUnit T ≫ a) * u) * (cubV Q.c z J x y (toUnit T ≫ a))⁻¹)
    {w₁ : LB.Iso P₁.L.L (Q.L.L.pull F)} (h₁ : IsCPMap P₁ Q f F hw w₁) :
    ∃ P₀ : CP G', (∃ w, IsCPMap P₀ P f F hw w) ∧ P₀.L.L = P₁.L.L.pull ((toUnit G' ≫ a') * 𝟙 G').left ∧
      (∀ (T : Over S') (x : T ⟶ G') (z : T.left) (J : (T.left ⟶ G'.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G'.left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left))) →
        val P₀.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a') * x).left z J * (val P₁.sym (toUnit T ≫ a').left z J)⁻¹) ∧
      (∀ (T : Over S') (x y u : T ⟶ G') (z : T.left) (J : (T.left ⟶ G'.left) → P₁.L.L.ι)
        (J' : (T.left ⟶ G'.left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left))) →
        cubV P₀.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a') * u) * (cubV P₁.c z J x y (toUnit T ≫ a'))⁻¹) := by
  obtain ⟨⟨L, rg, hL, hrg⟩, c, sy, g₁, g₂, g₃⟩ := P
  dsimp only at hP hs hc
  subst hP
  have hβ : ∀ T : Over S', toBase hw (toUnit T ≫ a') = toUnit (Over.mk (T.hom ≫ f)) ≫ a := fun T =>
    Over.OverMorphism.ext (by
      show ((toUnit T).left ≫ a'.left) ≫ F = (toUnit (Over.mk (T.hom ≫ f))).left ≫ a.left
      rw [Rosenlicht.toUnit_left, Rosenlicht.toUnit_left, Category.assoc, ha, ← Category.assoc]; rfl)
  have hpt : ∀ {T : Over S'} (x : T ⟶ G'), (x.left ≫ F) ≫ ((toUnit G ≫ a) * 𝟙 G).left =
      ((toUnit T ≫ a') * x).left ≫ F := fun {T} x => by
    refine (left_translate a (toBase hw x)).trans ?_
    rw [← hβ, ← h₁.mul]; rfl
  have hτ : ((toUnit G' ≫ a') * 𝟙 G').left ≫ F = F ≫ ((toUnit G ≫ a) * 𝟙 G).left :=
    (hpt (𝟙 G')).symm.trans (congrArg (· ≫ _) (Category.id_comp F))
  obtain ⟨w, hg, hv⟩ := exists_translate hτ w₁ h₁.gen
  obtain ⟨rig, hr, c₀, s₀, k₁, k₂, k₃, H⟩ := exists_isCPMap (hw := hw) ⟨⟨_, rg, hL, hrg⟩, c, sy, g₁, g₂, g₃⟩ h₁.mul _
    (pull_isLB P₁.L.isLB _) w hg
  have main : ∀ (T : Over S') (z : T.left) (J : (T.left ⟶ G'.left) → P₁.L.L.ι), Good P₁.L.L z J →
      (∀ x : T ⟶ G', val s₀ x.left z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left)) =
          val P₁.sym ((toUnit T ≫ a') * x).left z J * (val P₁.sym (toUnit T ≫ a').left z J)⁻¹) ∧
      ∀ x y u : T ⟶ G', cubV c₀ z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left)) x y u =
        cubV P₁.c z J x y ((toUnit T ≫ a') * u) * (cubV P₁.c z J x y (toUnit T ≫ a'))⁻¹ := by
    intro T z J hJ
    obtain ⟨I, hI⟩ := exists_good_pt Q.L.isLB z
    obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w₁ x.left z (I (x.left ≫ F)) (J x.left) := ⟨_, fun _ => rfl⟩
    obtain ⟨-, a₂, a₃⟩ := h₁.vals T z J I hJ hI W hW
    obtain ⟨b, hb⟩ : ∃ b, b = toUnit T ≫ a' := ⟨_, rfl⟩
    have hbb : b⁻¹ = b := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← sq, hb, ← MonObj.comp_pow, h2, MonObj.comp_one]
    obtain ⟨-, b₂, b₃⟩ := H.vals T z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left))
      (fun r _ => I (r ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (fun r => mem_pull.2 (hJ (r ≫ _)))
      (fun r => mem_pull.2 (hI (r ≫ _))) (fun x => W (b * x)) (fun x => by
        refine Eq.trans ?_ (hv _ x.left z _ _ (hI ((x.left ≫ F) ≫ _)) (hJ (x.left ≫ _))).symm
        rw [hW, hpt, left_translate, hb])
    rw [← hb]
    refine ⟨fun x => ?_, fun x y u => ?_⟩
    · have e₀ := hs (Over.mk (T.hom ≫ f)) (toBase hw x) z I _ hI (fun _ => HEq.rfl)
      rw [← hβ, ← h₁.mul, ← hb] at e₀
      have e₁ : val Q.sym ((b * x).left ≫ F) z I * (val Q.sym (b.left ≫ F) z I)⁻¹ * W (b * x) =
          W (b * x⁻¹) * val s₀ x.left z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left)) :=
        (congrArg (· * W (b * x)) e₀).symm.trans (b₂ x)
      have e₂ := a₂ (b * x)
      have e₃ := a₂ b
      rw [mul_inv, hbb] at e₂
      rw [hbb] at e₃
      apply Additive.ofMul.injective
      have f₁ := congrArg Additive.ofMul e₁
      have f₂ := congrArg Additive.ofMul e₂
      have f₃ := congrArg Additive.ofMul e₃
      simp only [ofMul_mul, ofMul_inv] at f₁ f₂ f₃ ⊢
      linear_combination (norm := abel) f₂ - f₁ - f₃
    · have e₀ := hc (Over.mk (T.hom ≫ f)) (toBase hw x) (toBase hw y) (toBase hw u) z I _ hI (fun _ => HEq.rfl)
      rw [← hβ, ← h₁.mul, ← hb] at e₀
      obtain ⟨C, hC⟩ : ∃ C : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ, ∀ v, C v =
        cubV Q.c (T := Over.mk (T.hom ≫ f)) z I (toBase hw x) (toBase hw y) (toBase hw v) := ⟨_, fun _ => rfl⟩
      have e₁ : C (b * u) * (C b)⁻¹ * W (b * (x * y)) * W (b * (x * u)) * W (b * (y * u)) * W (b * 1) =
          W (b * (x * y * u)) * W (b * x) * W (b * y) * W (b * u) *
            cubV c₀ z (fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left)) x y u := by
        rw [hC, hC]
        exact (congrArg (· * W (b * (x * y)) * W (b * (x * u)) * W (b * (y * u)) * W (b * 1)) e₀).symm.trans (b₃ x y u)
      have e₂ : ∀ v, C v * W (x * y) * W (x * v) * W (y * v) * W 1 =
          W (x * y * v) * W x * W y * W v * cubV P₁.c z J x y v := fun v => by rw [hC]; exact a₃ x y v
      have e₃ := e₂ (b * u)
      have e₄ := e₂ b
      rw [mul_left_comm x b, mul_left_comm y b, mul_left_comm (x * y) b] at e₃
      rw [mul_comm x b, mul_comm y b, mul_comm (x * y) b] at e₄
      rw [_root_.mul_one] at e₁
      apply Additive.ofMul.injective
      have f₁ := congrArg Additive.ofMul e₁
      have f₂ := congrArg Additive.ofMul e₃
      have f₃ := congrArg Additive.ofMul e₄
      simp only [ofMul_mul, ofMul_inv] at f₁ f₂ f₃ ⊢
      linear_combination (norm := abel) f₂ - f₁ - f₃
  refine ⟨⟨⟨_, rig, _, hr⟩, c₀, s₀, k₁, k₂, k₃⟩, ⟨w, H⟩, rfl, fun T x z J J' hJ h => ?_, fun T x y u z J J' hJ h => ?_⟩
  · obtain rfl : J' = fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left) := funext fun r => eq_of_heq (h r)
    exact (main T z J hJ).1 x
  · obtain rfl : J' = fun r _ => J (r ≫ ((toUnit G' ≫ a') * 𝟙 G').left) := funext fun r => eq_of_heq (h r)
    exact (main T z J hJ).2 x y u

theorem exists_section_pullback (f : S' ⟶ S) (a : 𝟙_ (Over S) ⟶ G) (h2 : a ^ 2 = 1) :
    ∃ a' : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G, a'.left ≫ pullback.fst G.hom f = f ≫ a.left ∧ a' ^ 2 = 1 := by
  have h0 : (f ≫ a.left) ≫ G.hom = 𝟙 S' ≫ f := by
    rw [Category.assoc, Over.w a]; simp
  let a' : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G :=
    Over.homMk (pullback.lift (f ≫ a.left) (𝟙 S') h0) (pullback.lift_snd _ _ _)
  have ha : a'.left ≫ pullback.fst G.hom f = f ≫ a.left := pullback.lift_fst _ _ _
  refine ⟨a', ha, ?_⟩
  let β := toBaseHom (toBase_mul_pullback G f) (𝟙_ (Over S'))
  have e : β a' = toUnit _ ≫ a := Over.OverMorphism.ext (by
    refine ha.trans ?_
    rw [Over.comp_left, Rosenlicht.toUnit_left]
    exact congrArg (· ≫ a.left) (Category.id_comp f).symm)
  have e' : β (a' ^ 2) = β 1 := by rw [map_pow, map_one, e, ← MonObj.comp_pow, h2, MonObj.comp_one]
  exact Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) e')
    ((Over.w (a' ^ 2)).trans (Over.w (1 : 𝟙_ (Over S') ⟶ (Over.pullback f).obj G)).symm))

theorem exists_level_translate : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G), a ^ 2 = 1 →
    ∀ P : GlobalTheory.UU.CP G, P.L.L = U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left →
      (∀ (T : Over (Sp R)) (x : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        val P.sym x.left z J' =
          val U.symG ((toUnit T ≫ a) * x).left z J * (val U.symG (toUnit T ≫ a).left z J)⁻¹) →
      (∀ (T : Over (Sp R)) (x y u : T ⟶ G) (z : T.left) (J : (T.left ⟶ G.left) → U.LG.L.ι)
        (J' : (T.left ⟶ G.left) → P.L.L.ι), Good U.LG.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit G ≫ a) * 𝟙 G).left))) →
        cubV P.c z J' x y u = cubV U.cubG z J x y ((toUnit T ≫ a) * u) * (cubV U.cubG z J x y (toUnit T ≫ a))⁻¹) →
    ∀ P₁ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G),
      GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₁ (GlobalTheory.ValueForm.modelCP U.toUnifPre GlobalTheory.firstFiveLaws.1.globalFns) →
    ∃ (a₀ : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) ⟶ thickObj R (maximalIdeal R) 0 G)
      (P₀ : GlobalTheory.UU.CP (thickObj R (maximalIdeal R) 0 G)),
      a₀.left ≫ pullback.fst G.hom (thick R (maximalIdeal R) 0) = thick R (maximalIdeal R) 0 ≫ a.left ∧ a₀ ^ 2 = 1 ∧
      GlobalTheory.UU.IsLevelCP (maximalIdeal R) 0 P₀ P ∧
      P₀.L.L = P₁.L.L.pull ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left ∧
      (∀ (T : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) (x : T ⟶ thickObj R (maximalIdeal R) 0 G) (z : T.left)
        (J : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₁.L.L.ι)
        (J' : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left))) →
        val P₀.sym x.left z J' =
          val P₁.sym ((toUnit T ≫ a₀) * x).left z J * (val P₁.sym (toUnit T ≫ a₀).left z J)⁻¹) ∧
      (∀ (T : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1))))) (x y u : T ⟶ thickObj R (maximalIdeal R) 0 G) (z : T.left)
        (J : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₁.L.L.ι)
        (J' : (T.left ⟶ (thickObj R (maximalIdeal R) 0 G).left) → P₀.L.L.ι), Good P₁.L.L z J →
        (∀ r, HEq (J' r) (fun _ : PUnit.{1} => J (r ≫ ((toUnit (thickObj R (maximalIdeal R) 0 G) ≫ a₀) * 𝟙 (thickObj R (maximalIdeal R) 0 G)).left))) →
        cubV P₀.c z J' x y u = cubV P₁.c z J x y ((toUnit T ≫ a₀) * u) * (cubV P₁.c z J x y (toUnit T ≫ a₀))⁻¹) := by
  intro R _ _ _ D A G _ _ U a h2 P hP hs hc P₁ h₁
  obtain ⟨w₁, h₁⟩ := h₁
  obtain ⟨a₀, ha, h₀⟩ := exists_section_pullback (thick R (maximalIdeal R) 0) a h2
  obtain ⟨P₀, k⟩ := exists_translate_pull _ P P₁ a a₀ ha h₀ hP hs hc h₁
  exact ⟨a₀, P₀, ha, h₀, k⟩

end GlobalTheory.Mum.TranslateLevel
end
end

