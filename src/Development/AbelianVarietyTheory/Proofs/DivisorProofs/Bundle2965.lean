module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2941
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0805
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0820
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0806
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0818
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2145
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2127
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2904
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2894
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2862
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeOfSqZero
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBLift

section
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.Obs

theorem abLift_of_prim (hP : PrimitiveExtendedDegTwoVanish) : AbLift := by
  intro R _ I hI A _ g hA hg X₀ Y₀ i i' ψ₀ ψ₁ ψ₂ hi hi' e₀ e₁ e₂ c hc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨hB, ⟨u, hu⟩, hall⟩ := _root_.GlobalTheory.LBLift.small_basis_lift R I hI _ _ A.hom i L hi hL
  obtain ⟨hun, hdef, hnear⟩ := hall u hu
  obtain ⟨T, _, _, H, K₀, K₁, K₂, le₀, le₁, le₂, v, hH, hv, hrel⟩ := _root_.GlobalTheory.LBLift.IsoRel.mulRel_of_iso R I hI _ _ _ _ A.hom (A ⊗ A).hom i i'
    _ _ _ (overW μ[A]) (overW (fst A A)) (overW (snd A A)) ψ₀ ψ₁ ψ₂ L hL u hi' hB hu e₀ e₁ e₂ hc
  obtain ⟨R₁, _, _, q, hq, hprim⟩ := _root_.GlobalTheory.PrimIdeal.primI_of_ext R I
  haveI : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  haveI : Smooth (A ⊗ A).hom := by
    rw [← Over.w (fst A A)]
    haveI : Smooth (fst A A).left := inferInstanceAs (Smooth (pullback.fst A.hom A.hom))
    infer_instance
  have hpi := hprim _ _ _ _ (pullMap (overW μ[A]) _ H K₀ le₀) (pullMap (overW (fst A A)) _ H K₁ le₁)
    (pullMap (overW (snd A A)) _ H K₂ le₂)
    (fun t ↦ haveI := GlobalTheory.LiftSys.smooth_sec_affine A.hom ((smallG i L).obj t).unop
      inferInstanceAs (Module.Flat R (Sec A.hom ((smallG i L).obj t).unop.1)))
    (fun t ↦ haveI := GlobalTheory.LiftSys.smooth_sec_affine (A ⊗ A).hom (H.obj t).unop
      inferInstanceAs (Module.Flat R (Sec (A ⊗ A).hom (H.obj t).unop.1)))
    (_root_.GlobalTheory.Obs.additiveClassDegreeTwo_vanish_affineBases hP R R₁ q hq A g hA hg _ T _ H K₀ K₁ K₂ le₀ le₁ le₂ hB hH)
  obtain ⟨u', h1, h2⟩ := _root_.GlobalTheory.LBLift.cocycle_of_sqZero R I hI _ _ _ _ _ _ _ hpi u v hun hdef hv hrel
  exact _root_.GlobalTheory.LBLift.exists_pic_of_strict_lift R _ _ A.hom i L hL u' hB (hnear u' h1) (hall u' (hnear u' h1)).1 h2

theorem abLift : AbLift :=
  abLift_of_prim (GlobalTheory.T.primitive_degree_two_extension (GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish fun R _ A _ g hA hg ↦
    ⟨(_root_.GlobalTheory.AbCoh.oStr R A g hA hg).1, (_root_.GlobalTheory.AbCoh.oStr R A g hA hg).2.1⟩))

end

theorem exists_fac_quot {R K : Type} [CommRing R] [Field K] (J : Ideal R) (hJ : J ^ 2 = ⊥) (s : Sp K ⟶ Sp R) :
    ∃ s' : Sp K ⟶ Sp (R ⧸ J), s' ≫ spMap (Ideal.Quotient.mk J) = s := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  have h : ∀ a ∈ J, φ.hom a = 0 := fun a ha ↦ by
    have h2 : a ^ 2 = 0 := by simpa [hJ] using Ideal.pow_mem_pow ha 2
    have := congrArg φ.hom h2
    rw [map_pow, map_zero] at this
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  refine ⟨spMap (Ideal.Quotient.lift J φ.hom h), ?_⟩
  rw [← Spec.map_comp]
  rfl

theorem exists_fam {S : Scheme.{0}} {A U T : Over S} [GrpObj A] [IsLocallyNoetherian U.left] (hA : IsAbelianScheme A)
    (p : T ⟶ U) (hp : ∀ (K : Type) [Field K] (s : Sp K ⟶ S) (t : Over.mk s ⟶ U), ∃ t' : Over.mk s ⟶ T, t' ≫ p = t)
    {N : LB (A ⊗ T).left} (hN : N.IsLB) (ha : IsAdditive N) (c : Pic (A ⊗ U).left)
    (hc : CechPic.pull (A ◁ p).left c = cls N hN) :
    ∃ (M : LB (A ⊗ U).left) (hM : M.IsLB), IsAdditive M ∧
      ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), evc hM a (t ≫ p) = evc hN a t := by
  obtain ⟨M, hM, e⟩ := cls_surj (c - CechPic.pull (lift 1 (snd A U)).left c)
  have k : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ U), evc hM a t =
      CechPic.pull (lift a t).left c - CechPic.pull (lift (1 : Y ⟶ A) t).left c := fun Y a t ↦ by
    rw [evc, e, map_sub, ← CechPic.pull_comp, ← Over.comp_left, comp_lift, MonObj.comp_one, lift_snd]
  have k' : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), CechPic.pull (lift a (t ≫ p)).left c = evc hN a t :=
    fun Y a t ↦ by
    rw [evc, ← hc, ← CechPic.pull_comp, ← Over.comp_left, lift_whiskerLeft]
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), evc hM a (t ≫ p) = evc hN a t := fun Y a t ↦ by
    rw [k, k', k', ha.evc_one hN, sub_zero]
  refine ⟨M, hM, GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres S A U hA M hM ((triv_ev_iff hM _ _).2 (by rw [k, sub_self])) fun K _ _ s t ↦ ?_, key⟩
  obtain ⟨t', rfl⟩ := hp K s t
  refine (isAdditive_iff (pull_isLB hM _)).2 fun Y a a' y ↦ ?_
  simp only [evc_ev hM, lift_fst, lift_snd_assoc]
  simp only [← Category.assoc, key]
  exact (isAdditive_iff hN).1 ha Y a a' _

theorem hasRep_of_sqZero : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ J : Ideal R, J ^ 2 = ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J))) → HasRep A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg J hJ ⟨B, b, P, hP, hb⟩
  refine GlobalTheory.T.representingScheme_of_finite_surjective_lift R A g hA hg B _ b P ?_ ?_ hP hb fun x ↦ ?_
  · haveI : IsClosedImmersion (spMap (Ideal.Quotient.mk J)) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    exact inferInstanceAs (IsFinite (spMap (Ideal.Quotient.mk J)))
  · exact GlobalTheory.LiftSys.surjective_spMap_sqZero _ Ideal.Quotient.mk_surjective hJ
      fun _ h ↦ Ideal.Quotient.eq_zero_iff_mem.1 h
  obtain ⟨C, _, σ, j, hs, hj, ho, hx⟩ := _root_.GlobalTheory.LBLift.exists_chart_lift R J hJ g B b hb.smooth x
  have hN : (ev P (fst A _) (snd A _ ≫ j)).IsLB := pull_isLB hP.fam.isLB _
  have ha : IsAdditive (ev P (fst A _) (snd A _ ≫ j)) := (isAdditive_iff hN).2 fun Y a a' y ↦ by
    simp only [evc_ev hP.fam.isLB, lift_fst, lift_snd_assoc]
    exact (isAdditive_iff hP.fam.isLB).1 hP.fam.add Y a a' _
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.AddFamLift.main abLift R J hJ A g hA hg C σ _ hN ha
  haveI : Smooth (spMap σ) := SmoothOfRelativeDimension.smooth g _
  haveI : IsLocallyNoetherian (Over.mk (spMap σ)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (spMap σ)
  obtain ⟨M, hM, hMa, key⟩ := exists_fam hA (fst (Over.mk (spMap σ)) (Over.mk (spMap (Ideal.Quotient.mk J))))
    (fun K _ s t ↦ by
      obtain ⟨s', hs'⟩ := exists_fac_quot J hJ s
      exact ⟨lift t (Over.homMk s' hs'), lift_fst _ _⟩) hN ha c hc
  refine ⟨_, M, j, ⟨hM, hMa⟩, hs, hj, ho, hx, (same_iff hM hP.fam.isLB _ _).2 ?_⟩
  rw [key, evc_ev hP.fam.isLB, lift_fst, lift_snd_assoc]

end GlobalTheory.LBLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorConstMulDerivationTerm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatOpConst

open GlobalTheory.HeatGlue

section General

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}

theorem op_constFn_mul {vv : Fin n → TanM (𝟙 (Sp R)) G} {dd : Fin n → Fld G.left} (hinv : ∀ a, IsInv G (vv a) (dd a))
    {D : R → R} (Θ : Matrix (Fin n) (Fin n) R) (u : Fin n → R) {d : Fld G.left} {W : G.left.Opens}
    (hd : IsLift G D W d) (p p' : Γ(G.left, W)) (k : ℕ) {O : G.left.Opens} (hO : O ≤ W) (c : R) (f : Γ(G.left, O)) :
    op G dd Θ u d p p' k O (constFn G.hom O c * f) =
      constFn G.hom O c * op G dd Θ u d p p' k O f + constFn G.hom O (2 * (k : R) * D c) * f := by
  have e1 : ∀ a (g : Γ(G.left, O)), dd a O (constFn G.hom O c * g) = constFn G.hom O c * dd a O g := fun a g => by
    rw [(isDer_of_isField (hinv a).1 le_top).2, IsInv.apply_constFn G (vv a) (dd a) (hinv a) O c, mul_zero, add_zero]
  have e2 : d O (constFn G.hom O c * f) = constFn G.hom O c * d O f + f * constFn G.hom O (D c) := by
    rw [(isDer_of_isField hd.1 hO).2, hd.2 O hO c]
  have e3 : constFn G.hom O (k : R) = (k : Γ(G.left, O)) := by simp [constFn]
  have e4 : ∀ a b : Γ(G.left, O), a * (constFn G.hom O c * b) = constFn G.hom O c * (a * b) := fun a b => by ring
  unfold op
  rw [e2, constFn_mul, constFn_mul, constFn_two, e3]
  simp only [e1, e4, ← Finset.mul_sum]
  ring

variable {X Y Z : Scheme.{0}}

theorem gs_rsT (r : Z ⟶ Y) (z : Z) {U V : Y.Opens} (hle : V ≤ U) (h : r z ∈ V) (a : Γ(Y, U)) :
    gs r z V (rsT a V) = gs r z U a := by
  rw [GlobalTheory.KS.rsT_of_le hle]
  exact gs_res r z hle h a

theorem gs_constFn_of_mem (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) {V : Y.Opens} (h : r z ∈ V) (e : R) :
    gs r z V (constFn p V e) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom e) := by
  rw [← GlobalTheory.HeatTermLin.gs_constFn, ← resG_constFn p (le_top : V ≤ ⊤)]
  exact gs_res r z le_top h _

theorem le_wchart {m : Y ⟶ X} {L : LB X} {V : Y.Opens} {j : L.ι} (h : V ≤ m ⁻¹ᵁ L.U j) :
    V ≤ LB.wchart L (K := Fin 1) (fun _ => m) (fun _ => j) := fun _ hy => Set.mem_iInter.2 fun _ => h hy

end General

theorem heat_const_mul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (vv : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vv a) (dd a)) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left Q.P.L dd ⇑D) (k : ℕ) (c : R) (τ τ' τu τu' : SecM Y.q.left Q.P.L k), h.Acts k τ τ' → h.Acts k τu τu' → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval τu r z J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval τ' r z J = gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) * sval τu' r z J + gs (r ≫ Y.H.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (2 * (k : R) * D c)) * sval τu r z J := by
  intro R _ _ Q O _ _ _ oa Y n vv dd hinv D h k c τ τ' τu τu' a₁ a₂ hτ Z r z J hJ
  have hle : ∀ i, h.W i ≤ LB.wchart Q.P.L (K := Fin 1) (fun _ => Y.q.left) (fun _ => h.j i) := fun i =>
    le_wchart (h.le i)
  have s₁ : ∀ i, rsT (τ.f fun _ => h.j i) (h.W i) = constFn Y.H.hom (h.W i) c * rsT (τu.f fun _ => h.j i) (h.W i) := by
    intro i
    refine fn_ext fun y hy => ?_
    obtain ⟨I, hI, eI⟩ := exists_good Q.P.L Q.P.isLB y (K := Unit) (fun _ => 𝟙 _ ≫ Y.q.left) (fun _ => h.j i)
      (fun _ _ _ => rfl) (fun _ => h.le i hy)
    have e := hτ _ (𝟙 _) y I hI
    rw [sval_of τ _ y I (fun _ => h.j i) (fun _ => eI ()), sval_of τu _ y I (fun _ => h.j i) (fun _ => eI ())] at e
    refine (gs_rsT (𝟙 _) y (hle i) hy _).trans (e.trans (Eq.symm ?_))
    exact (gs_mul (𝟙 _) y _ hy _ _).trans (congrArg₂ (· * ·) (gs_constFn_of_mem _ _ y hy c)
      (gs_rsT (𝟙 _) y (hle i) hy _))
  have s₂ : ∀ i, rsT (τ'.f fun _ => h.j i) (h.W i) = constFn Y.H.hom (h.W i) c * rsT (τu'.f fun _ => h.j i) (h.W i) +
      constFn Y.H.hom (h.W i) (2 * (k : R) * D c) * rsT (τu.f fun _ => h.j i) (h.W i) := by
    intro i
    rw [a₁ i, a₂ i, s₁ i]
    exact op_constFn_mul hinv h.Θ h.u (h.lift i) (h.p i) (h.p' i) k le_rfl c _
  obtain ⟨i, hi⟩ : ∃ i, r z ∈ h.W i := TopologicalSpace.Opens.mem_iSup.1 (h.cover.ge trivial)
  have t : ∀ s : SecM Y.q.left Q.P.L k, sval s r z J =
      (trF (K := Fin 1) (fun _ => Y.q.left) (fun _ => (k : ℤ)) r z (fun _ => J (r ≫ Y.q.left)) (fun _ => h.j i)).val *
        gs r z (h.W i) (rsT (s.f fun _ => h.j i) (h.W i)) := fun s =>
    (sec_trans s r z (hJ.mem _ r) (hle i hi)).trans (congrArg _ (gs_rsT r z (hle i) hi _).symm)
  rw [t τ', t τu', t τu, s₂ i, gs_add r z _ hi, gs_mul r z _ hi, gs_mul r z _ hi, gs_constFn_of_mem _ r z hi,
    gs_constFn_of_mem _ r z hi]
  ring

end GlobalTheory.HeatOpConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorFourierTermAlongFibreConnection
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatConn
open GlobalTheory.KS.DlogPol (gs_rsT gs_pbT gs_one gs_sub)

section T
variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem trF_term (e : ℕ) (α : Q.X) (t : Fin 4 → Q.P.L.ι) (J : (Y.H.left ⟶ Q.P.A.left) → Q.P.L.ι) (y : Y.H.left) :
    trF (fun _ : Fin 1 => Y.q.left) (fun _ => (e : ℤ)) (𝟙 _) y (fun _ => J Y.q.left) (fun _ => t 0) =
      trF (Q.famφB α) (DegPre.famε e) Y.q.left y (fun j => J (Y.q.left ≫ Q.famφB α j)) t *
        trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε (𝟙 _) y
          (fun k => J (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k))) (fun k => t (![1, 2, 0, 3] k)) := by
  let G : (Y.H.left ⟶ Q.P.A.left) → Q.P.L.ι → (Y.H.left.presheaf.stalk y)ˣ := fun ψ i =>
    gm ψ y (Q.P.L.U (J ψ) ⊓ Q.P.L.U i) (Q.P.L.g (J ψ) i)
  have e1 : trF (Q.famφB α) (DegPre.famε e) Y.q.left y (fun j => J (Y.q.left ≫ Q.famφB α j)) t =
      ∏ k, G (Y.q.left ≫ Q.famφB α k) (t k) ^ DegPre.famε e k := rfl
  have e2 : trF (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α) DegPre.gtε (𝟙 _) y
      (fun k => J (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k))) (fun k => t (![1, 2, 0, 3] k)) =
      ∏ k, G (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k)) (t (![1, 2, 0, 3] k)) ^ DegPre.gtε k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Category.id_comp, gtφT_eq]
  have e3 : trF (fun _ : Fin 1 => Y.q.left) (fun _ => (e : ℤ)) (𝟙 _) y (fun _ => J Y.q.left) (fun _ => t 0) =
      G Y.q.left (t 0) ^ (e : ℤ) := by
    rw [trF, Fin.prod_univ_one, Category.id_comp]
  have f0 : Q.famφB α 0 = 𝟙 _ := rfl
  rw [e1, e2, e3]
  simp only [Fin.prod_univ_four, DegPre.famε, DegPre.gtε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, f0, Category.comp_id]
  rw [zpow_sub_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_inv, zpow_one, zpow_neg]
  abel

theorem term_germ {e : ℕ} {α : Q.X} {σ : Q.SecB e α} {τ : SecM Y.q.left Q.P.L e} (hτ : IsTerm Y e α σ τ)
    (t : Fin 4 → Q.P.L.ι) (y : Y.H.left) (h₁ : Y.q.left y ∈ LB.wchart Q.P.L (Q.famφB α) t) (h₂ : y ∈ xU Y α t) :
    gs (𝟙 _) y _ (τ.f fun _ => t 0) = gs Y.q.left y _ (σ.f t) * gs (𝟙 _) y _ (xc Y α t).val := by
  have hL : Q.P.L.IsLB := Q.P.isLB
  choose J hJ using fun χ : Y.H.left ⟶ Q.P.A.left => exists_chart hL (χ y)
  have hJ' : Good Q.P.L y J := hJ
  have e₀ := hτ Y.H (𝟙 _) y J hJ'
  have f0 : Q.famφB α 0 = 𝟙 _ := rfl
  have h₀ : y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) fun _ => t 0 := Set.mem_iInter.2 fun _ => by
    have := Set.mem_iInter.1 h₁ 0
    rw [f0] at this
    exact this
  rw [sval_of τ _ y J (fun _ => J Y.q.left) (fun _ => by simp),
    sval_of σ _ y J (fun j => J (Y.q.left ≫ Q.famφB α j)) (fun _ => by simp),
    val_of _ _ y J (fun k => J (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k))) (fun k => by rw [Category.id_comp, gtφT_eq])] at e₀
  simp only [Over.id_left, Over.comp_left, Category.id_comp] at e₀
  have m₁ : (𝟙 Y.H.left : Y.H.left ⟶ Y.H.left) y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) fun _ => J Y.q.left :=
    Set.mem_iInter.2 fun _ => hJ _
  have m₂ : Y.q.left y ∈ LB.wchart Q.P.L (Q.famφB α) fun j => J (Y.q.left ≫ Q.famφB α j) :=
    Set.mem_iInter.2 fun j => hJ _
  have m₃ : (𝟙 Y.H.left : Y.H.left ⟶ Y.H.left) y ∈ LB.wchart Q.P.L (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α)
      fun k => J (Y.q.left ≫ Q.famφB α (![1, 2, 0, 3] k)) :=
    Set.mem_iInter.2 fun k => by
      show y ∈ (DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b α k) ⁻¹ᵁ _
      rw [gtφT_eq]; exact hJ _
  rw [sec_trans τ _ y m₁ h₀, sec_trans σ Y.q.left y m₂ h₁, gen_trans ((Y.Φ Y.H (𝟙 _)).isGen α) (𝟙 _) y m₃ h₂,
    Units.val_mul] at e₀
  rw [gs_unit (𝟙 _) y _ h₂]
  rw [trF_term Y e α t J y, Units.val_mul] at e₀
  exact ((Units.isUnit _).mul (Units.isUnit _)).mul_left_cancel (e₀.trans (mul_mul_mul_comm _ _ _ _))
end T

section T2
variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem term_germ_at {e : ℕ} {α : Q.X} {σ : Q.SecB e α} {τ : SecM Y.q.left Q.P.L e} (hτ : IsTerm Y e α σ τ)
    (t : Fin 4 → Q.P.L.ι) {Z : Scheme.{0}} (r : Z ⟶ Y.H.left) (z : Z)
    (h₁ : Y.q.left (r z) ∈ LB.wchart Q.P.L (Q.famφB α) t) (h₂ : r z ∈ xU Y α t) :
    gs r z _ (τ.f fun _ => t 0) = gs (r ≫ Y.q.left) z _ (σ.f t) * gs r z _ (xc Y α t).val := by
  have h₀ : r z ∈ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (e : ℤ)).U fun _ => t 0 :=
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h₁ 0
  have h₁' : Y.q.left (r z) ∈ (LB.LinComb Q.P.L (Q.famφB α) (DegPre.famε e)).U t := h₁
  have e₁ : gs Y.q.left (r z) _ (σ.f t) = gs (𝟙 _) (r z) (Y.q.left ⁻¹ᵁ _) ((Y.q.left.app _).hom (σ.f t)) := by
    rw [gs_pull (𝟙 _) Y.q.left (r z) _ h₁', Category.id_comp]
  rw [gs_stalkMap r z _ h₀, term_germ Y hτ t (r z) h₁ h₂, map_mul, ← gs_stalkMap r z _ h₂, e₁,
    ← gs_stalkMap r z _ h₁', gs_pull r Y.q.left z _ h₁']
end T2

theorem heat_term_fibre : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → ∀ (α : Q.X) (c : K), CoordEq Y h ν m₀ V pb α c → ∀ (σ σ' : Q.SecB e α), TActs Y h e α σ σ' → ∀ (i : Fin 4 → h.J) (T : Fin 4 → (A₀.left ⟶ A₀.left)), (∀ j, T j ≫ m₀ = m₀ ≫ Q.famφB α j) → (∀ j, T j ≫ A₀.hom = A₀.hom) → ∀ U : A₀.left.Opens, U ≤ m₀ ⁻¹ᵁ LB.wchart Q.P.L (Q.famφB α) (fun j => h.j (i j)) → (∀ j, U ≤ T j ⁻¹ᵁ (m₀ ⁻¹ᵁ V (i j))) → pbT m₀ (σ'.f (fun j => h.j (i j))) U = 2 * (e : Γ(A₀.left, U)) * (rsT (ed _ (σ.f (fun j => h.j (i j)))) U + pbT m₀ (σ.f (fun j => h.j (i j))) U * (∑ j, ((DegPre.famε e j : ℤ) : Γ(A₀.left, U)) * pbT (T j) (pb (i j)) U + constFn A₀.hom U c)) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hK hD α c hC σ σ' hA i T hT₁ hT₂ U hU hUT
  obtain ⟨τ, τ', hτ, hτ', hAc⟩ := hA
  refine ext_lift Y m₀ fun Z a b w z hz => ?_
  have hV : ∀ i, V i ≤ Q.P.L.U (h.j i) := hK.2.2.1
  have hi : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i j) := fun j => hUT j hz
  have ha := hF.mem_chart hD hV hT₁ w hi
  have T0 : T 0 = 𝟙 _ := hF.T_zero (hT₁ 0) (hT₂ 0)
  have wz : Y.q.left (a z) = m₀ (b z) := by
    have := congrArg (fun f => f z) w
    simpa using this
  set W := (LB.LinComb Q.P.L (Q.famφB α) (DegPre.famε e)).U fun j => h.j (i j) with hWdef
  have hU' : U ≤ m₀ ⁻¹ᵁ W := hU
  have hbW : m₀ (b z) ∈ W := hU hz
  have hqa : Y.q.left (a z) ∈ W := wz ▸ hbW
  have hb0 : (b ≫ m₀) z ∈ V (i 0) := by simpa [T0] using hi 0

  have P : ∀ j, gs b z U (pbT (T j) (pb (i j)) U) = gs (b ≫ T j) z _ (pb (i j)) := fun j =>
    gs_pbT b (T j) z (hUT j) hz _
  have Ed : gs b z U (rsT (ed W (σ.f fun j => h.j (i j))) U) = gs b z (m₀ ⁻¹ᵁ W) (ed W (σ.f fun j => h.j (i j))) :=
    gs_rsT b z hU' hz _
  have Sb : ∀ s : Q.SecB e α, gs b z U (pbT m₀ (s.f fun j => h.j (i j)) U) = gs (a ≫ Y.q.left) z W (s.f fun j => h.j (i j)) :=
    fun s => by rw [gs_pbT b m₀ z hU' hz, w]
  have Cc : gs b z U (constFn A₀.hom U c) = cst (b ≫ A₀.hom) z c := gs_constFn _ _ _ _ hz _

  have hΘ : ∀ a' b', gsH a z (h.W (i 0)) ha.1 (constFn Y.H.hom (h.W (i 0)) (h.Θ a' b')) = 0 := fun a' b' => by
    rw [← gs_eq_gsH, hF.gs_const w z (h.W (i 0)) ha.1, hF.symb, cst_eq_cstH, map_zero]
  have hop := congrArg (gsH a z (h.W (i 0)) ha.1) (hAc (i 0))
  rw [map_op h ν e hF.inv (i 0) (h.W (i 0)) le_rfl _ hΘ] at hop
  simp only [← gs_eq_gsH] at hop
  have hWc : h.W (i 0) ≤ (LB.LinComb Q.P.L (K := Fin 1) (fun _ => Y.q.left) fun _ => (e : ℤ)).U fun _ => h.j (i 0) :=
    fun y hy => Set.mem_iInter.2 fun _ => h.le (i 0) hy
  rw [gs_rsT a z hWc ha.1, gs_rsT a z le_rfl ha.1,
    term_germ_at Y hτ' (fun j => h.j (i j)) a z hqa ha.2, ← hD.2.2 Z a b w z (i 0) hb0] at hop

  obtain ⟨δ, -, hδm, hδv⟩ := exists_stalkDer_field (isField_dE h ν hF.field (i 0)) a z ha.1
  set U' : Q.P.A.left.Opens := V (i 0) ⊓ W with hU'def
  have hqU : Y.q.left ⁻¹ᵁ U' ≤ h.W (i 0) := by
    rw [hD.1 (i 0)]; exact fun y (hy : Y.q.left y ∈ U') => hy.1
  have haV : Y.q.left (a z) ∈ V (i 0) := by
    have := ha.1; rw [hD.1 (i 0)] at this; exact this
  have haU : a z ∈ Y.q.left ⁻¹ᵁ U' := ⟨haV, hqa⟩
  have hbU : (b ≫ m₀) z ∈ U' := ⟨hb0, by simpa using hbW⟩
  have haU' : (a ≫ Y.q.left) z ∈ U' := by simpa using haU
  set f' : Γ(Q.P.A.left, U') := resG Q.P.A.left (inf_le_right : U' ≤ W) (σ.f fun j => h.j (i j)) with hf'
  have hAB : gs (𝟙 _) (a z) (h.W (i 0)) (rsT (τ.f fun _ => h.j (i 0)) (h.W (i 0))) =
      gs (𝟙 _) (a z) (Y.q.left ⁻¹ᵁ U') ((Y.q.left.app U').hom f') *
        gs (𝟙 _) (a z) (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))
          (rsT (xc Y α fun j => h.j (i j)).val (h.W (i 0) ⊓ xU Y α fun j => h.j (i j))) := by
    rw [gs_rsT (𝟙 _) (a z) hWc ha.1, term_germ Y hτ (fun j => h.j (i j)) (a z) hqa ha.2,
      gs_rsT (𝟙 _) (a z) inf_le_right ha, gs_pull (𝟙 _) Y.q.left (a z) U' haU, Category.id_comp, hf',
      gs_res Y.q.left (a z) inf_le_right haU]
  have hδ := hδv (h.W (i 0)) le_rfl ha.1 (rsT (τ.f fun _ => h.j (i 0)) (h.W (i 0)))
  rw [hAB, hδm, hδv _ hqU haU, hδv _ inf_le_left ha, ← hD.2.1 Z a b w z (i 0) U' inf_le_left hbU,
    hf', hK.1.res W U' inf_le_right le_top, gs_rsT b z (fun y (hy : m₀ y ∈ U') => hy.2) hbU,
    hC T hT₁ hT₂ Z a b w z i hi, ← gs_stalkMap a z _ haU, ← gs_stalkMap a z _ ha, gs_pull a Y.q.left z U' haU,
    gs_res _ z inf_le_right haU', gs_rsT a z inf_le_right ha] at hδ
  rw [gs_rsT a z hWc ha.1 (τ.f fun _ => h.j (i 0)), term_germ_at Y hτ (fun j => h.j (i j)) a z hqa ha.2, ← hδ] at hop
  have hX : IsUnit (gs a z (xU Y α fun j => h.j (i j)) (xc Y α fun j => h.j (i j)).val) := by
    rw [gs_unit a z _ ha.2]; exact Units.isUnit _
  rw [Sb σ', gs_eq_gsH b z U hz]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_add (f := _), map_sum, map_natCast, map_ofNat, map_intCast]
  simp only [← gs_eq_gsH b z U hz]
  rw [Ed, Sb σ, Cc, Fin.sum_univ_four, P 0, P 1, P 2, P 3]
  rw [T0, Category.comp_id] at hop ⊢
  simp only [W] at hop ⊢
  have f0 : DegPre.famε e 0 = (e : ℤ) - 1 := rfl
  have f1 : DegPre.famε e 1 = 1 := rfl
  have f2 : DegPre.famε e 2 = -1 := rfl
  have f3 : DegPre.famε e 3 = 1 := rfl
  rw [f0, f1, f2, f3]
  push_cast
  apply hX.mul_left_cancel
  linear_combination hop
end GlobalTheory.HeatConn
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeBundleTrivialGeometricFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HeckeFibre

theorem transl_triv {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    (M : LB A.left) (hM : M.IsLB) (hR : Out.Rigidified A M) (K : Type) [Field K] [IsAlgClosed K]
    (y : Sp K ⟶ S) (n : ℕ) (hn : (n : K) ≠ 0) (x : Over.mk y ⟶ A) (hx : x ^ n = 1)
    (h : ∀ z : Over.mk y ⟶ A, z ^ n = 1 → Out.WeilIs A M (n : ℤ) x z 1) :
    ∃ t : (Out.translDiff A M x).Gen, t.IsGen := by
  obtain ⟨L, hL, ⟨c⟩⟩ := GlobalTheory.Moduli.cubicalStr_of_triv_theta GlobalTheory.abelianSchemeLaws_all.1 _ A hA M hM hR
    (GlobalTheory.WeilIntegral.triv_theta GlobalTheory.CubeTop.cubeTheorem hA hM)
  subst hL
  exact GlobalTheory.OrthKer.mem_kernel_of_cubWeil_orthogonal K S y A hA L c n hn x hx
    (fun z hz => (GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.globalFns_holds hA hx hz 1).2 (h z hz))

theorem pic_field_eq_zero (K : Type) [Field K] (c : GlobalTheory.CechPic.Pic (Sp K)) : c = 0 := by
  obtain ⟨V, hV, hc⟩ := GlobalTheory.AbDual.exists_pull_eq_zero c (IsLocalRing.closedPoint K)
  have h := GlobalTheory.AbDual.pull_eq_zero_of_mem V (𝟙 _) (fun z => by
    have : z = IsLocalRing.closedPoint K := Subsingleton.elim (α := PrimeSpectrum K) _ _
    rw [this]; exact hV) hc
  rwa [GlobalTheory.CechPic.pull_id] at h

theorem rigidified_diag {S : Scheme.{0}} (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB)
    (rig₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) :
    Out.Rigidified A (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
  have h0 := (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 rig₁
  refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB (pull_isLB hP _) _)).1 ?_
  rw [GlobalTheory.CechPic.cls_pull (pull_isLB hP _), GlobalTheory.CechPic.cls_pull hP, ← GlobalTheory.CechPic.pull_comp]
  have e : eSec A ≫ (lift (𝟙 A) (𝟙 A)).left = eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
    have h1 : η[A] ≫ (1 : A ⟶ A) = η[A] := by
      rw [MonObj.comp_one, CategoryTheory.Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    simp only [eSec, ← Over.comp_left, comp_lift, Category.comp_id, h1]
  rw [e, GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull hP _ (pull_isLB hP _), h0, map_zero]

end GlobalTheory.HeckeFibre

namespace GlobalTheory.HeckeFibre

theorem fibre_triv : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (g : D.La →ₗ[D.O] D.La) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → (∀ x y, D.EF (g x) (g y) = c * D.EF x y) → (∀ x, ∃ y, g y = k • x) → c ∣ k ^ 2 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ h ∈ GlobalTheory.UPel.HT.Hecke.heckeSub o g N, ∀ (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S), ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ h) (𝟙 o.A)).left).pull (pullback.fst o.A.hom y)).Gen, t.IsGen := by
  intro p _ D R _ b g c k N hc hk hN3 hNp hEF hsurj hdvd S s o h hh K _ _ y
  obtain ⟨x, rfl⟩ := hh
  obtain ⟨β, hβ⟩ : ∃ β : R →+* K, y ≫ s = spMap β :=
    ⟨(Spec.preimage (y ≫ s)).hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := o.geom K y β hβ
  obtain ⟨n, h', hn0, hnp, hsq, hpow, hW⟩ :=
    GlobalTheory.T.exists_sqrt_heckePoint_weilPairing_orthogonal D K _ _ _ I g c k N hc hk (by omega) hNp hEF hsurj hdvd x
  have hnK : (n : K) ≠ 0 := by
    have := (b.unit n hnp).map β
    rw [map_natCast] at this
    exact this.ne_zero
  have htr := transl_triv o.A o.ab _ (pull_isLB o.isLB _) (rigidified_diag o.A o.P o.isLB o.rig₁) K y n hnK
    (h' ^ (k ^ 2 / c)) hpow (fun z hz => by
      have w := hW z hz
      have e1 : unitOn (1 : Kˣ) = 1 := map_one _
      rw [e1] at w
      exact w)
  exact GlobalTheory.T.biextension_trivial_of_translate_difference_trivial o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm (Over.mk y) (pic_field_eq_zero K)
    (o.eta (N • g x)) h' (k ^ 2 / c) (by rw [hsq, hI]) htr

end GlobalTheory.HeckeFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackOfIdempotentImagesAndActionPullbacStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_pullback_of_idempotent_images_and_action_pullback : ∀ (h h' M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S₁ S₂ : Scheme.{0}) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (y : S₂ ⟶ S₁) (c₁ : SiegPre h M ζ s₁) (w₁ : SiegPre h' M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (c₂ : SiegPre h M ζ s₂) (w₂ : SiegPre h' M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₂ act₂ w₁ act₁ y → ZRel e jl o κ c₁ w₁ act₁ → ZRel e jl o κ c₂ w₂ act₂ → SiegPB c₂ c₁ y := by
  first | (exact @GlobalTheory.UPel.HT.siegPB_of_zRel_actPB) | (exact GlobalTheory.UPel.HT.siegPB_of_zRel_actPB) | (intros; apply GlobalTheory.UPel.HT.siegPB_of_zRel_actPB  <;> assumption)
end

