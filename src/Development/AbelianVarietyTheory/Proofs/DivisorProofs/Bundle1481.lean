module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1463
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1454
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0810
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1467
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapDegreeEqExpCharPowMulCardKernel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePlacesCentreOutsideOpen
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem evAt_congr' {R : Type} [CommRing R] {X : Scheme.{0}} {ξ ξ' : Sp R ⟶ X} (e : ξ = ξ') {U : X.Opens}
    (h : ⊤ ≤ ξ ⁻¹ᵁ U) (h' : ⊤ ≤ ξ' ⁻¹ᵁ U) (f : Γ(X, U)) : evAt ξ h f = evAt ξ' h' f := by
  subst e; rfl

theorem top_le_preimage_comp' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) :
    ⊤ ≤ (f ≫ g) ⁻¹ᵁ U := by
  intro z _
  exact h (Set.mem_univ (f z))

theorem finite_centre_not_mem (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E]
    [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)]
    (x : Sp K ⟶ C) (hx : IsGenOver k x) (V : C.Opens) (hV : (V : Set C).Nonempty) :
    {p : Place k E | ∃ b : Sp p.O ⟶ C, spMap p.O.subtype ≫ b = spMap (algebraMap K E) ≫ x ∧ ¬ ⊤ ≤ b ⁻¹ᵁ V}.Finite := by
  have hC := hx.1
  haveI : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hC.1 hC.2.2
  obtain ⟨z, hz⟩ := hV
  obtain ⟨V', hV'a, hzV', hV'V⟩ := Opens.isBasis_iff_nbhd.1 C.isBasis_affineOpens hz
  have hV'a : IsAffineOpen V' := hV'a
  obtain ⟨hxV', -, -⟩ := _root_.GlobalTheory.Nef.isGen_evAt_frac K C x hx.2.1 V' ⟨z, hzV'⟩
  obtain ⟨ev1, ev2, -, -, ev5, ev6, -⟩ := _root_.GlobalTheory.Nef.evAt_calculus
  let f : Γ(C, V') →+* E := (algebraMap K E).comp (evAt x hxV')
  haveI := hC.1
  haveI : Smooth (strHom k (X := C)) := SmoothOfRelativeDimension.smooth 1 _
  have eV : V' ≤ strHom k C ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let ψ := ((strHom k C).appLE ⊤ V' eV).hom
  have hft : ψ.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) (strHom k C) inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨V', hV'a⟩ eV
  letI := ψ.toAlgebra
  obtain ⟨s, hs⟩ := hft.out

  have hconst : ∀ (p : Place k E) (c : Γ(Sp k, ⊤)), p.1 (f (ψ c)) ≤ 1 := by
    intro p c
    have hxs : ⊤ ≤ (x ≫ strHom k C) ⁻¹ᵁ (⊤ : (Sp k).Opens) := top_le_preimage_comp' x (strHom k C) ⊤ (fun _ _ => trivial)
    have htop : ⊤ ≤ (𝟙 (Sp k)) ⁻¹ᵁ (⊤ : (Sp k).Opens) := fun _ _ => trivial
    have h1 : evAt x hxV' (ψ c) = evAt (x ≫ strHom k C) hxs c :=
      (ev2 K C (Sp k) x (strHom k C) V' ⊤ hxV' _ eV c).symm
    have h2 : evAt (x ≫ strHom k C) hxs c =
        evAt (spMap (algebraMap k K) ≫ 𝟙 (Sp k)) (top_le_preimage_comp' _ _ _ htop) c :=
      evAt_congr' (by rw [Category.comp_id]; exact hx.2.2) _ _ c
    have h3 := ev1 k K (Sp k) (algebraMap k K) (𝟙 (Sp k)) ⊤ htop (top_le_preimage_comp' _ _ _ htop) c
    have hf : f (ψ c) = algebraMap k E (evAt (𝟙 (Sp k)) htop c) := by
      simp only [f, RingHom.comp_apply]
      rw [h1, h2, h3, ← IsScalarTower.algebraMap_apply]
    rw [hf]
    by_cases hd : evAt (𝟙 (Sp k)) htop c = 0
    · rw [hd, map_zero, map_zero]; exact zero_le'
    · exact (p.2.2 _ hd).le
  have key : ∀ p : Place k E, (∀ a ∈ s, p.1 (f a) ≤ 1) → ∀ g, p.1 (f g) ≤ 1 := by
    intro p hp g
    have hg : g ∈ Algebra.adjoin Γ(Sp k, ⊤) (s : Set Γ(C, V')) := by rw [hs]; trivial
    induction hg using Algebra.adjoin_induction with
    | mem a ha => exact hp a ha
    | algebraMap c => exact hconst p c
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact (p.1.map_add _ _).trans (max_le ha hb)
    | mul a b _ _ ha hb => rw [map_mul, map_mul]; exact mul_le_one' ha hb
  have hE : IsFF k E := (_root_.GlobalTheory.Nef.isFF_main k K (_root_.GlobalTheory.Nef.CurveFF.isFF_of_isGenOver k K C x hx)).2 E
  refine ((s.finite_toSet.biUnion fun a _ => (?_ : {p : Place k E | ¬ p.1 (f a) ≤ 1}.Finite))).subset ?_
  · by_cases h0 : f a = 0
    · simpa [h0] using (Set.finite_empty : (∅ : Set (Place k E)).Finite)
    · exact (_root_.GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero k E hE (f a) h0).1.subset fun p hp h1 => hp h1.le
  · rintro p ⟨b, hb1, hb2⟩
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    by_contra hno
    push_neg at hno
    have hall := key p fun a ha => hno a ha
    have hmem : ∀ g, f g ∈ p.O := fun g => (Valuation.mem_valuationSubring_iff _ _).2 (hall g)
    let φ : Γ(C, V') →+* p.O := f.codRestrict p.O hmem
    obtain ⟨b', hb', hev⟩ := ev6 p.O C V' hV'a φ
    have hc := top_le_preimage_comp' (spMap p.O.subtype) b' V' hb'
    have hd := top_le_preimage_comp' (spMap (algebraMap K E)) x V' hxV'
    have hcd : spMap p.O.subtype ≫ b' = spMap (algebraMap K E) ≫ x := by
      refine ev5 E C _ _ V' hV'a hc hd ?_
      ext g
      rw [ev1 p.O E C p.O.subtype b' V' hb' hc g, ev1 K E C (algebraMap K E) x V' hxV' hd g, hev]
      rfl
    have hbb := (_root_.GlobalTheory.Nef.existsUnique_centre k K E C x hx p).unique hb1 hcd
    subst hbb
    exact hb2 fun w hw => hV'V (hb' hw)

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMulEq
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UU.MulDegree

theorem finrank_mul_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → n ≠ 0 → ∀ [IsFinite (𝟙 B ^ n : B ⟶ B).left] [Flat (𝟙 B ^ n : B ⟶ B).left], ∀ x : B.left, (𝟙 B ^ n : B ⟶ B).left.finrank x = n ^ (2 * g) := by
  intro k _ _ B _ g n hB hg hn0 _ _ x
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  haveI := hB.comm
  haveI := hB.smooth
  haveI := hB.proper
  haveI : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have hq : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hn0)
  haveI : IsMonHom (𝟙 B ^ n : B ⟶ B) := GlobalTheory.AbLaw.MulN.isMonHom_mulA B n
  haveI : Surjective (𝟙 B ^ n : B ⟶ B).left :=
    (GlobalTheory.flat_and_surjective_of_isFinite_grpEnd k B (𝟙 B ^ n)).2
  obtain ⟨D, -, hD⟩ := GlobalTheory.DegKer.exists_mapDeg_of_isFinite _ _ (𝟙 B ^ n : B ⟶ B).left inferInstance inferInstance
  have hrank : ∀ y : B.left, (𝟙 B ^ n : B ⟶ B).left.finrank y = D :=
    fun y => GlobalTheory.SemiAbelianTower.finrank_eq_of_mapDeg _ hD y
  rw [hrank x]
  have hproj := _root_.GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme k B hB
  obtain ⟨H, m, s, hH, hs, hsym⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmpleBy k B hB hproj
  obtain ⟨r, hr⟩ : ∃ r : LB.Gen (H.pull (eSec B)), r.IsGen :=
    DVR.exists_gen_of_isLB_local (V := k) _ (pull_isLB hH _)
  obtain ⟨M, hM⟩ := (GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps hG _ B hB).1 ⟨H, r, hH, hr⟩
    (GlobalTheory.AbLaw.CubeProj.exists_gen_theta_abelianVariety hG k B hB hproj H hH) hsym
  have hiso : LBIso (AbLaw.pw H ((n ^ 2 : ℕ) : ℤ)) (H.pull (𝟙 B ^ n).left) := by
    have h := _root_.GlobalTheory.UU.lbIso_pw_pull_pow_local k B M n
    rw [hM] at h
    rw [Nat.cast_pow]
    exact h
  have hφ : (𝟙 B ^ n).left ≫ B.hom = B.hom := Over.w _
  obtain ⟨hfin, hmono, c, C, hc1, hgrow⟩ :=
    GlobalTheory.VeryAmpleGrowth.finite_monotone_growth k B.left B.hom g hg H m s hH hs
  have e := GlobalTheory.UU.TorsionCount.nonempty_secEquiv B.hom _ hφ hH (n ^ 2) hiso
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.finrank_sec_pull_sandwich_flat k B.left B.left B.hom (𝟙 B ^ n).left H m s hH hs D hrank hfin fun t => by
    obtain ⟨e⟩ := e t
    haveI := hfin (n ^ 2 * t)
    exact Module.Finite.equiv e
  rw [pow_mul]
  refine GlobalTheory.UU.degree_eq_pow_of_growth (fun t : ℕ => Module.finrank k (SecOnR B.hom (AbLaw.pw H t) ⊤)) g c C a _ (n ^ 2)
    hc1 hq hmono hgrow fun t => ?_
  obtain ⟨e₁⟩ := e (t + a)
  obtain ⟨e₂⟩ := e t
  exact ⟨(ha t).1.trans e₁.finrank_eq.ge, e₂.finrank_eq.le.trans (ha t).2⟩

end GlobalTheory.UU.MulDegree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankTorusExtensionCharactersLeRelDimStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_torusExtension_characters_le_relDim : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G] (E : TorusExtension G) (g : ℕ), SmoothOfRelativeDimension g G.hom → (letI := E.addCommGroup; Module.finrank ℤ E.X) ≤ g := by
  first | exact @GlobalTheory.finrank_torusExtension_le | exact GlobalTheory.finrank_torusExtension_le | (intros; apply GlobalTheory.finrank_torusExtension_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumLinePlacewiseSignaturesStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_vacuum_line_placewise_signatures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → ∀ (f₀ : SInf F κ) (ε : InfinitePlace F → ℤˣ),
    (∀ u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u → At (evI F) u' → ∀ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) →
      ∀ f f' : SInf F κ, SD (fun t => d.rho ψ (realAd F t • u)) f₀ f → SD (fun t => d.rho ψ (realAd F t • u')) f₀ f' →
        f' = Complex.I • f) →
    ∃ z : ℂ, f₀ = z • Φ (PiTensorProduct.tprod ℂ fun _ => 1) := by
  first | exact @GlobalTheory.HoweD.vacLineD | exact GlobalTheory.HoweD.vacLineD | (intros; apply GlobalTheory.HoweD.vacLineD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalSquaringPathsBaseChangeAndHom
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem path_bc_ring {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] {R' : Type} [CommRing R']
    (φ : R →+* R') (c : R) (u : R') (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left) (h : IsPath G c b ξ) :
    IsPath G (φ c) (spMap φ ≫ b) (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) := by
  have hC : ((PowerSeries.rescale u).comp (PowerSeries.map φ)).comp (PowerSeries.C (R := R)) =
      (PowerSeries.C (R := R')).comp φ := by
    ext a n
    simp [PowerSeries.coeff_C]
    split_ifs <;> simp_all
  have h0 : (PowerSeries.constantCoeff (R := R')).comp ((PowerSeries.rescale u).comp (PowerSeries.map φ)) =
      φ.comp (PowerSeries.constantCoeff (R := R)) := by
    ext p
    simp only [RingHom.comp_apply]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale, PowerSeries.coeff_map]
    simp
  have hs : (PowerSeries.rescale (φ c)).comp ((PowerSeries.rescale u).comp (PowerSeries.map φ)) =
      ((PowerSeries.rescale u).comp (PowerSeries.map φ)).comp (PowerSeries.rescale c) := by
    ext p n
    simp [PowerSeries.coeff_rescale, PowerSeries.coeff_map]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [Category.assoc, h.base, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hC,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h0, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, h.zero, Category.assoc]
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hs, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc, h.scale, Category.assoc]

theorem unitSec_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] :
    unitSec G ≫ q.left = unitSec H := by
  show (η[G]).left ≫ q.left = (η[H]).left
  rw [← Over.comp_left, IsMonHom.one_hom]

theorem sqr_comp {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] :
    sqr G ≫ q.left = q.left ≫ sqr H := by
  unfold sqr
  rw [← Over.comp_left, ← Over.comp_left, MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id]

end GlobalTheory.Nef

theorem GlobalTheory.Nef.paths_bc : (∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (c : R) (u : R') (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), IsPath G c b ξ → IsPath G (φ c) (spMap φ ≫ b) (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) ∧ ∀ [IsLocalRing R] (n : ℕ) (V : S.Opens) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), ⊤ ≤ b ⁻¹ᵁ V → ∀ (U : G.left.Opens) (hU : ⊤ ≤ ξ ⁻¹ᵁ U), HasTan G b ξ τ w → ∀ (hU' : ⊤ ≤ (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hb : ⊤ ≤ b ⁻¹ᵁ V') (f : Γ(G.left, U)), PowerSeries.coeff 1 (evAt (spMap ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ≫ ξ) hU' f) = ∑ i, u * φ (w i) * φ (evAt b hb (dualApp (τ i) hV (dUnit G he f)))) ∧ (∀ (S : Scheme.{0}) (G H : Over S) [GrpObj G] [GrpObj H] (q : G ⟶ H) [IsMonHom q] (R : Type) [CommRing R] (c : R) (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left), (IsPath G c b ξ → IsPath H c b (ξ ≫ q.left)) ∧ triv G b ≫ q.left = triv H b ∧ sqr G ≫ q.left = q.left ≫ sqr H) := by
  refine ⟨?_, ?_⟩
  · intro S G _ R _ R' _ φ c u b ξ h
    refine ⟨path_bc_ring G φ c u b ξ h, ?_⟩
    intro _ n V τ w _ U hU ht hU' V' hV he hb f
    rw [(_root_.GlobalTheory.Nef.evAt_calculus).1 (PowerSeries R) (PowerSeries R') G.left ((PowerSeries.rescale u).comp (PowerSeries.map φ)) ξ U hU hU' f]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.comp_apply, PowerSeries.coeff_rescale, PowerSeries.coeff_map, ht U hU V' hV he hb f, map_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, pow_one, ← _root_.mul_assoc]
  · intro S G H _ _ q _ R _ c b ξ
    refine ⟨fun h => ⟨?_, ?_, ?_⟩, ?_, sqr_comp q⟩
    · rw [Category.assoc, Over.w q, h.base]
    · rw [← Category.assoc, h.zero, Category.assoc, unitSec_comp]
    · rw [← Category.assoc, h.scale, Category.assoc, Category.assoc, sqr_comp]
    · rw [triv, Category.assoc, Category.assoc, unitSec_comp, triv]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedStr
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

namespace GlobalTheory.CompHS.Modif

theorem geometricallyConnected_str : ∀ (F : Type) [Field F] (Y : Scheme.{0}) (p : Y ⟶ Sp F) (U : Y.Opens) (D : ℕ)
    (M : Modif p U D), SmoothOfRelativeDimension D p → GeometricallyConnected p → Dense (U : Set Y) →
    GeometricallyConnected M.str := by
  intro F _ Y p U D M hs hc hd
  have : Smooth p := SmoothOfRelativeDimension.smooth D p
  have : GeometricallyIntegral p := GlobalTheory.geometricallyIntegral_of_smooth p
  have : Nonempty Y := by
    obtain ⟨x⟩ := (inferInstance : Nonempty (Sp F))
    obtain ⟨y, -⟩ := p.surjective x
    exact ⟨y⟩
  obtain ⟨u, hu⟩ := hd.nonempty
  have : Surjective (U.ι ≫ p) := ⟨fun x => ⟨⟨u, hu⟩, Subsingleton.elim _ _⟩⟩
  have hU : GeometricallyIrreducible (U.ι ≫ p) := inferInstance
  have : IsIso (M.σ ∣_ U) := M.iso
  have e : M.opn.ι ≫ M.str = (M.σ ∣_ U) ≫ (U.ι ≫ p) := by
    show (M.opn.ι ≫ M.σ) ≫ p = _
    rw [← morphismRestrict_ι, Category.assoc]
  have hO : GeometricallyIrreducible (M.opn.ι ≫ M.str) := by
    have sq : IsPullback (M.σ ∣_ U) (M.opn.ι ≫ M.str) (U.ι ≫ p) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [e, Category.comp_id]⟩
    exact MorphismProperty.of_isPullback sq hU
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  have hy : UniversallyOpen y := inferInstance
  have hf : UniversallyOpen fst := MorphismProperty.of_isPullback h.flip hy
  have hdense : Dense ((fst ⁻¹ᵁ M.opn : Z.Opens) : Set Z) := M.dense.preimage fst.isOpenMap
  have hsq : IsPullback (fst ∣_ M.opn) ((fst ⁻¹ᵁ M.opn).ι ≫ snd) (M.opn.ι ≫ M.str) y :=
    (isPullback_morphismRestrict fst M.opn).paste_vert h
  have : IrreducibleSpace (fst ⁻¹ᵁ M.opn) :=
    hO.geometrically_irreducibleSpace y _ _ hsq
  have hirr : IsIrreducible ((fst ⁻¹ᵁ M.opn : Z.Opens) : Set Z) := by
    have := (IrreducibleSpace.isIrreducible_univ (fst ⁻¹ᵁ M.opn)).image _
      (fst ⁻¹ᵁ M.opn).ι.continuous.continuousOn
    rwa [Set.image_univ, Scheme.Opens.range_ι] at this
  have : IrreducibleSpace Z := by
    have hc := hirr.closure
    rw [hdense.closure_eq] at hc
    exact irreducibleSpace_def Z |>.mpr hc
  exact (connectedSpace_iff_univ).mpr (IrreducibleSpace.isIrreducible_univ Z).isConnected

end GlobalTheory.CompHS.Modif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupSchemeSquaringCotangentEqTwo
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

private theorem eta_comp_mul_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : η[G] ≫ (𝟙 G * 𝟙 G) = η[G] := by
  rw [Hom.mul_def, ← Category.assoc, comp_lift, Category.comp_id]
  simpa using lift_comp_one_left (𝟙 _) η[G]

private theorem unitSec_comp_sqr {S : Scheme.{0}} (G : Over S) [GrpObj G] : unitSec G ≫ sqr G = unitSec G :=
  congrArg (·.left) (eta_comp_mul_self G)

theorem sqr_sub_two_mem : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], QuasiSeparated G.hom → ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)), StalkData G s π ε m → ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2 := by
  intro S G _ hqs s π ε m hd f hf
  haveI := hqs
  obtain ⟨hπ, hε, hm⟩ := _root_.GlobalTheory.Nef.stalkData_germ S G s π ε m hd
  have he : unitSec G ≫ G.hom = 𝟙 S := sec_hom η[G]
  obtain ⟨U₀, hU₀, g, rfl⟩ := G.left.presheaf.germ_exist f
  have hsq : sqr G (unitSec G s) = unitSec G s := by rw [← Scheme.Hom.comp_apply, unitSec_comp_sqr]
  have hb : G.hom (unitSec G s) = s := by rw [← Scheme.Hom.comp_apply, he]; rfl
  obtain ⟨U₁, hU₁, hs₁, -⟩ := QCoh.exists_affine_mem_le (U := (⊤ : S.Opens)) s trivial
  obtain ⟨W₁, hW₁, hx₁, k₁⟩ := QCoh.exists_affine_mem_le
    (U := U₀ ⊓ sqr G ⁻¹ᵁ U₀ ⊓ G.hom ⁻¹ᵁ U₁) (unitSec G s)
    ⟨⟨hU₀, show sqr G (unitSec G s) ∈ U₀ by rw [hsq]; exact hU₀⟩,
      show G.hom (unitSec G s) ∈ U₁ by rw [hb]; exact hs₁⟩
  obtain ⟨U, hsU, -, -, c⟩ := GlobalTheory.Conormal.exists_isChart_inf he hU₁ hW₁ (k₁.trans inf_le_right) hx₁
    (show s ∈ (⊤ : S.Opens) from trivial)
  have kW : W₁ ⊓ G.hom ⁻¹ᵁ U ≤ U₀ := inf_le_left.trans (k₁.trans (inf_le_left.trans inf_le_left))
  have kS : W₁ ⊓ G.hom ⁻¹ᵁ U ≤ sqr G ⁻¹ᵁ U₀ :=
    inf_le_left.trans (k₁.trans (inf_le_left.trans inf_le_right))
  have hxW : unitSec G s ∈ W₁ ⊓ G.hom ⁻¹ᵁ U := c.le hsU
  have hU0 : U ≤ unitSec G ⁻¹ᵁ U₀ := c.le.trans ((unitSec G).preimage_mono kW)

  have a1 := cotMap_d (𝟙 G * 𝟙 G) (eta_comp_mul_self G) hU0 c.le kS g
  have a2 := cotMap_d (𝟙 G) (Category.comp_id _) hU0 c.le kW g
  have hmul := cotMap_mul (x := 𝟙 G) (y := 𝟙 G) (Category.comp_id η[G]) (Category.comp_id η[G]) (eta_comp_mul_self G)
  have key : GlobalTheory.Conormal.d he c.le ((sqr G).appLE U₀ _ kS g) =
      GlobalTheory.Conormal.d he c.le (resG G.left kW g) + GlobalTheory.Conormal.d he c.le (resG G.left kW g) := by
    have := congrArg (fun φ => φ.app U (GlobalTheory.Conormal.d he hU0 g)) hmul
    simp only at this
    exact (a1.symm.trans this).trans (congrArg₂ (· + ·) a2 a2)
  letI := c.algebra
  let h : Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) := (sqr G).appLE U₀ _ kS g - (resG G.left kW g + resG G.left kW g)
  have hz : AugCot.d (c.aug he) h = 0 := (c.augCotEquiv he).injective (by
    rw [c.augCotEquiv_d he, map_zero, map_sub, map_add (f := _), key, sub_self])
  rw [AugCot.d_eq_zero_iff] at hz
  let gW := G.left.presheaf.germ (W₁ ⊓ G.hom ⁻¹ᵁ U) (unitSec G s) hxW
  have g1 : gW ((sqr G).appLE U₀ _ kS g) = m (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g) :=
    (hm U₀ hU₀ _ hxW kS g).symm
  have g2 : gW (resG G.left kW g) = G.left.presheaf.germ U₀ (unitSec G s) hU₀ g :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have gh : gW h = m (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g) -
      2 * G.left.presheaf.germ U₀ (unitSec G s) hU₀ g := by
    simp only [h, map_sub, map_add (f := _), g1, g2, two_mul]
  have hf0 : ε (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g) = 0 := hf
  have hker : ∀ x, c.aug he x = 0 → ε (gW x) = 0 := by
    intro x hx
    have hx' : (unitSec G).appLE _ U c.le x = 0 := hx
    rw [hε _ hxW U hsU c.le x, hx', map_zero]
  have hmap : ∀ y ∈ RingHom.ker (c.aug he) ^ 2, gW y ∈ RingHom.ker ε ^ 2 := by
    intro y hy
    have := Ideal.mem_map_of_mem (ConcreteCategory.hom gW) hy
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_comap.2 (RingHom.mem_ker.2 (hker x (RingHom.mem_ker.1 hx)))) 2 this
  have hεm : ε (m (G.left.presheaf.germ U₀ (unitSec G s) hU₀ g)) = 0 := by
    rw [← g1, hε _ hxW U hsU c.le, GlobalTheory.Conormal.appLE_appLE (unitSec_comp_sqr G) kS c.le hU0,
      ← hε U₀ hU₀ U hsU hU0 g, hf0]
  have hεh : ε (gW h) = 0 := by rw [gh, map_sub, map_mul, hεm, hf0, mul_zero, sub_zero]
  have halg : gW (algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) = 0 := by
    have e1 : gW (algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) =
        π (S.presheaf.germ U s hsU (c.aug he h)) := (hπ U hsU _ hxW c.le_base _).symm
    have e2 : S.presheaf.germ U s hsU (c.aug he h) = ε (gW h) := (hε _ hxW U hsU c.le h).symm
    rw [e1, e2, hεh, map_zero]
  rw [← gh, show gW h = gW (h - algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) +
      gW (algebraMap Γ(S, U) Γ(G.left, W₁ ⊓ G.hom ⁻¹ᵁ U) (c.aug he h)) by rw [← map_add (f := _), sub_add_cancel],
    halg, add_zero]
  exact hmap _ hz
end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1VanishingAffineBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CxForm.firstCohomologyVanishes_of_isRelAcyclic_affine : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → CompactSpace X → GlobalTheory.CxForm.IsRelAcyclic f f M → GlobalTheory.AbLaw.FirstCohomologyVanishes M := by
  first
  | exact @_root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic
  | exact _root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic
  | (apply _root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic ..)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDifferentialOneFormCompHolomorphicStatement
section
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicDifferentialOneForm_comp_holomorphic : ∀ {n : ℕ} {φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n} {c : ReciprocityTheory.L2DbarEstimates.V n → ℂ} {v : ReciprocityTheory.L2DbarEstimates.V n}, DifferentiableAt ℝ c (φ v) → DifferentiableAt ℂ φ v → GlobalTheory.CxForm.DelForm.dOne (fun w => c (φ w)) v = GlobalTheory.CxForm.pull (fderiv ℂ φ v) (GlobalTheory.CxForm.DelForm.dOne c (φ v)) := by
  first | exact @GlobalTheory.CxForm.DelForm.dOne_comp_holo | exact GlobalTheory.CxForm.DelForm.dOne_comp_holo | (intros; apply GlobalTheory.CxForm.DelForm.dOne_comp_holo <;> assumption)
end

