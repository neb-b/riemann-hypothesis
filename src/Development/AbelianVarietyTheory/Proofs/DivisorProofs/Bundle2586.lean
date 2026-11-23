module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePointsCycAway
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIffEighthPowerPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectEighthPowerPrincipalSiegel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2519
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2485
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2491
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2562
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2563
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2468
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2504
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2305
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2505
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2431
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameTheoremOfCube
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2445
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2508
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerE8BundleIsoOfPrincipalSiegelIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull
open GlobalTheory.CechPic

noncomputable section

namespace GlobalTheory.SharpIso

theorem iso_of_sRel : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N) (C : SiegPre g N (b.ζ : K) (𝟙 (Sp K))) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) (a : J → Matrix (Fin 8) (Fin 8) ℤ) (bas : (Fin (2 * (8 * g)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin g ⊕ Fin g → ℤ))) (t : TObj (8 * g) N J b (𝟙 (Sp K))) (Q : PolAV (Sp K)) (pr : Fin 8 → (Q.A ⟶ c.A)), (∀ u, IsMonHom (pr u)) → (∀ (T' : Over (Sp K)) (y : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ Q.A, ∀ u, x ≫ pr u = y u) → LBIso Q.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → SRel C c 0 0 (𝟙 _) → IsSharp W a bas t C → ∃ φ : t.A ≅ Q.A, IsMonHom φ.hom ∧ LBIso t.L (Q.L.pull φ.hom.left) := by
  intro g n N B _ ζ K _ s c b C W J a bas t Q pr hpr huniv hQ hrel hsharp
  obtain ⟨φ, hpb, ⟨φ₂, hsq, hP⟩, -⟩ := hrel
  obtain ⟨pr', hpr', huniv', ht, -, -⟩ := hsharp
  have w : φ ≫ c.A.hom = C.A.hom := by simpa using hpb.1.w
  let f : C.A ⟶ c.A := Over.homMk φ w
  haveI : IsIso φ := hpb.1.isIso_fst_of_isIso
  haveI : IsIso f := by
    have : IsIso ((Over.forget _).map f) := by simpa [f] using (inferInstance : IsIso φ)
    exact isIso_of_reflects_iso f (Over.forget _)
  haveI hf : IsMonHom f := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f
    (fun _ x y => GlobalTheory.AbelianLetters.mul_comp_of_isGrpPullback_id f hpb x y)
  obtain ⟨ψ, hψ, -⟩ := huniv t.A (fun u => pr' u ≫ f)
  obtain ⟨χ, hχ, -⟩ := huniv' Q.A (fun u => pr u ≫ inv f)
  have h1 : ψ ≫ χ = 𝟙 _ := (huniv' t.A pr').unique (fun u => by
      rw [Category.assoc, hχ, ← Category.assoc, hψ, Category.assoc, IsIso.hom_inv_id, Category.comp_id])
    (fun u => Category.id_comp _)
  have h2 : χ ≫ ψ = 𝟙 _ := (huniv Q.A pr).unique (fun u => by
      rw [Category.assoc, hψ, ← Category.assoc, hχ, Category.assoc, IsIso.inv_hom_id, Category.comp_id])
    (fun u => Category.id_comp _)
  have hm : ∀ u, IsMonHom (ψ ≫ pr u) := fun u => by
    rw [hψ]; haveI := hpr' u; infer_instance
  have hψm : IsMonHom ψ := by
    refine ⟨(huniv _ fun u => η[Q.A] ≫ pr u).unique (fun u => ?_) fun _ => rfl,
      (huniv _ fun u => μ[t.A] ≫ ψ ≫ pr u).unique (fun u => Category.assoc _ _ _) fun u => ?_⟩
    · have := hm u
      have := hpr u
      rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
    · have := hm u
      have := hpr u
      rw [Category.assoc, IsMonHom.mul_hom, IsMonHom.mul_hom, ← Category.assoc, tensorHom_comp_tensorHom]
  refine ⟨⟨ψ, χ, h1, h2⟩, hψm, ?_⟩
  have hsq' : Geo.Tor.IsSquare φ (f ⊗ₘ f).left :=
    ⟨by rw [← Over.comp_left, tensorHom_fst]; rfl, by rw [← Over.comp_left, tensorHom_snd]; rfl⟩
  obtain rfl := GlobalTheory.LamPull.isSquare_unique hsq hsq'
  have key : ∀ uv : Fin 8 × Fin 8, (lift (pr' uv.1) (pr' uv.2)).left ≫ (f ⊗ₘ f).left =
      ψ.left ≫ (lift (pr uv.1) (pr uv.2)).left := fun uv => by
    rw [← Over.comp_left, ← Over.comp_left, lift_map, comp_lift, hψ, hψ]
  rw [← cls_eq_iff t.isLB (pull_isLB Q.isLB _), (cls_eq_iff t.isLB (LB.isLB_linComb C.isLB _ _)).2 ht,
    cls_linComb C.isLB, (cls_eq_iff C.isLB (pull_isLB c.isLB _)).2 hP, cls_pull c.isLB,
    cls_pull Q.isLB, (cls_eq_iff Q.isLB (LB.isLB_linComb c.isLB _ _)).2 hQ, cls_linComb c.isLB]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, ← pull_comp, key]

end GlobalTheory.SharpIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerEndomorphismLatticeAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.E8Endomorphism

open GlobalTheory.Poinc.Sep.EndCompat

theorem lattice_of_charMap {X Y : Type} [AddCommGroup X] [AddCommGroup Y] (S a a' : Matrix (Fin 8) (Fin 8) ℤ)
    (hS : S.transpose = S) (hSa : S * a' = a.transpose * S) (c : Fin 8 → (X →+ Y)) (e : Y ≃+ (Fin 8 → X))
    (hT : ∀ y, ∑ v, c v (∑ u, S v u • e y u) = y) (h : Y →+ Y) (hh : ∀ u χ, h (c u χ) = ∑ v, a' u v • c v χ)
    (y : Y) : e (h y) = fun u => ∑ v, a u v • e y v := by
  have hM' : a'.transpose * S = S * a := by
    have := congrArg Matrix.transpose hSa
    rwa [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hS] at this
  have hM : ∀ w u, ∑ v, a' v w * S v u = ∑ x, S w x * a x u := fun w u => by
    have := congrFun (congrFun hM' w) u
    simpa [Matrix.mul_apply] using this
  have key : ∀ x : Fin 8 → X, ∑ v, c v (∑ u, S v u • x u) = e.symm x := by
    intro x
    conv_rhs => rw [← hT (e.symm x)]
    simp
  apply e.symm.injective
  rw [AddEquiv.symm_apply_apply, ← key]
  conv_lhs => rw [← hT y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_zsmul, hh, Finset.smul_sum, smul_smul]
  have L : ∀ f : Fin 8 → Fin 8 → Fin 8 → Y, ∑ v, ∑ u, ∑ w, f v u w = ∑ w, ∑ u, ∑ v, f v u w := fun f => by
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun u _ => Finset.sum_comm]
    rw [Finset.sum_comm]
  calc ∑ v, ∑ u, ∑ w, (S v u * a' v w) • c w (e y u)
      = ∑ w, ∑ u, ∑ v, (S v u * a' v w) • c w (e y u) := L (fun v u w => (S v u * a' v w) • c w (e y u))
    _ = ∑ w, ∑ u, (∑ v, a' v w * S v u) • c w (e y u) := by
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_smul]
        exact Finset.sum_congr rfl fun v _ => by rw [mul_comm]
    _ = ∑ w, ∑ u, (∑ x, S w x * a x u) • c w (e y u) := by simp only [hM]
    _ = ∑ w, ∑ x, ∑ u, (S w x * a x u) • c w (e y u) := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun u _ => Finset.sum_smul

theorem endU_lattice_adjoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ (a a' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ E' : GlobalTheory.UT.EndU U'.toUnifPre, (∀ u, E'.aA ≫ pr u = (List.ofFn fun v => pr v ^ a' u v).prod) → ∀ y, e (E'.h y) = fun u => ∑ v, a u v • e y v := by
  intro R _ _ _ hB hDVR G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniqA hL pG hpG hpGc c hc e he a a' haa' E' hE' y
  have hCN : GlobalTheory.TorRef.IsCN R := ⟨hB.1.1, hB.1.2.2.1, hB.1.2.2.2, hB.2⟩
  haveI : IsNoetherianRing R := hCN.1
  haveI : IsIntegrallyClosed R := hCN.2.1
  haveI := E'.homG
  haveI := U.gen_hom
  have hstep : ∀ u, E'.aG ≫ pG u = (List.ofFn fun v => pG v ^ a' u v).prod := by
    intro u
    haveI := hpG u
    have hR : IsMonHom (List.ofFn fun v => pG v ^ a' u v).prod := by
      refine isMonHom_of_mul _ fun T x z => ?_
      have key : ∀ w : T ⟶ G', w ≫ (List.ofFn fun v => pG v ^ a' u v).prod = ∏ v, (w ≫ pG v) ^ a' u v := fun w => by
        rw [← List.prod_ofFn]
        exact map_ofFn_prod (preH w) pG (a' u)
      rw [key, key, key, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      haveI := hpG v
      rw [MonObj.mul_comp, mul_zpow]
    obtain ⟨F0, -, huniq⟩ := GlobalTheory.semiAbelianHomExtension_holds.fractionField R (FractionRing R) G' G hG' hG
      ((Over.pullback (jK R)).map (E'.aG ≫ pG u))
    refine (huniq _ ⟨inferInstance, rfl⟩).trans (huniq _ ⟨hR, ?_⟩).symm
    rw [← cancel_mono U.gen.hom]
    have e1 : (Over.pullback (jK R)).map (E'.aG ≫ pG u) ≫ U.gen.hom =
        U'.gen.hom ≫ (List.ofFn fun v => pr v ^ a' u v).prod := by
      rw [Functor.map_comp, Category.assoc, hpGc u, ← Category.assoc, E'.ext, Category.assoc, hE' u]
    rw [e1]
    calc (Over.pullback (jK R)).map (List.ofFn fun v => pG v ^ a' u v).prod ≫ U.gen.hom
        = ((postH U.gen.hom U.gen_hom).comp (pullH (jK R) G' G)) (List.ofFn fun v => pG v ^ a' u v).prod := rfl
      _ = (List.ofFn fun v => ((postH U.gen.hom U.gen_hom).comp (pullH (jK R) G' G)) (pG v) ^ a' u v).prod :=
          map_ofFn_prod _ pG (a' u)
      _ = (List.ofFn fun v => preH U'.gen.hom (pr v) ^ a' u v).prod :=
          congrArg (fun z : Fin 8 → _ => (List.ofFn fun v => z v ^ a' u v).prod) (funext hpGc)
      _ = preH U'.gen.hom (List.ofFn fun v => pr v ^ a' u v).prod := (map_ofFn_prod _ pr (a' u)).symm
      _ = U'.gen.hom ≫ (List.ofFn fun v => pr v ^ a' u v).prod := rfl
  have hEC := GlobalTheory.Poinc.Eq8.endChar_endU R hCN D' A' G' hG' U' E'
  have hh := _root_.GlobalTheory.Poinc.MatChar.charMap_matrix R hCN D A G hG U D' A' G' hG' U' pG hpG c hc a' E'.aG E'.h E'.homG hEC hstep
  exact lattice_of_charMap (W + W.transpose) a a' (by rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm])
    haa' c e he E'.h hh y

end GlobalTheory.Poinc.E8Endomorphism
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFirstFactorThetaModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.SiegFactor.firstFactor : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (β : cycAway n →+* o) (S : ThetaSys o Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SysAt F W β S ρ u → ∀ (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZHOut ρ M U₀ EE) (U : M.Z.Opens) (c : U.toScheme ⟶ F.X), S.Over₀ M U₀ → OpenAt F β u M U c → ∃ (G : Over M.Z) (_ : GrpObj G) (e : pullback F.univ.A.hom c ⟶ G.left) (_ : IsCommMonObj G), IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧ IsGrpPullback ((Over.pullback c).obj F.univ.A) G U.ι e ∧ LBIso (hodge Zh.G S.g) (lbPow (hodge G g) 8) := by
  intro g n hg hn hodd F W hW o Ω _ _ _ _ β S ρ u hsys M U₀ EE Zh U c hO hOpen
  obtain ⟨-, -, hSg, ⟨c', hc'pb, pr, hpr, huniv, -⟩, -⟩ := hsys
  haveI : IsCommMonObj ρ.P.A := ρ.P.isAb.comm
  obtain ⟨inj, hinj, hinjpr, hsum⟩ := _root_.GlobalTheory.eighthPower_inj_exists ρ.P.A c'.A pr hpr huniv
  let E' : Fin 8 → Fin 8 → (ρ.P.A ⟶ ρ.P.A) := fun a b => pr a ≫ inj b
  have hE' : ∀ a b, IsMonHom (E' a b) := fun a b => by
    haveI := hpr a; haveI := hinj b; exact inferInstanceAs (IsMonHom (pr a ≫ inj b))
  have hrel' : ∀ a b c d, E' a b ≫ E' c d = if b = c then E' a d else 1 := by
    intro a b c d
    show (pr a ≫ inj b) ≫ pr c ≫ inj d = if b = c then pr a ≫ inj d else 1
    rw [Category.assoc, ← Category.assoc (inj b), hinjpr]
    split_ifs
    · rw [Category.id_comp]
    · haveI := hinj d; rw [MonObj.one_comp, MonObj.comp_one]
  haveI : AlgebraicGeometry.IsNoetherian M.Z := _root_.GlobalTheory.ratModel_isNoetherian_of_arithBase M
  have hdense : Dense (U₀ : Set M.Z) := U₀.isOpen.dense hO.ne
  obtain ⟨E, hE, hrel, hsumE, hcompat⟩ := _root_.GlobalTheory.EighthPowerUnits.exists_matrixUnits_extend hO.normal U₀ hdense Zh.G Zh.semi
    ((Over.pullback Zh.u₀).obj ρ.P.A) ρ.P.A Zh.u₀ Zh.φ (pullback.fst _ _) Zh.cart (isGrpPullback_pullback _ _)
    E' hE' hrel' hsum
  have hidem : E 0 0 ≫ E 0 0 = E 0 0 := by rw [hrel]; simp
  obtain ⟨H, _, i, r, hi, hr, hir, hri, hH⟩ := _root_.GlobalTheory.SiegMin.exists_semiAbelian_idempotent_image M.Z Zh.G Zh.semi (E 0 0) (hE 0 0) hidem
  haveI : IsCommMonObj H := hH.comm
  have huniv8 := _root_.GlobalTheory.matUnits_univ_of_idem Zh.G H E hE hrel hsumE i r hi hr hir hri
  have hpr8 : ∀ a, IsMonHom (E a 0 ≫ r) := fun a => by
    haveI := hE a 0; haveI := hr; exact inferInstanceAs (IsMonHom (E a 0 ≫ r))
  have hdimG : SmoothOfRelativeDimension (8 * g) Zh.G.hom := hSg ▸ Zh.dim
  have hdim : SmoothOfRelativeDimension g H.hom := _root_.GlobalTheory.PowDim.smoothOfRelativeDimension_of_eighthPower H Zh.G g (fun a => E a 0 ≫ r) huniv8 hH hdimG
  have hhodge := _root_.GlobalTheory.HodgePow.hodge_eight_mul_iso_hodge_pow_eight M.Z H Zh.G g (fun a => E a 0 ≫ r) hpr8 huniv8 hH hdim
  obtain ⟨e', he'm, h1, h2⟩ := hcompat 0 0
  obtain ⟨C', _, a, b, ha, hb⟩ := _root_.GlobalTheory.RetractPullback.exists_isGrpPullback_of_retracts U₀.ι Zh.u₀ Zh.G ((Over.pullback Zh.u₀).obj ρ.P.A) ρ.P.A Zh.φ
    (pullback.fst _ _) Zh.cart (isGrpPullback_pullback _ _) (E 0 0) (E' 0 0) e' he'm h1 h2 H i r hi hr hir hri
    c'.A (inj 0) (pr 0) (hinj 0) (hpr 0) (by simpa using hinjpr 0 0) rfl
  obtain ⟨φ', φ₂, hφ', -, -, -⟩ := hc'pb
  obtain ⟨e, he⟩ := _root_.GlobalTheory.FactorOverOpen.factor_over_open hO.normal (_root_.GlobalTheory.SepSiegel.isSeparated_toZ F) F.univ.A F.univ.ab H hH U₀ U hO.ne hOpen.1
    (Zh.u₀ ≫ u) c C' a (b ≫ φ') ha (hb.comp hφ') Ω M.pt M.gen (fun x y hx hy => by
      rw [hOpen.2.2.2.2 x hx, ← Category.assoc, Zh.u₀_gen y hy])
  refine ⟨H, inferInstance, e, inferInstance, hH, hdim, he, ?_⟩
  rw [hSg]
  exact hhodge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsExtendUniformisedGroups
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

def matAddEquiv {M : Type*} [AddCommGroup M] (S : Matrix (Fin 8) (Fin 8) ℤ) (hS : S.det = 1) :
    (Fin 8 → M) ≃+ (Fin 8 → M) where
  toFun w v := ∑ u, S v u • w u
  invFun w v := ∑ u, S.adjugate v u • w u
  left_inv w := by
    funext v
    have h : S.adjugate * S = 1 := by rw [Matrix.adjugate_mul, hS, one_smul]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  right_inv w := by
    funext v
    have h : S * S.adjugate = 1 := by rw [Matrix.mul_adjugate, hS, one_smul]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Matrix.mul_apply, h, Matrix.one_apply, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  map_add' x y := by
    funext v
    simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

def sumChars {X X' : Type*} [AddCommGroup X] [AddCommGroup X'] (c : Fin 8 → (X →+ X')) : (Fin 8 → X) →+ X' where
  toFun y := ∑ v, c v (y v)
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

theorem e8data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∃ (pG : Fin 8 → (G' ⟶ G)) (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)) (e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X)), (∀ v, IsMonHom (pG v)) ∧ (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) ∧ (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) ∧ ∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y := by
  intro R _ _ _ hR hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL
  haveI := hdvr
  haveI := U.gen_hom
  haveI := U'.gen_hom
  have hpG : ∀ v, ∃ F : G' ⟶ G, IsMonHom F ∧
      (Over.pullback (jK R)).map F = U'.gen.hom ≫ pr v ≫ U.gen.inv := by
    intro v
    haveI := hpr v
    obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelian_hom_extends_uniquely_dvr R (FractionRing R) G' G hG' hG
      (U'.gen.hom ≫ pr v ≫ U.gen.inv) inferInstance
    exact ⟨F, hF, hF'⟩
  choose pG hpGm hpGg using hpG
  have hgen : ∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v := by
    intro v
    rw [hpGg v]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  choose c hc using fun v =>
    GlobalTheory.Poinc.HomTor.exists_torMatch R hR G hG D A U G' hG' D' A' U' (pG v) (hpGm v)
  have hbij := (characters_eighthPower_elementaryMatrices R hR hdvr G hG D A U G' hG' D' A' U' W hW pr hpr huniv hL pG hpGm hgen c hc).1
  let Φ := AddEquiv.ofBijective (sumChars c) hbij
  let Sm := matAddEquiv (M := D.toPre.X) (W + W.transpose) hW.2
  refine ⟨pG, c, Φ.symm.trans Sm.symm, hpGm, hgen, hc, fun y => ?_⟩
  have h1 : Sm ((Φ.symm.trans Sm.symm) y) = Φ.symm y := by simp
  have h2 : Φ (Φ.symm y) = y := Φ.apply_symm_apply y
  rw [← h1] at h2
  exact h2

end GlobalTheory.Poinc.Eq8
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallApplyHodgePrimitiveEqZero
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PDivGroup

theorem eq_zero_of_forall_apply_psi_eq_zero :
    ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → LieExact A →
    ∀ (G : PDivGroup p R) (t : TorsionTower G A) (ψ : PrimitiveSubmodule A →ₗ[R] G.omega),
    (∀ c : PrimitiveSubmodule A, PtExt.IsCan t c.1 (G.rigOfOmega (ψ c))) →
    ∀ x : G.Lie, (∀ c, x (ψ c) = 0) → x = 0 := by
  intro p _ R _ N hN A _ hA hL G t ψ hψ x hx
  have : IsAdicComplete (Ideal.span {(p : R)}) R :=
    GlobalTheory.isAdicComplete_span_natCast_of_isNilpotent p R ⟨N, hN⟩
  obtain ⟨v, hv⟩ := exists_lieCorr_of_pow_eq_zero p R N hN A G t x
  obtain ⟨h, hh⟩ := hL.2 v hv.1

  have hFil : h ∈ Fil A := by
    rw [mem_Fil]
    intro f hf
    have hF : (⟨_, hf⟩ : primDR A) ∈ PrimitiveSubmodule A := by
      change Form.cl _ f ∈ F1 (A.hom ≫ 𝟙 _)
      rw [hodgeFiltration_eq_range]
      exact LinearMap.mem_range_self _ f
    rw [hh.2 f hf, ← lie_psi_cl_eq_tanVal p R N hN A hA G t ψ hψ f hf hF x v hv]
    exact hx _

  have hv1 : v = 1 := (hL.1 h).unique hh (isLieImage_one_iff.mpr hFil)
  subst hv1
  exact hv.unique_left TorsionTower.lieCorr_zero

end GlobalTheory.PDivGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFrobeniusPullbackCotangentModVerscStatement
section
open GlobalTheory GlobalTheory.PDiv

theorem _root_.GlobalTheory.T.exists_additive_frobeniusPullback_cotangent_mod_verschiebung
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K)
    (w : Cot K ((PDivGroup.frobTwist h G).A 1)) :
    ∃ (β : (PDivGroup.frobTwist h G).A 1) (w' : Cot K (G.A 1)),
      cobOne K (G.A 1) ((PDivGroup.relFrob h G).app 1 β) = 0 ∧
        dUnit (R := K) β = w + cotMap ((PDivGroup.verschiebung h G).app 1) w' :=
  PDivGroup.exists_cobOne_relFrob_eq_zero_dUnit_eq p K h G w
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumTwistedSectionFamilyTendsToZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adicSum_twistedSectionFamily_tendsToZero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (n j : ℤ) (Ix : Type) (w : Ix → D.toPre.X) (s : ∀ i, SecT D.toPre a n j (w i)), Small (maximalIdeal R) s → ∃ F : ∀ β, SecT D.toPre a n j β, IsSum (maximalIdeal R) s F ∧ Small (maximalIdeal R) (w := id) F := by
  first | exact @GlobalTheory.TwFam.AdicSum.exists_isSum | exact GlobalTheory.TwFam.AdicSum.exists_isSum | (intros; apply GlobalTheory.TwFam.AdicSum.exists_isSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenNormalNoetherianCharZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_normal_noetherian_charZero : ∀ (X : Scheme.{0}), Geo.Tor.IsNormalScheme X → IsLocallyNoetherian X → (∀ x : X, CharZero (X.residueField x)) → ∀ x : X,
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧ IsDomain Γ(X, U) ∧ IsNoetherianRing Γ(X, U) ∧ IsIntegrallyClosed Γ(X, U) ∧ CharZero Γ(X, U) := by
  first | exact @GlobalTheory.exists_affineOpen_isIntegrallyClosed_charZero | exact GlobalTheory.exists_affineOpen_isIntegrallyClosed_charZero | (intros; apply GlobalTheory.exists_affineOpen_isIntegrallyClosed_charZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseElementThetaTermIntegralPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_base_element_theta_term_integralPoint : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (θ : D.SecB 1 0) (g : GtPt D (𝟙_ (Over (Sp V)))) (g' : GtPtF D (FractionRing V)) (w : Frm D (FractionRing V) 1 g'.b) (l : FractionRing V), GtPt.IsPullF (FractionRing V) (toUnit (TF (R := V) (FractionRing V))).left g g' → IntTerm.IntFrm D g.b w l → ∀ (mu : D.X) (gam : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c mu).left) (fun _ => -1))), gam.IsGen → ∃ a : V, (∀ (z : (TF (R := V) (FractionRing V)).left) (J : ((TF (R := V) (FractionRing V)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing V) z l * (Geo.Tor.val gam (toUnit (TF (R := V) (FractionRing V))).left z J).val * sval θ (padd D.P.A (DegPre.cT D _ mu) g'.b).left z J * (Geo.Tor.val (g'.s mu) (𝟙 _) z J).val * (Geo.Tor.val w (𝟙 _) z J).val = GlobalTheory.UT.cst (FractionRing V) z (algebraMap V (FractionRing V) a)) ∧ (IntTerm.UnitAt D θ (D.c mu * g.b) → IsUnit (Geo.Tor.cst (𝟙 (Sp V)) (closedPoint V) a)) := by
  first | exact @GlobalTheory.Poinc.IntTerm.IntPoint.main | exact GlobalTheory.Poinc.IntTerm.IntPoint.main | (intros; apply GlobalTheory.Poinc.IntTerm.IntPoint.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCarriedFrameTheoremOfCubeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_carriedFrame_theoremOfCube : ∀ {S : Scheme.{0}} (G' : Over S) [GrpObj G'] [IsCommMonObj G'] (L : RigLB G') (c : CubicalStr G' L) (θ : L.L.Sec) (T : Over S) (x a b c' : T ⟶ G') (W : T.left.Opens), (∀ g ∈ cubeTen x a b c', W ≤ g.left ⁻¹ᵁ secNz θ) → ∃ τ : ∀ k : L.L.ι, Γ(T.left, W ⊓ x.left ⁻¹ᵁ L.L.U k)ˣ, FrameAlong L.L x.left W τ ∧ ∀ (f : G'.left ⟶ G'.left) (fS : S ⟶ S) (hc : IsGrpPullback G' G' fS f) (w : LB.Iso L.L (L.L.pull f)), w.IsGen → PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G') (fun _ => 1) L.rig L.rig fS → PMaps w (thφ G' (x3 G')) (thφ G' (x3 G')) thε c.t c.t (cubeMapOf hc).F3 → SecCarried L.L θ f w → ∀ hT : T.left ⟶ T.left, hT ≫ T.hom = T.hom ≫ fS → x.left ≫ f = hT ≫ x.left → a.left ≫ f = hT ≫ a.left → b.left ≫ f = hT ≫ b.left → c'.left ≫ f = hT ≫ c'.left → FrameCarriedAlong L.L x.left W τ f w hT := by
  first | exact @GlobalTheory.Mum.exists_carried_frame_of_cubeTen | exact GlobalTheory.Mum.exists_carried_frame_of_cubeTen | (intros; apply GlobalTheory.Mum.exists_carried_frame_of_cubeTen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDeeperPointIntegralClosureGaloisStalkStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deeperPoint_integralClosure_galois_stalk : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (𝔗 : Tower X₁ act) (z₁ : X₁.M.Z), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ := ((algebraMap X₁.Ω₁ 𝔗.X₂.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra; ∃ (z₂ : 𝔗.X₂.M.Z) (j₂ : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁ →+* 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.p z₂ = z₁ ∧ (∀ b, 𝔗.X₂.M.stalkHom z₂ (j₂ b) = b) ∧ ((maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂)).comap j₂).IsMaximal ∧ (∀ x : 𝔗.X₂.Ω₁, (∀ w, 𝔗.p w = z₁ → x ∈ 𝔗.X₂.M.O w) → x ∈ integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁) ∧ (∀ σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁, (∀ b b' : integralClosure (X₁.M.Z.presheaf.stalk z₁) 𝔗.X₂.Ω₁, (b' : 𝔗.X₂.Ω₁) = σ b → (j₂ b ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂) ↔ j₂ b' ∈ maximalIdeal (𝔗.X₂.M.Z.presheaf.stalk z₂))) → ∃ σ₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ ≃+* 𝔗.X₂.M.Z.presheaf.stalk z₂, ∀ x, 𝔗.X₂.M.stalkHom z₂ (σ₂ x) = σ (𝔗.X₂.M.stalkHom z₂ x)) ∧ ∀ (V : Type) [CommRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (V' : Type) [CommRing V'] (io : V →+* V') (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V'), Function.Injective ev → Function.Injective io → 𝔗.Ext ev io ev₂ → Function.Injective ev₂ := by
  first | exact @GlobalTheory.Poinc.Sep.Tower.exists_point_integralClosure_stalk | exact GlobalTheory.Poinc.Sep.Tower.exists_point_integralClosure_stalk | (intros; apply GlobalTheory.Poinc.Sep.Tower.exists_point_integralClosure_stalk <;> assumption)
end

