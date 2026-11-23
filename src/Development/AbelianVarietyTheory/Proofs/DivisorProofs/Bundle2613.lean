module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqProdOfMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2551
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoPeriodsFactorTensorPolarised
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2558
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2187

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativePolynomialFunctionEqNormForm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulPolyNorm

open Polynomial GlobalTheory.PolyNorm

theorem eq_prod_aroots : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (d : ℕ) (δ : Polynomial ℤ → ℚ) (P : Polynomial ℚ), (∀ F G, δ (F * G) = δ F * δ G) → (∀ (n : ℕ) (u : Fin n → Polynomial ℤ), ∃ Φ : MvPolynomial (Fin n) ℚ, Φ.IsHomogeneous (2 * d) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) Φ = δ (∑ i, m i • u i)) → P.Monic → P.natDegree = 2 * d → (∀ n : ℤ, P.eval (n : ℚ) = δ (Polynomial.C n - Polynomial.X)) → ∀ F : Polynomial ℤ, algebraMap ℚ Ω (δ F) = ((P.aroots Ω).map (fun a => Polynomial.aeval a F)).prod := by
  intro Ω _ _ _ d δ P hm hΦ0 hP hPd hPe
  choose Φ hh hΦ using fun r : ℕ => hΦ0 r (fun i : Fin r => (X : ℤ[X]) ^ (i : ℕ))
  have hN : ∀ r (F : ℤ[X]), F.natDegree < r → δ F = ev (Φ r) (F.map (Int.castRingHom ℚ)) := by
    intro r F hF
    have := hΦ r fun i => F.coeff i
    have e : ∑ i : Fin r, F.coeff i • (X : ℤ[X]) ^ (i : ℕ) = F := by
      conv_rhs => rw [← gen_coeff F hF]
      unfold gen
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_C_mul, C_mul_X_pow_eq_monomial]
    rw [e] at this
    rw [← this]
    simp [ev, MvPolynomial.aeval_eq_eval]
  have h11 : δ 1 = δ 1 * δ 1 := by rw [← hm, _root_.one_mul]
  have h1 : δ 1 = 1 := by
    by_contra hne
    have h0 : δ 1 = 0 := by
      have : δ 1 * (δ 1 - 1) = 0 := by rw [mul_sub, ← h11]; ring
      rcases mul_eq_zero.1 this with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) hne
    have hP0 : P = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine Set.Infinite.mono (s := Set.range (Int.cast : ℤ → ℚ)) ?_
        (Set.infinite_range_of_injective Int.cast_injective)
      rintro _ ⟨n, rfl⟩
      simp only [Set.mem_setOf_eq, IsRoot.def]
      rw [hPe, ← _root_.one_mul (C n - Polynomial.X : ℤ[X]), hm, h0, zero_mul]
    exact hP.ne_zero hP0
  obtain ⟨M, hM⟩ := exists_ext δ Φ hN h1 hm Ω
  have hPP : ev (Φ 2) (C Polynomial.X - Polynomial.X : ℚ[X][X]) = P := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := Set.range (Int.cast : ℤ → ℚ)) ?_
      (Set.infinite_range_of_injective Int.cast_injective)
    rintro _ ⟨n, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [hPe, hN 2 _ (lt_of_le_of_lt (natDegree_sub_le _ _) (by simp)), ← coe_evalRingHom, ev_map]
    congr 1
    simp
  have ha : P.map (algebraMap ℚ Ω) = ((P.aroots Ω).map fun x => Polynomial.X - C x).prod :=
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hP.map _)
      IsAlgClosed.card_roots_eq_natDegree).symm
  have hac : Multiset.card (P.aroots Ω) = 2 * d := by
    rw [aroots_def, IsAlgClosed.card_roots_eq_natDegree, hP.natDegree_map, hPd]
  have hMa : ∀ F, M F = ((P.aroots Ω).map fun x => F.eval x).prod := by
    refine eq_prod_of_mul M (P.aroots Ω) (fun c => ?_) (fun β => ?_)
    · rw [hM 1 _ (by simp), ← _root_.mul_one (C c), ev_homog (hh 1), ev_one δ Φ hN h1, _root_.mul_one, hac]
    · have := congrArg (eval β) ha
      rw [Polynomial.eval_multiset_prod, Multiset.map_map, Polynomial.eval_map, ← coe_eval₂RingHom, ← hPP,
        ev_map, hPP] at this
      rw [hM 2]
      · simpa using this
      · exact lt_of_le_of_lt (natDegree_sub_le _ _) (by simp)
  intro F
  have := hMa (F.map (algebraMap ℤ Ω))
  simp only [eval_map_algebraMap] at this
  rw [← this, hM (F.natDegree + 1) _ (Nat.lt_succ_of_le natDegree_map_le),
    hN _ F (Nat.lt_succ_self _), ev_map, Polynomial.map_map]
  congr 2
  exact RingHom.ext_int _ _

end GlobalTheory.MulPolyNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleAdjointOfGenericAdjoint
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

namespace GlobalTheory.PoincAdj

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend GlobalTheory.UT GlobalTheory.Mum.Two

theorem lbIso_adj_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (E E' : GlobalTheory.UT.EndU U.toUnifPre), LBIso (cubeLB A.A ![fst A.A A.A ≫ E.aA, snd A.A A.A] A.L) (cubeLB A.A ![fst A.A A.A, snd A.A A.A ≫ E'.aA] A.L) → LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) := by
  intro R _ _ _ hB G _ _ hS D A U E E' hA
  have hR : AdmBase R (maximalIdeal R) := hB.1
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  haveI := hS.smooth
  haveI := hS.geomConnected
  haveI := GlobalTheory.smooth_tensorObj_hom G G
  haveI := GlobalTheory.geometricallyIntegral_tensorObj_hom G G
  let U₁ := U.toUnifPre
  let δ := CartesianMonoidalCategory.prodComparison (Over.pullback (jK R)) G G
  let u := lift (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U₁.gen.hom)
    (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U₁.gen.hom)
  have hL := U₁.LG.isLB
  have hAL := A.isLB
  have hgen := U₁.gen_hom
  have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U₁.LG.L hL) =
      CechPic.pull U₁.gen.hom.left (cls A.L hAL) := by
    obtain ⟨w, hw⟩ := U₁.ext
    rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hAL _ (pull_isLB hAL _)]
    exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm
  have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
      ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
    fun q => pullback.lift_fst _ _ _
  have hu : u.left ≫ (A.A ⊗ A.A).hom =
      ((Over.pullback (jK R)).obj G ⊗ (Over.pullback (jK R)).obj G).hom ≫ 𝟙 _ := by
    rw [Category.comp_id]; exact Over.w u
  have key : ∀ (x y : G ⟶ G) (cx cy : A.A ⟶ A.A), Gen₀ U₁ U₁ x cx → Gen₀ U₁ U₁ y cy →
      CechPic.pull (pullback.fst (G ⊗ G).hom (jK R)) (cubeCls G ![fst G G ≫ x, snd G G ≫ y] (cls U₁.LG.L hL)) =
        CechPic.pull δ.left (CechPic.pull u.left
          (cubeCls A.A ![fst A.A A.A ≫ cx, snd A.A A.A ≫ cy] (cls A.L hAL))) := by
    intro x y cx cy hx hy
    have e' := push_cubeCls (isGrpPullback_pullback G (jK R)) (T' := (Over.pullback (jK R)).obj (G ⊗ G))
      (T := G ⊗ G) (fun i => (Over.pullback (jK R)).map (![fst G G ≫ x, snd G G ≫ y] i))
      ![fst G G ≫ x, snd G G ≫ y] (pullback.fst (G ⊗ G).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U₁.LG.L hL)
    refine e'.trans ((pull_cubeCls _ ![fst _ _ ≫ (Over.pullback (jK R)).map x,
      snd _ _ ≫ (Over.pullback (jK R)).map y] _ δ (fun i => ?_) _).symm.trans ?_)
    · fin_cases i <;> simp [δ]
    rw [hc']
    refine congrArg (CechPic.pull δ.left) (push_cubeCls (isGrpPullback_of_iso U₁.gen) _ _ u.left hu (fun i => ?_) _).symm
    fin_cases i
    · show ((fst _ _ ≫ (Over.pullback (jK R)).map x) ≫ U₁.gen.hom).left = (u ≫ fst A.A A.A ≫ cx).left
      congr 1
      simp only [u, Category.assoc, lift_fst_assoc]
      rw [hx]
    · show ((snd _ _ ≫ (Over.pullback (jK R)).map y) ≫ U₁.gen.hom).left = (u ≫ snd A.A A.A ≫ cy).left
      congr 1
      simp only [u, Category.assoc, lift_snd_assoc]
      rw [hy]
  have g₁ : Gen₀ U₁ U₁ (𝟙 G) (𝟙 A.A) := by
    unfold Gen₀; rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  have k₁ := key E.aG (𝟙 G) E.aA (𝟙 A.A) E.ext g₁
  have k₂ := key (𝟙 G) E'.aG (𝟙 A.A) E'.aA g₁ E'.ext
  simp only [Category.comp_id] at k₁ k₂
  have eA : cubeCls A.A ![fst A.A A.A ≫ E.aA, snd A.A A.A] (cls _ hAL) =
      cubeCls A.A ![fst A.A A.A, snd A.A A.A ≫ E'.aA] (cls _ hAL) :=
    (cls_cubeLB A.A _ hAL).symm.trans (((cls_eq_iff _ _).2 hA).trans (cls_cubeLB A.A _ hAL))
  refine GlobalTheory.Mum.lbIso_of_generic_local R (G ⊗ G) (η[G ⊗ G]).left (Over.w _) _ _ (LB.isLB_linComb hL _ _)
    (LB.isLB_linComb hL _ _) ?_
  refine (cls_eq_iff (pull_isLB (LB.isLB_linComb hL _ _) _) (pull_isLB (LB.isLB_linComb hL _ _) _)).1 ?_
  rw [cls_pull (LB.isLB_linComb hL _ _) _ (pull_isLB (LB.isLB_linComb hL _ _) _),
    cls_pull (LB.isLB_linComb hL _ _) _ (pull_isLB (LB.isLB_linComb hL _ _) _)]
  refine (congrArg (CechPic.pull _) (cls_cubeLB G ![fst G G ≫ E.aG, snd G G] hL)).trans ?_
  refine Eq.trans ?_ (congrArg (CechPic.pull _) (cls_cubeLB G ![fst G G, snd G G ≫ E'.aG] hL)).symm
  rw [k₁, k₂, eA]

end GlobalTheory.PoincAdj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoEqOneAlongAxes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem lamVal_axes_one : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (Z : Over (Sp V)) (y : Z ⟶ D.P.A) (z : Z.left) J J', Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (1 : Z ⟶ D.P.A) y).left z J J' = 1 ∧ lamVal w (lift y (1 : Z ⟶ D.P.A)).left z J J' = 1 := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hB hF Z y z J J' hJ hJ'
  letI := D.P.isAb.comm
  have hpb := hF.1
  have hsq := hF.2.1
  have hw := hF.2.2.1
  have N := _root_.GlobalTheory.GenOrigin.lamVal_origin_of_generic T.B D.P.A T.M.L D.P.L T.M.isLB D.P.isLB (spMap ω) β ββ w hpb hsq hw
    (_root_.GlobalTheory.TInj.lamVal_origin_of_from T ε n V D ω s e β ββ w hB hF)
  exact ⟨_root_.GlobalTheory.MumRigidZeroPull.lamVal_one_left_pull T.B D.P.A T.M.L D.P.L T.M.isLB D.P.isLB D.P.isAb (spMap ω) β ββ w hpb hsq hw N Z y z J J' hJ hJ',
    _root_.GlobalTheory.MumRigidZero.lamVal_one_right_base T.B D.P.A T.M.L D.P.L T.M.isLB D.P.isLB D.P.isAb (spMap ω) β ββ w hpb hsq hw N Z y z J J' hJ hJ'⟩

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoFamilyIffLocallyTrivialTranslati
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TwistFlat

theorem pull_cls_translDiff_div {S : Scheme.{0}} {A T Y Z : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}
    (hL : L.IsLB) (hP : (abelian₂ A L).IsLB) {N : LB (A ⊗ T).left} (hN : N.IsLB) (a : Y ⟶ A) (t : Y ⟶ T)
    (hD : (LB.div (translDiff A L a) (ev N (snd Y A) (fst Y A ≫ t))).IsLB) (s : Z ⟶ Y) (u : Z ⟶ A) :
    CechPic.pull (lift s u).left (cls _ hD) = evc hP u (s ≫ a) - evc hN u (s ≫ t) +
      CechPic.pull s.left (CechPic.pull a.left (cls L hL) - CechPic.pull (1 : Y ⟶ A).left (cls L hL)) := by
  have hT : (translDiff A L a).IsLB := LB.isLB_linComb hL _ _
  rw [cls_div hT (pull_isLB hN _) hD, map_sub, GlobalTheory.AbDual.pull_translDiff hL a hT, cls_ev hN, pull_evc, lift_snd,
    lift_fst_assoc, GlobalTheory.CubeDual.evc_lam hL, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left,
    MonObj.comp_one, lam, _root_.mul_comm u (s ≫ a)]
  abel_nf

theorem same_lam_iff_locally_triv : ∀ {S : Scheme.{0}} (A T : Over S) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → ∀ (N : LB (A ⊗ T).left), Fam A N → ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∀ p : Y.left, ∃ U : Y.left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff A L a) (ev N (snd Y A) (fst Y A ≫ t))).pull ((fst Y A).left ⁻¹ᵁ U).ι) := by
  intro S A T _ hA L hL N hN Y a t
  haveI := hA.comm
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have hF : Fam A (abelian₂ A L) := ⟨hP, (GlobalTheory.CubeDual.isAdditive_lam GlobalTheory.CubeTop.cubeTheorem hA hL hP).1⟩
  have hT : (translDiff A L a).IsLB := LB.isLB_linComb hL _ _
  have hD : (LB.div (translDiff A L a) (ev N (snd Y A) (fst Y A ≫ t))).IsLB :=
    LB.isLB_div hT (pull_isLB hN.isLB _)
  constructor
  · intro h p
    obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
      (CechPic.pull a.left (cls L hL) - CechPic.pull (1 : Y ⟶ A).left (cls L hL)) p
    refine ⟨V, hV, (cls_eq_zero_iff (pull_isLB hD _)).1 ?_⟩
    have e₁ := pull_cls_translDiff_div hL hP hN.isLB a t hD (fst Y A) (snd Y A)
    rw [lift_fst_snd, Over.id_left, pull_id] at e₁
    have e₂ := congrArg (CechPic.pull (lift (snd Y A) (fst Y A)).left) ((same_iff hP hN.isLB a t).1 h)
    rw [pull_evc, pull_evc, lift_fst, lift_snd_assoc, lift_snd_assoc] at e₂
    rw [cls_pull hD, e₁, e₂, sub_self, zero_add, ← pull_comp]
    exact pull_eq_zero_of_mem V (((fst Y A).left ⁻¹ᵁ V).ι ≫ (fst Y A).left) (fun z ↦ z.2) hc
  · intro h
    refine same_of_local S A A T hA _ N hF hN Y a t fun p ↦ ?_
    obtain ⟨U, hU, hU'⟩ := h p
    obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero
      (CechPic.pull a.left (cls L hL) - CechPic.pull (1 : Y ⟶ A).left (cls L hL)) p
    let Z : Over S := Over.mk ((U ⊓ V).ι ≫ Y.hom)
    let z : Z ⟶ Y := Over.homMk (U ⊓ V).ι rfl
    refine ⟨Z, z, inferInstanceAs (IsOpenImmersion (U ⊓ V).ι), ⟨⟨p, hU, hV⟩, rfl⟩, ?_⟩
    rw [same_iff hP hN.isLB, ← sub_eq_zero]
    have hm : ∀ w, (snd A Z ≫ z).left w ∈ U ⊓ V := fun w ↦ ((snd A Z).left w).2
    have e₁ := pull_cls_translDiff_div hL hP hN.isLB a t hD (snd A Z ≫ z) (fst A Z)
    have z₀ : CechPic.pull ((fst Y A).left ⁻¹ᵁ U).ι (cls _ hD) = 0 := (cls_eq_zero_iff (pull_isLB hD _)).2 hU'
    have e : (lift (snd A Z ≫ z) (fst A Z)).left ≫ (fst Y A).left = (snd A Z ≫ z).left := by
      rw [← Over.comp_left, lift_fst]
    rw [pull_eq_zero_of_mem _ _ (fun w ↦ (congrArg (fun q ↦ q w ∈ U) e).mpr (hm w).1) z₀,
      pull_eq_zero_of_mem V _ (fun w ↦ (hm w).2) hc, add_zero, Category.assoc, Category.assoc] at e₁
    exact e₁.symm

end GlobalTheory.TwistFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleRetractOfAdjointPairs
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum GlobalTheory.MumFam

noncomputable section

open GlobalTheory.CechPic

namespace GlobalTheory.MumFam

theorem lbIso_lam_retract_adj : ∀ (S : Scheme.{0}) (G G' G₀ : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj G₀] [IsCommMonObj G₀] (L : LB G.left) (L' : LB G'.left) (L₀ : LB G₀.left), L.IsLB → L'.IsLB → L₀.IsLB → ∀ (inc : G ⟶ G') (u : G' ⟶ G₀) (u' : G₀ ⟶ G') (E E' Fm : G' ⟶ G'), IsMonHom inc → IsMonHom u → inc ≫ E = inc → u ≫ u' = E ≫ Fm ≫ E' → GAdj L' L₀ u u' → GAdj L' L' E E' → LBIso L (L₀.pull (inc ≫ u).left) → LBIso (abelian₂ G L) ((abelian₂ G' L').pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ Fm) : G2 G ⟶ G2 G').left) := by
  intro S G G' G₀ _ _ _ _ _ _ L L' L₀ hL hL' hL₀ inc u u' E E' Fm hinc hu hE huu hA hB hLL
  haveI := hinc
  haveI := hu
  have key : inc ≫ u ≫ u' = inc ≫ Fm ≫ E' := by
    rw [huu, ← Category.assoc inc E, hE]
  let P : G2 G ⟶ G2 G' := lift (fst G G ≫ inc) (snd G G ≫ inc ≫ Fm)
  let Q : G2 G ⟶ G' ⊗ G₀ := lift (fst G G ≫ inc) (snd G G ≫ inc ≫ u)
  have hLam : (abelian₂ G L).IsLB := LB.isLB_linComb hL _ _
  have hLam' : (abelian₂ G' L').IsLB := LB.isLB_linComb hL' _ _
  refine (cls_eq_iff hLam (pull_isLB hLam' _)).1 ?_
  rw [cls_pull hLam']
  have c1 : cls (abelian₂ G L) hLam =
      GlobalTheory.ZH.EndoExtend.cubeCls G₀ ![fst G G ≫ inc ≫ u, snd G G ≫ inc ≫ u] (cls L₀ hL₀) := by
    have e0 : cls L hL = CechPic.pull (inc ≫ u).left (cls L₀ hL₀) := (cls_eq_iff hL (pull_isLB hL₀ _)).2 hLL
    have hp : GlobalTheory.ZH.EndoExtend.cubeCls G (x2 G) (CechPic.pull (inc ≫ u).left (cls L₀ hL₀)) =
        GlobalTheory.ZH.EndoExtend.cubeCls G₀ (fun i => x2 G i ≫ (inc ≫ u)) (cls L₀ hL₀) := by
      unfold GlobalTheory.ZH.EndoExtend.cubeCls
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [← CechPic.pull_comp, ← Over.comp_left]
      have he := psum_hom (MonoidHom.mk' (fun z : G2 G ⟶ G => z ≫ (inc ≫ u))
        fun a b => MonObj.mul_comp a b (inc ≫ u)) (x2 G) I.down
      change psum G (x2 G) I.down ≫ (inc ≫ u) =
        psum G₀ (fun i => x2 G i ≫ (inc ≫ u)) I.down at he
      rw [he]
    rw [show cls (abelian₂ G L) hLam = GlobalTheory.ZH.EndoExtend.cubeCls G (x2 G) (cls L hL) from
      GlobalTheory.ZH.EndoExtend.cls_cubeLB G _ hL, e0, hp]
    congr 1
    ext i
    fin_cases i <;> simp [x2]
  have c2 : CechPic.pull P.left (cls (abelian₂ G' L') hLam') =
      GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm] (cls L' hL') := by
    rw [show cls (abelian₂ G' L') hLam' = GlobalTheory.ZH.EndoExtend.cubeCls G' (x2 G') (cls L' hL') from
      GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL']
    exact GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ _ _ (fun i => by fin_cases i <;> simp [x2, P]) _
  have a1 : GlobalTheory.ZH.EndoExtend.cubeCls G₀ ![fst G' G₀ ≫ u, snd G' G₀] (cls L₀ hL₀) =
      GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G' G₀, snd G' G₀ ≫ u'] (cls L' hL') :=
    (GlobalTheory.ZH.EndoExtend.cls_cubeLB G₀ _ hL₀).symm.trans
      (((cls_eq_iff _ _).2 hA).trans (GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL'))
  have b1 := congrArg (CechPic.pull Q.left) a1
  rw [GlobalTheory.ZH.EndoExtend.pull_cubeCls G₀ _ ![fst G G ≫ inc ≫ u, snd G G ≫ inc ≫ u] Q
      (fun i => by fin_cases i <;> simp [Q]),
    GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm ≫ E'] Q
      (fun i => by fin_cases i <;> simp [Q, key])] at b1
  have a2 : GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G' G' ≫ E, snd G' G'] (cls L' hL') =
      GlobalTheory.ZH.EndoExtend.cubeCls G' ![fst G' G', snd G' G' ≫ E'] (cls L' hL') :=
    (GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL').symm.trans
      (((cls_eq_iff _ _).2 hB).trans (GlobalTheory.ZH.EndoExtend.cls_cubeLB G' _ hL'))
  have b2 := congrArg (CechPic.pull P.left) a2
  rw [GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm] P
      (fun i => by fin_cases i <;> simp [P, hE]),
    GlobalTheory.ZH.EndoExtend.pull_cubeCls G' _ ![fst G G ≫ inc, snd G G ≫ inc ≫ Fm ≫ E'] P
      (fun i => by fin_cases i <;> simp [P])] at b2
  exact c1.trans (b1.trans (b2.symm.trans c2.symm))

end GlobalTheory.MumFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordIsoPeriodsFactorTensorPolarisedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordIso_periods_factor_tensor_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
    {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef →
    ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.toPre.P.A pr)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    ∀ i₀ : Fin r,
    letI := PowLim.mod xe (symUnitOf W h)
    ∃ w' : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ D'.toPre.P.A D'.toPre.P.L).pull
      (lift (fst Q.B Q.B ≫ PowLim.inc pr hl i₀) (snd Q.B Q.B ≫ PowLim.inc pr hl i₀ ≫
        PowLim.act pr hl (TensO.mat _ (TensO.binv (symUnitOf W h)))) : G2 Q.B ⟶ G2 D'.toPre.P.A).left),
      w'.IsGen ∧ ∀ a b z J J', Good D'.toPre.P.L z J → Good Q.M.L z J' →
        val (Q.tau a b) (𝟙 _) z J' =
          lamVal w' (lift (toUnit (TK R) ≫ Q.c a) (toUnit (TK R) ≫ Q.c b)).left z J J' *
            val (D'.toPre.tau (PowLim.xi xe i₀ a) (TensO.binv (symUnitOf W h) • PowLim.xi xe i₀ b)) (𝟙 _) z J := by
  first | exact @GlobalTheory.Mum.PolPair.pairing_factor | exact GlobalTheory.Mum.PolPair.pairing_factor | (intros; apply GlobalTheory.Mum.PolPair.pairing_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaModelPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep.SupISymm

theorem exists_unit_of_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    {c ε : Ω} (hc : c ^ 2 = 1) (hε : ε ^ ((S.r * S.N) ^ 2) = 1) : ∃ u : oˣ, c * ε = algebraMap o Ω (u : o) := by
  have hinj : Function.Injective (algebraMap o Ω) := ArithBase.inj
  have hp : IsPrimitiveRoot (algebraMap o Ω S.ζ) ((S.r * S.N) ^ 2) := S.prim.map_of_injective hinj
  have hpos : 0 < (S.r * S.N) ^ 2 := by
    have := S.N_ge; have := S.r_pos; positivity
  obtain ⟨k, -, hk⟩ := hp.eq_pow_of_pow_eq_one hε
  have hζu : IsUnit S.ζ := S.prim.isUnit hpos.ne'
  have hc' : c = 1 ∨ c = -1 := by
    have : c * c = 1 := by rw [← sq]; exact hc
    exact mul_self_eq_one_iff.1 this
  rcases hc' with rfl | rfl
  · exact ⟨(hζu.unit) ^ k, by simp [← hk, map_pow]⟩
  · exact ⟨-(hζu.unit) ^ k, by simp [← hk, map_pow]⟩

theorem exists_unit_th_neg {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (H : ∀ a : S.Gam, ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a) (a : S.Gam) :
    ∃ u : oˣ, S.th (-a) = algebraMap o Ω (u : o) * S.th a := by
  obtain ⟨c, ε, hc, hε, h⟩ := H a
  obtain ⟨u, hu⟩ := exists_unit_of_pow_eq_one S hc hε
  exact ⟨u, by rw [h, hu]⟩

theorem neg_mem_supI_of_parity {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (M : RatModel o Ω)
    (H : ∀ a : S.Gam, ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a)
    (z : M.Z) (a : S.Gam) (ha : a ∈ S.supI M z) : -a ∈ S.supI M z := by
  obtain ⟨hne, hdiv⟩ := ha
  obtain ⟨u, hu⟩ := exists_unit_th_neg S H a
  have hu0 : algebraMap o Ω (u : o) ≠ 0 := by
    intro h0
    have h1 : algebraMap o Ω ((u : o) * ((u⁻¹ : oˣ) : o)) = 1 := by simp
    rw [map_mul, h0, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨by rw [hu]; exact mul_ne_zero hu0 hne, fun j => ?_⟩
  obtain ⟨v, hv⟩ := exists_unit_th_neg S H (-j)
  rw [neg_neg] at hv
  have key : S.th j / S.th (-a) = algebraMap o Ω ((v : o) * ((u⁻¹ : oˣ) : o)) * (S.th (-j) / S.th a) := by
    have hi : algebraMap o Ω ((u⁻¹ : oˣ) : o) = (algebraMap o Ω (u : o))⁻¹ := by
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)
    rw [hv, hu, map_mul, hi]
    field_simp
  rw [key]
  exact (M.O z).mul_mem (Subalgebra.algebraMap_mem _ _) (hdiv (-j))

end GlobalTheory.Poinc.Sep.SupISymm


open GlobalTheory.Poinc.Sep.SupISymm in
theorem GlobalTheory.Poinc.Sep.neg_mem_supI : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → -a ∈ X₁.S.supI X₁.M z₁ := by
  intro g n F W Z i X₁ z₁ a ha
  exact neg_mem_supI_of_parity X₁.S X₁.M (fun a => _root_.GlobalTheory.ThetaParity.theta_neg X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ a) z₁ a ha
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareClassAdditiveInDualVariable
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.AbDual.poincare_evc_mul_right : ∀ (K : Type) [Field K] (A A' : AbVar K) (P : LB (A.X ⊗ A'.X).left)
    (hP : AbDual.IsDual A.X A'.X P) (Y : Over (Sp K)) (a : Y ⟶ A.X) (b b' : Y ⟶ A'.X),
    AbDual.evc hP.isLB a (b * b') = AbDual.evc hP.isLB a b + AbDual.evc hP.isLB a b' := by
  intro K _ A A' P hP Y a b b'
  have hs : (AbDual.swap P).IsLB := pull_isLB hP.isLB _
  have h := (AbDual.isAdditive_iff hs).1 (AbDual.isDual_isAdditive_swap _ A.X A'.X P A'.ab hP) Y b b' a
  rwa [AbDual.evc_swap hP.isLB hs, AbDual.evc_swap hP.isLB hs, AbDual.evc_swap hP.isLB hs] at h
end

