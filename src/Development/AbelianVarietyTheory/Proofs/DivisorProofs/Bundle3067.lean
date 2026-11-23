module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2789
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2953
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0850
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2101
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreIsoCarriesSharpPointsToConjugates
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3061
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0702
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0985
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0717
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2529
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3062
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2269
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2241
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2721
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPeriodGens
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnTorusComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3040
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividingLabelAndShiftsPersistDeeperModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.Poinc.Sep.div_lam_and_lam_mem_HH : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), 𝔗.X₂.M.Div 𝔗.X₂.S.th (𝔗.lam x₀) z₂ ∧ ∀ a ∈ X₁.S.HH X₁.M z₁, 𝔗.lam a ∈ 𝔗.X₂.S.HH 𝔗.X₂.M z₂ := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hW hTI X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hx₀ V _ _ _ ev X _ m t δ 𝔪
  refine ⟨GlobalTheory.T.dividingLabel_stays_dividing_deeper_model g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hTI X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hx₀ V ev X m t δ 𝔪, ?_⟩
  intro a ha
  obtain ⟨V', _, _, _, io, ev₂, hcn', hinj, hfin, -, -, hext⟩ := _root_.GlobalTheory.Poinc.Sep.exists_centred_ext_tower g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hTI
    X₁ z₁ act hact 𝔗 z₂ hz₂ V ev 𝔪.cn 𝔪.loc 𝔪.reg
  obtain ⟨u, hT, -, -⟩ := _root_.GlobalTheory.Poinc.IntTerm.exists_terms g n F W Z i X₁ z₁ act x₀ hx₀ V ev X m t δ 𝔪 (X₁.S.HH X₁.M z₁) Subtype.val
    Subtype.range_coe
  obtain ⟨eps, hbc⟩ := _root_.GlobalTheory.exists_baseChange_member_of_tower g hg n hn hodd F Z z i hproj hnorm hiz hdense W hW hTI X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hx₀
  obtain ⟨𝔪₂, hterms, -⟩ := hbc V ev X m t δ 𝔪 _ Subtype.val _ hT V' io hcn' hinj hfin
  let zt : 𝔗.X₂.M.Z.presheaf.stalk z₂ := (𝔗.X₂.M.stalkEquiv z₂).symm
    ⟨algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ, (𝔗.X₂.M.O z₂).algebraMap_mem _⟩
  have hzt : 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ :=
    congrArg Subtype.val ((𝔗.X₂.M.stalkEquiv z₂).apply_symm_apply _)
  have hyy := _root_.GlobalTheory.Poinc.Sep.TermsLabel.yy_zero_of_terms g n F W Z i 𝔗.X₂ z₂ 𝔗.act₂ (𝔗.lam x₀) V' ev₂ X m (fun k => io (t k)) δ (𝔪₂ ev₂ hext) _ _ _
    (hterms ev₂ hext zt hzt) ⟨a, ha⟩
  obtain ⟨x₂, hx₂⟩ := 𝔗.X₂.div z₂
  exact (_root_.GlobalTheory.Poinc.Sep.mem_HH_iff_yy_zero g n F W Z i 𝔗.X₂ z₂ 𝔗.act₂ x₂ hx₂ V' ev₂ X m (fun k => io (t k)) δ (𝔪₂ ev₂ hext) (𝔗.lam a)).2 hyy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPoincareLeftKernelTrivialAlgClosed
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualKer

theorem finite_of_factor {K : Type} [Field K] {N A H : Over (Sp K)} (i : N ⟶ A) (j : H ⟶ A) (z : N ⟶ H)
    (hz : z ≫ j = i) (hi : IsClosedImmersion i.left) (hj : IsClosedImmersion j.left) (hH : IsFinite H.hom) :
    IsFinite N.hom := by
  have e : z.left ≫ j.left = i.left := by rw [← Over.comp_left, hz]
  haveI : IsClosedImmersion (z.left ≫ j.left) := e ▸ hi
  haveI : IsClosedImmersion z.left := IsClosedImmersion.of_comp z.left j.left
  have : N.hom = z.left ≫ H.hom := (Over.w z).symm
  rw [this]; infer_instance

theorem leftKer_eq_one : ∀ (K : Type) [Field K] [IsAlgClosed K] (A B : Over (Sp K)) [GrpObj A] [GrpObj B] (g : ℕ) (P : LB (A ⊗ B).left), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → IsDual A B P → ∀ (T : Over (Sp K)) (x : T ⟶ A), Triv (ev P (fst T B ≫ x) (snd T B)) → x = 1 := by
  intro K _ _ A B _ _ g P hA hB hgA hgB hP T x hx
  obtain ⟨N, _, i, hi, hci, hNt, hfac⟩ := _root_.GlobalTheory.DualKernel.exists_closed_subgroup_ker K A B P hA hB hP
  obtain ⟨L, H, _, j, hL, -, -, -, hcj, hH, hKL⟩ := _root_.GlobalTheory.KernelSubgroup.exists_finite_subgroup_kernel K A hA
  obtain ⟨z, hz⟩ := (hKL N i).1 (_root_.GlobalTheory.AbDual.memKL_of_triv_ev_left K A B P L hA hB hP hL N i hNt)
  have hfin : IsFinite N.hom := finite_of_factor i j z hz hci hcj hH
  haveI : Mono i.left := inferInstance
  have hmono : Mono i := (Over.forget _).mono_of_mono_map (by simpa using (inferInstance : Mono i.left))
  obtain ⟨A', _, hA', q, hq, hqf, hqfl, hqs, hpb⟩ := _root_.GlobalTheory.AbelianQuotientField.exists_quotient K A hA N i hi hmono hfin
  have hgA' := _root_.GlobalTheory.FiniteSurjDimField.smoothOfRelativeDimension_of_finite_surjective K A A' g q hA hA' hqf hqs hgA
  obtain ⟨P', hP', hP'a, hP'i⟩ := _root_.GlobalTheory.PoincareDescent.descends K A A' B N P i q hA hA' hB hP hi hq hqf hqfl hqs hpb hNt
  have hi1 : i = 1 := by
    by_contra hne
    obtain ⟨T', M, hM, hMa, hMq, hMn⟩ := _root_.GlobalTheory.CharKer.exists_nontriv_family K A A' N i q hA hA' hi hq hfin hqf hqfl hqs hpb hne
    exact hMn (_root_.GlobalTheory.DualInjPull.triv_of_triv_pull K A A' B g P P' q hA hA' hB hgA' hgB hP hq hP' hP'a hP'i T' M hM hMa hMq)
  obtain ⟨w, rfl⟩ := hfac T x hx
  rw [hi1, MonObj.comp_one]

end GlobalTheory.DualKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8PowerFibreConjugateEvaluationIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem sharp_fibre_conj_iso : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∃ (f : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A).left), IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) ((Over.pullback (spMap (σ.toRingHom.comp ev))).obj D.P.A) (𝟙 _) f ∧ LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (D.P.L.pull (f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)))) ∧ (∀ (y : Over.mk (spMap ev) ⟶ D.P.A), (∃ k : ℕ, y ^ (l ^ k) = 1) → ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left, q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ y.left) ∧ (∀ mu (q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left), q ≫ pullback.fst D.P.A.hom (spMap ev) = spMap ev ≫ (D.c (e mu)).left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ → q ≫ f ≫ pullback.fst D.P.A.hom (spMap (σ.toRingHom.comp ev)) = spMap σ.toRingHom ≫ q ≫ pullback.fst D.P.A.hom (spMap ev)) := by
  intro g l hl hlo W hW
  obtain ⟨jB, hB⟩ := _root_.GlobalTheory.Poinc.Sep.sharp_fibre_iso_exists g l hl hlo W hW
  obtain ⟨jD, hD⟩ := _root_.GlobalTheory.Poinc.Sep.conj_sharp_points g l hl hlo W hW
  refine ⟨max jB jD, fun j hj V V₁ _ _ _ _ _ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K _ _ ev k₀ hk₀ hr σ hσ => ?_⟩
  obtain ⟨f, h0, h1, h2⟩ :=
    hB j (le_of_max_le_left hj) V V₁ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K ev k₀ hk₀ hr σ hσ
  exact ⟨f, h0, h1, h2,
    hD j (le_of_max_le_right hj) V V₁ hCN hlU Q hQg ρ hρ D e hS C u mo hmo hT K ev k₀ hk₀ hr σ hσ f h0 h1
      (fun y hy => h2 y ⟨j * 2, by rw [pow_mul]; exact hy⟩)⟩

end GlobalTheory.Poinc.Sep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharpolyTateDetDegreeTraceStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.endCharpoly_tate_det_degree_trace : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K) (f : End A), (∀ [Module.Finite ℚ_[l] (Vl l A)], (charpoly f).map (algebraMap ℤ ℚ_[l]) = (vmap l (A := A) (B := A) f.asHom).charpoly) ∧ (∀ [Module.Free ℤ_[l] (Tl l A)] [Module.Finite ℤ_[l] (Tl l A)], (charpoly f).map (algebraMap ℤ ℤ_[l]) = (tend l A f).charpoly) ∧ LinearMap.det (vmap l (A := A) (B := A) f.asHom) = (deg (A := A) (B := A) f.asHom : ℚ_[l]) ∧ LinearMap.trace ℚ_[l] _ (vmap l (A := A) (B := A) f.asHom) = (trace f : ℚ_[l]) := by
  intro K _ l _ hl A f
  have hcharpoly [Module.Finite ℚ_[l] (Vl l A)] (g : End A) :
      (charpoly g).map (algebraMap ℤ ℚ_[l]) = (vmap l g.asHom).charpoly := by
    obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A g
    have h := GlobalTheory.T.abelianVariety_degreePolynomial_map_eq_charpoly_rationalTate
      K l hl A g ((charpoly g).map (algebraMap ℤ ℚ)) (hm.map _)
      (by rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (algebraMap ℤ ℚ)), hd])
      (fun n => by simpa using congrArg (algebraMap ℤ ℚ) (hev n))
    rw [← h, Polynomial.map_map, show (algebraMap ℚ ℚ_[l]).comp (algebraMap ℤ ℚ) =
      algebraMap ℤ ℚ_[l] from Subsingleton.elim _ _]
  refine ⟨fun {_} => hcharpoly f, fun {_ _} => ?_, ?_, ?_⟩
  · apply Polynomial.map_injective (algebraMap ℤ_[l] ℚ_[l]) (IsFractionRing.injective ℤ_[l] ℚ_[l])
    rw [Polynomial.map_map, ← LinearMap.charpoly_baseChange,
      show (algebraMap ℤ_[l] ℚ_[l]).comp (algebraMap ℤ ℤ_[l]) =
        algebraMap ℤ ℚ_[l] from Subsingleton.elim _ _]
    exact hcharpoly f
  · obtain ⟨-, -, -, hfin, hrk⟩ := tl_free_finrank K l hl A
    have hneg : vmap l f.asHom = (-1 : ℚ_[l]) • vmap l (-f).asHom := by
      simp [vmap, LinearMap.baseChange_neg]
    have hev : (charpoly (-f)).eval 0 = (deg f.asHom : ℤ) := by
      simpa using (GlobalTheory.T.abelianVarietyEndCharpoly_spec K A (-f)).1.2.2 0
    rw [hneg, LinearMap.det_smul, LinearMap.det_eq_sign_charpoly_coeff, ← hcharpoly (-f),
      Polynomial.coeff_map, Polynomial.coeff_zero_eq_eval_zero, hev, hrk, pow_mul, neg_one_sq, one_pow]
    simp
  · obtain ⟨-, -, -, hfin, -⟩ := tl_free_finrank K l hl A
    rw [linTrace_eq_neg_nextCoeff, ← hcharpoly f,
      Polynomial.nextCoeff_map (RingHom.injective_int (algebraMap ℤ ℚ_[l])), trace]
    simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvarianceTensorPowerIntegralClosur
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem hInv_of_finite_over_aic (q : ℕ) [NeZero q] (d : ℕ) (hH : (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R))
    (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D] (hq : IsUnit (q : D))
    (hd : ringKrullDim D ≤ d) (T : Type) [CommRing T] [IsDomain T] [Algebra D T]
    [Algebra.IsIntegral D T] (hT : AIC T) (hTq : HInv q T) (E : Type) [CommRing E] [Algebra D E]
    [Algebra.IsIntegral D E] (ι : T →ₐ[D] E) (F : Finset E)
    (hF : Algebra.adjoin D (Set.range ι ∪ (F : Set E)) = ⊤) : HInv q E := by
  have hlow := GlobalTheory.T.etaleHomotopyInvariant_integral_killed_of_lowerDim q d hH D hq hd
  have hqE : IsUnit (q : E) := by simpa using hq.map (algebraMap D E)
  set X : Finset (E →ₐ[D] T) := (GlobalTheory.T.finite_retractions_of_adjoin_finset_integral_domain D T E ι F hF).toFinset with hX
  have hXid : ∀ χ ∈ X, χ.comp ι = AlgHom.id D T := fun χ hχ => by simpa [hX] using hχ
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.T.exists_ne_zero_isNilpotent_mul_finite_inf_fg_ideals D E (E →ₐ[D] T) X (fun χ => RingHom.ker χ)
    (fun χ hχ => GlobalTheory.T.ker_retraction_fg_of_adjoin_finset D T E ι F hF χ (hXid χ hχ))
    (fun Q hQ hQc => by
      obtain ⟨χ, hχι, hχQ⟩ := GlobalTheory.T.exists_retraction_of_monicPolynomialsHaveRoots D T E hT ι Q hQ hQc
      have hmem : χ ∈ X := by simpa [hX] using hχι
      rw [← hχQ]
      exact iInf₂_le χ hmem)
  set I : Ideal E := ⨅ χ ∈ X, RingHom.ker χ with hI
  set J : Ideal E := Ideal.span {algebraMap D E s} with hJ
  have hIJ : I ⊓ J ≤ nilradical E := by
    intro y hy
    obtain ⟨hyI, hyJ⟩ := Ideal.mem_inf.mp hy
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hyJ
    obtain ⟨m, hm⟩ := hs _ hyI
    refine ⟨2 * m, ?_⟩
    calc (a * algebraMap D E s) ^ (2 * m)
        = a ^ m * (algebraMap D E s * (a * algebraMap D E s)) ^ m := by ring
      _ = 0 := by rw [hm, mul_zero]
  have hJs : ∀ K : Ideal E, J ≤ K → algebraMap D (E ⧸ K) s = 0 := by
    intro K hK
    rw [IsScalarTower.algebraMap_apply D E (E ⧸ K), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hK (Ideal.mem_span_singleton_self _)
  exact GlobalTheory.T.etaleHomotopyInvariantTwists_of_closedCover q E I J hIJ hqE (GlobalTheory.T.hInv_quot_iInf_ker_retractions q D T E hq hTq hlow ι X hXid)
    (hlow (E ⧸ J) s hs0 (hJs J le_rfl)) (hlow (E ⧸ (I ⊔ J)) s hs0 (hJs _ le_sup_right))

def subalgebraOfSubringEquiv {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A) :
    S ≃+* subalgebraOfSubring S.toSubring where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

theorem hInv_tensorPower_integralClosure : ∀ (q : ℕ) [NeZero q] (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra.FiniteType ℤ R], IsUnit (q : R) → ringKrullDim R < d → HInv q R) → ∀ (D : Type) [CommRing D] [IsDomain D] [Algebra.FiniteType ℤ D], IsUnit (q : D) → ringKrullDim D ≤ d → ∀ k : ℕ, HInv q (PiTensorProduct D (fun _ : Fin (k + 1) => integralClosure D (AlgebraicClosure (FractionRing D)))) := by
  intro q _ d hH D _ _ _ hq hd k
  have hqDp : IsUnit (q : integralClosure D (AlgebraicClosure (FractionRing D))) := by
    simpa using hq.map (algebraMap D (integralClosure D (AlgebraicClosure (FractionRing D))))
  have hTq := GlobalTheory.T.etaleHomotopyInvariance_absolutelyIntegrallyClosed q _ (GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure D) hqDp
  have hqS : ∀ F, IsUnit (q : firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F) :=
    fun F => by simpa using hq.map (algebraMap D (firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F))
  refine GlobalTheory.T.hInv_of_directed_union_subalgebras q _ (Finset (integralClosure D (AlgebraicClosure (FractionRing D))))
    (fun F => subalgebraOfSubring (firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F).toSubring)
    ?_ ?_ ?_ ?_
  · intro F G hFG x hx
    rw [mem_subalgebraOfSubring] at hx ⊢
    exact Algebra.adjoin_mono (Set.union_subset_union_right _
      (Set.iUnion_mono fun i => Set.image_mono (Finset.coe_subset.mpr hFG))) hx
  · intro x
    obtain ⟨F, hF⟩ := GlobalTheory.T.exists_finset_mem_tensorPowerFirstFactorAdjoinFinset D _ k x
    exact ⟨F, (mem_subalgebraOfSubring).mpr hF⟩
  · intro F
    simpa using (hqS F).map (subalgebraOfSubringEquiv (firstAndFinite D (integralClosure D (AlgebraicClosure (FractionRing D))) k F))
  · intro F
    haveI := GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_isIntegral D (integralClosure D (AlgebraicClosure (FractionRing D))) k F
    obtain ⟨F', hF'⟩ := GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_fg_over_first D (integralClosure D (AlgebraicClosure (FractionRing D))) k F
    exact _root_.GlobalTheory.EtC.hInv_of_ringEquiv q _ _ (subalgebraOfSubringEquiv _)
      (hInv_of_finite_over_aic q d hH D hq hd _ (GlobalTheory.T.monicPolynomialsHaveRoots_integralClosure_algClosure D) hTq _ (firstIncl D _ k F) F' hF')

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechKodairaSpencerClassAbelianTriple
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

namespace GlobalTheory.KSExists

theorem isField_mono {Z : Scheme.{0}} {W₀ W₁ : Z.Opens} (h : W₁ ≤ W₀) {d : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)}
    (hd : IsField W₀ d) : IsField W₁ d :=
  ⟨fun W hW => hd.1 W (hW.trans h), fun W hW => hd.2.1 W (hW.trans h), fun W W' h' hW => hd.2.2 W W' h' (hW.trans h)⟩

theorem isField_sub {Z : Scheme.{0}} {W₀ : Z.Opens} {d d' : ∀ W : Z.Opens, Γ(Z, W) → Γ(Z, W)}
    (hd : IsField W₀ d) (hd' : IsField W₀ d') : IsField W₀ (fun W f => d W f - d' W f) := by
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
  · simp only [hd.1 W hW, hd'.1 W hW]; ring
  · simp only [hd.2.1 W hW, hd'.2.1 W hW]; ring
  · simp only [map_sub, hd.2.2 W W' h hW, hd'.2.2 W W' h hW]

theorem lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)), ∃ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι) (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsAffineOpen (W i)) ∧ ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 ∧ (∀ i, W i ≤ t.PP.L.U (j i)) ∧ (∀ i, IsField (W i) (d i)) ∧ ∀ i (h : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), d i (W i) ((t.G.hom.appLE U.1 (W i) h).hom r) = (t.G.hom.appLE U.1 (W i) h).hom (D r) := _root_.GlobalTheory.KSLift.exists_lifts

theorem cocycle : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (J : Type) (W : J → t.G.left.Opens) (j : J → t.PP.L.ι), (∀ i, IsAffineOpen (W i)) → ⨆ i, W i = t.G.hom ⁻¹ᵁ U.1 → (∀ i, W i ≤ t.PP.L.U (j i)) → ∀ (e : J → J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i i', IsField (W i ⊓ W i') (e i i')) → (∀ i i' (h : W i ⊓ W i' ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), e i i' (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') h).hom r) = 0) → (∀ i i' i'' (O : t.G.left.Opens), O ≤ W i ⊓ W i' ⊓ W i'' → ∀ f : Γ(t.G.left, O), e i i' O f + e i' i'' O f = e i i'' O f) → ∃ (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) (h : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ i, IsField (W i) (h i)) ∧ (∀ i (hW : W i ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), h i (W i) ((t.G.hom.appLE U.1 (W i) hW).hom r) = 0) ∧ ∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, IsTranslate t φ g₀ (v a) (w a)) → valR g₀ O (e i i' O f) = valR g₀ O (h i O f - h i' O f) + ∑ a, ∑ b, φ (Θ a b) * ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) * (valR (w a) O f).snd := _root_.GlobalTheory.KSCocycle.exists_coboundary_add_dlog

theorem exists_isKS : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ D : Derivation ℤ Γ(X, U.1) Γ(X, U.1), ∃ Θ, IsKS t ⊤ U v D Θ := by
  intro E _ _ _ H X t hP hA hK U n v hv hb D
  obtain ⟨J, W, j, d, hWa, hcov, hWj, hd, hlift⟩ := lifts E H X t U D
  have hWU : ∀ i, W i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i => hcov ▸ le_iSup W i
  have hres : ∀ i i' (r : Γ(X, U.1)), resG t.G.left (inf_le_left : W i ⊓ W i' ≤ W i)
      ((t.G.hom.appLE U.1 (W i) (hWU i)).hom r) = (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom r := by
    intro i i' r
    exact congrArg (fun q => q.hom r) (Scheme.Hom.appLE_map t.G.hom (hWU i) (homOfLE (inf_le_left : W i ⊓ W i' ≤ W i)).op)
  have hres' : ∀ i i' (r : Γ(X, U.1)), resG t.G.left (inf_le_right : W i ⊓ W i' ≤ W i')
      ((t.G.hom.appLE U.1 (W i') (hWU i')).hom r) = (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom r := by
    intro i i' r
    exact congrArg (fun q => q.hom r) (Scheme.Hom.appLE_map t.G.hom (hWU i') (homOfLE (inf_le_right : W i ⊓ W i' ≤ W i')).op)
  have a1 : ∀ i i' (r : Γ(X, U.1)), d i (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom r) =
      (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (D r) := by
    intro i i' r
    rw [← hres i i' r, (hd i).2.2 _ _ inf_le_left le_rfl, hlift i (hWU i), hres]
  have a2 : ∀ i i' (r : Γ(X, U.1)), d i' (W i ⊓ W i') ((t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom r) =
      (t.G.hom.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom (D r) := by
    intro i i' r
    rw [← hres' i i' r, (hd i').2.2 _ _ inf_le_right le_rfl, hlift i' (hWU i'), hres']
  obtain ⟨Θ, h, hh, hhv, hks⟩ := cocycle E H X t hP hA hK U n v hv hb J W j hWa hcov hWj
    (fun i i' O f => d i O f - d i' O f)
    (fun i i' => isField_sub (isField_mono inf_le_left (hd i)) (isField_mono inf_le_right (hd i')))
    (fun i i' hW r => by
      show d i _ _ - d i' _ _ = 0
      rw [a1, a2, sub_self])
    (fun i i' i'' O _ f => sub_add_sub_cancel _ _ _)
  refine ⟨Θ, J, W, j, fun i O f => d i O f - h i O f, by rw [inf_top_eq]; exact hcov, hWj,
    fun i => isField_sub (hd i) (hh i), fun i hW r => ?_, fun i i' O hO f S _ φ g₀ w hg hO' hw => ?_⟩
  · show d i _ _ - h i _ _ = _
    rw [hlift i hW r, hhv i hW r, sub_zero]
  · have e := hks i i' O hO f S φ g₀ w hg hO' hw
    have hv' : ∀ a b : Γ(t.G.left, O), valR g₀ O (a - b) = valR g₀ O a - valR g₀ O b := fun a b => by
      simp only [valR, dif_pos hO', map_sub]
    show valR g₀ O ((d i O f - h i O f) - (d i' O f - h i' O f)) = _
    rw [show (d i O f - h i O f) - (d i' O f - h i' O f) = (d i O f - d i' O f) - (h i O f - h i' O f) by ring,
      hv', e]
    ring

end GlobalTheory.KSExists
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataTautologicalChartOfTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem exists_degFrom_of_trait : ∀ (g : ℕ), 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (T : GlobalTheory.Poinc.Trait F) (b : cycAway n →+* T.V), T.y ≫ F.s = jK T.V ≫ spMap b → ∃ (L : LowBase (zetaAway n) n) (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin L.T.r → ℤ))) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : T.V →+* V') (κ : L.W →+* V') (s : Fin m ⊕ Fin N → V') (D' : DegData V' (maximalIdeal V')) (e : D'.toPre.X ≃+ (Fin L.T.r → ℤ)) (G' : Over (Sp V')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ T.G.left) (A' : PolAV (Sp (FractionRing V'))) (U' : Unif (maximalIdeal V') D' A' G'), L.h + L.T.r = g ∧ IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) ∧ (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ)) x x) ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b ∧ (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) ∧ (∀ k, IsUnit (s (.inr k))) ∧ IsUnifAlong F T.y (T.U.gen.hom.left ≫ T.α) f π U' ∧ DegFrom L.T κ s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) n D'.toPre e := by
  intro g hg φ hφ n hn hodd F T b hb
  have hV : IsCN T.V := ⟨inferInstance, inferInstance, T.complete, inferInstance⟩
  let e₀ : (Fin (Module.finrank ℤ T.D.toPre.X) → ℤ) ≃+ T.D.toPre.X :=
    (Module.finBasis ℤ T.D.toPre.X).equivFun.symm.toAddEquiv
  have hc : ∀ a a', T.D.toPre.c (e₀ (a + a')) = T.D.toPre.c (e₀ a) * T.D.toPre.c (e₀ a') := fun a a' => by
    rw [map_add (f := _)]; exact T.D.toPre.c_add _ _
  obtain ⟨L, V₁, _, _, _, f₁, κ₁, e, hLh, hCN₁, hDVR₁, hi₁, hf₁, hl₁, hκ₁, hb₁, B', _, β', β'', β₂, β₂', p₁, p₂, s₁, s₂,
    lb, pts⟩ := _root_.GlobalTheory.TChart.exists_lowBase_of_trait n hn hodd T.V hV inferInstance b T.D.toPre.P _ (fun a => T.D.toPre.c (e₀ a)) hc
  have hr : L.T.r = Module.finrank ℤ T.D.toPre.X := by
    simpa using LinearEquiv.finrank_eq e.toIntLinearEquiv
  have hgen : L.h + L.T.r = g := by rw [hLh, hr]; exact GlobalTheory.Poinc.Trait.dim_add_rank (by omega) F T
  obtain ⟨q, hqs, hqa, hqp, hq⟩ := _root_.GlobalTheory.TChart.exists_periods_of_pull n T.V T.D _ e₀ L V₁ f₁ κ₁ e B' β' β'' β₂ β₂' hV inferInstance hCN₁ hDVR₁ hi₁ hf₁
    hl₁ hκ₁ p₁ p₂ s₁ s₂ lb pts
  obtain ⟨m, N, ε, hcone, hdef, V₂, _, _, _, f₂, fK, s, hCN₂, hDVR₂, hi₂, hf₂, hl₂, hfK, hs₁, hs₂, hqs'⟩ :=
    GlobalTheory.PerRoot.exists_roots_of_periods g n φ hφ (by omega) V₁ hCN₁ hDVR₁ L.T.r (by omega) q hqs hqa hqp
  have hl : IsLocalHom (f₂.comp f₁) := RingHom.isLocalHom_comp f₂ f₁
  have hlκ : IsLocalHom (f₂.comp κ₁) := RingHom.isLocalHom_comp f₂ κ₁
  obtain ⟨D', hD, G', _, _, π, A', U', hU⟩ :=
    GlobalTheory.TraitExt.exists_unifAlong_pullTo F T V₂ (f₂.comp f₁) hCN₂ hDVR₂ (hi₂.comp hi₁) (hf₂.comp hf₁) hl
  refine ⟨L, m, N, ε, V₂, inferInstance, inferInstance, inferInstance, f₂.comp f₁, f₂.comp κ₁, s, D',
    hD.xe.trans (e₀.symm.trans e.symm), G', inferInstance, inferInstance, π, A', U', hgen, hcone, hdef, hCN₂, hDVR₂,
    hi₂.comp hi₁, hf₂.comp hf₁, hl, hlκ, ?_, hs₁, hs₂, hU, ?_⟩
  · rw [RingHom.comp_assoc, hb₁, ← RingHom.comp_assoc]
  · exact hq V₂ f₂ fK s (fun k => (ε k : LinearMap.BilinForm ℤ (Fin L.T.r → ℤ))) hCN₂ hi₂ hf₂ hl₂ hfK hqs' D' hD

end GlobalTheory.TChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicSaturatedWeightFiltrationStatement
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_saturated_weight_filtration : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ C : GlobalTheory.UChart.Fam Xo c R,
  1 ≤ Module.finrank (𝓞 E) C.P.D.toPre.X →
  ∃ Z : Submodule (𝓞 E) Dw.La, GlobalTheory.LowDat.IsIsoSat Dw Z ∧ Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) C.P.D.toPre.X ∧
    ∃ (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)),
      ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
        ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F),
          GlobalTheory.LowDat.XFLevel C tK m1 m2 F I ∧ GlobalTheory.LowDat.FiltGraded C Z F I := by
  first | exact @GlobalTheory.LowFilt.exists_filt | exact GlobalTheory.LowFilt.exists_filt | (intros; apply GlobalTheory.LowFilt.exists_filt <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerObjectCompleteDVRBothMaps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.LowPull.exists_lowObj_cdvr : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ θ₁ θ₂ : R →+* V, Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK V ≫ spMap θ₁ → κ₂ ≫ jK R = jK V ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → ∃ (o' : LowObj Cn.D' c ((θ₁.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b)) (m₁ : ObjMap o' Cn.L.o (spMap (θ₁.comp (Cn.ψ.comp MvPolynomial.C)))) (m₂ : ObjMap o' Cn.L.o (spMap (θ₂.comp (Cn.ψ.comp MvPolynomial.C)))) (x : Cn.L.D.X → (Sp V ⟶ o'.t.G.left)), (∀ y, x y ≫ m₁.toSABMap.φ ≫ Cn.L.φB = spMap (θ₁.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left) ∧ (∀ y, x y ≫ m₂.toSABMap.φ ≫ Cn.L.φB = spMap (θ₂.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left) ∧ ∀ y, x y ≫ o'.t.G.hom = 𝟙 _ := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns R _ _ _ hR C Cn V _ _ _ hV θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨hdvr, hc, hch⟩ := hV
  haveI := hdvr
  haveI := hch
  have hb : θ₁.comp C.b = θ₂.comp C.b := LowPull.comp_b_eq C.toFam θ₁ θ₂ κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨D₁, D₂, hD₁, hD₂, j₁, j₂, b, φ', he₁, he₂, hM, hlin, hQ, hbl⟩ :=
    GlobalTheory.UInj.pair_match Xo c φ R hR C.toFam V hc θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  have hlat := GlobalTheory.T.canonicalFamily_latticeIdentification_eq_id Xo c φ hpq hφ hns R hR C Cn V hc θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b φ' he₁ he₂ hM
    hlin hQ
  exact LowPull.exists_pull₂ Cn.L V _ _ (GlobalTheory.T.canonicalFamily_base_eq_of_matching_pullbacks Xo c φ R hR C Cn V hc θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b φ'
    he₁ he₂ hM hQ hbl hlat hb)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorPolynomialDefect
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

namespace GlobalTheory.HeatEx

theorem exists_basic_heat_polyDefect : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Dd.toPre.X), IsMonomial Dd.toPre t gam → (∀ i, t i ≠ 0) → ∀ D : Derivation ℤ R R, (∀ i, D (t i) ∈ Ideal.span {t i}) → ∃ (h : Heat Y.H Y.q.left Dd.toPre.P.L dd ⇑D) (w : Dd.toPre.X → Dd.toPre.X →+ R) (π π' : Dd.toPre.X → R), IsBasic Y h ∧ HasDefect Y h (fun (k : ℕ) mu α => 2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y n v dd hdd m t gam hmon ht D hD
  obtain ⟨Θ, J, V, j, d, hs, hc, hle, hl, hw, hks⟩ := _root_.GlobalTheory.HeatInvLift.exists_invLift_symmKS R Dd O oa Y n v dd hdd D
  obtain ⟨h, hb⟩ := _root_.GlobalTheory.HeatGlue.exists_basic_heat R Dd O oa Y n v dd hdd D Θ J V j d hs hc hle hl hw hks
    (_root_.GlobalTheory.PullbackWeightZero.exists_comb_dlg_add_cob R Dd O oa Y n v dd hdd J V j hc hle)
  obtain ⟨w, π, π', hdef⟩ := _root_.GlobalTheory.HeatDefect.defect_polynomial R Dd O oa Y n v dd hdd m t gam hmon ht D hD h hb
  exact ⟨h, w, π, π', hb, hdef⟩

end GlobalTheory.HeatEx
end
end

