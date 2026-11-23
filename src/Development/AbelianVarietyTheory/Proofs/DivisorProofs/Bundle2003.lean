module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TrivOnOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1952
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1865
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeAdditiveFamiliesAgree
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.DualLocus

theorem exists_ideal_locTriv_noeth (hG : GlobalFnsSt) (R : Type) [CommRing R] [IsNoetherianRing R]
    (B : Over (Spec (CommRingCat.of R))) [GrpObj B] (hB : IsAbelianScheme B) (F : LB B.left) (hF : F.IsLB) :
    ∃ I : Ideal R, ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ B.left)
      (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) →
      ((∀ p : Spec (CommRingCat.of R'), ∃ U : (Spec (CommRingCat.of R')).Opens, p ∈ U ∧
        Triv ((F.pull π).pull (f' ⁻¹ᵁ U).ι)) ↔ I ≤ RingHom.ker g) := by
  haveI := hB.proper
  haveI := hB.geomConnected
  haveI := hB.smooth
  have hP := ProperFinite.nonempty_perf_of_isProper (R := R) B.hom hF
  have hQ := ProperFinite.nonempty_perf_of_isProper (R := R) B.hom (isLB_pw hF (-1))
  have hC := GlobalTheory.TrivLocus.isClosed_trivLocus R _ B.hom F hF hP hQ hB.proper
    (GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected)
  obtain ⟨I, hI⟩ := TrivRep.exists_ideal (TrivRep.TrivOn B.hom F) (TrivRep.TrivOn.comp B.hom F) (fun p => by
    by_cases hp : p ∈ {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0})
      (π : X' ⟶ B.left) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧
        IsPullback π f' B.hom (Spec.map (CommRingCat.ofHom g)) ∧ Triv (F.pull π)}
    · obtain ⟨K, _, g₀, X₀, π₀, f₀, hk, h₀, ht⟩ := hp
      obtain ⟨r, I, hr, -, H⟩ := GlobalTheory.AbLaw.Seesaw.seesaw R _ B.hom F hF hP inferInstance inferInstance K g₀ X₀ π₀ f₀
        h₀ (CubeOpen.bijective_appTop hG B hB h₀) ht
      exact ⟨r, hk ▸ hr, I, fun S _ g hu => H S g _ _ _ (IsPullback.of_hasPullback _ _) hu⟩
    · obtain ⟨_, ⟨r, rfl⟩, hr, hU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
        (Set.mem_compl hp) hC.isOpen_compl
      refine ⟨r, hr, ⊤, fun S _ g hu => ⟨fun ht => ?_, fun h => ?_⟩⟩
      · rcases subsingleton_or_nontrivial S with _ | _
        · exact fun a _ => Subsingleton.elim _ _
        obtain ⟨m, hm⟩ := Ideal.exists_maximal S
        letI := Ideal.Quotient.field m
        let g' := (Ideal.Quotient.mk m).comp g
        refine (hU (a := ⟨RingHom.ker g', RingHom.ker_isPrime g'⟩) (hu.map (Ideal.Quotient.mk m)).ne_zero ?_).elim
        exact ⟨S ⧸ m, inferInstance, g', _, _, _, rfl, IsPullback.of_hasPullback _ _, ht.comp B.hom F S g _ _⟩
      · haveI : Subsingleton S := subsingleton_of_zero_eq_one
          ((h (Submodule.mem_top (x := 1))).symm.trans (map_one g))
        exact TrivRep.trivOn_of_subsingleton B.hom F S g)
  refine ⟨I, fun S _ g X' π f' h => ?_⟩
  rw [← hI S g]
  exact forall_congr' fun q => TrivRep.loc_iff B.hom F h q

variable {S : Scheme.{0}} (A : Over S)

theorem isPullback_lift {Y T : Over S} (y : Y ⟶ T) :
    IsPullback (lift (fst A Y) (snd A Y ≫ y)).left (snd A Y).left (snd A T).left y.left := by
  have h₀ : IsPullback (pullback.fst A.hom T.hom) (snd A T).left A.hom T.hom :=
    IsPullback.of_hasPullback A.hom T.hom
  have e₁ : (lift (fst A Y) (snd A Y ≫ y)).left ≫ pullback.fst A.hom T.hom = (fst A Y).left := by
    rw [show pullback.fst A.hom T.hom = (fst A T).left from rfl, ← Over.comp_left, lift_fst]
  have big : IsPullback ((lift (fst A Y) (snd A Y ≫ y)).left ≫ pullback.fst A.hom T.hom) (snd A Y).left A.hom
      (y.left ≫ T.hom) := by
    have := IsPullback.of_hasPullback A.hom Y.hom
    rw [e₁, Over.w y]
    exact this
  exact IsPullback.of_right big (by rw [← Over.comp_left, lift_snd, Over.comp_left]) h₀

theorem exists_closed_locTriv_noeth (hG : GlobalFnsSt) {T : Over S} [GrpObj A] [IsLocallyNoetherian T.left]
    (hA : IsAbelianScheme A) (F : LB (A ⊗ T).left) (hF : F.IsLB) :
    ∃ (G : Over S) (i : G ⟶ T), IsClosedImmersion i.left ∧ ∀ (Y : Over S) (y : Y ⟶ T),
      TrivSubscheme.LocTrivOver (snd A T).left F Y.left y.left ↔ ∃ z : Y ⟶ G, z ≫ i = y := by
  have h₀ : IsPullback (pullback.fst A.hom T.hom) (snd A T).left A.hom T.hom :=
    IsPullback.of_hasPullback A.hom T.hom
  obtain ⟨I, hI⟩ := TrivSubscheme.exists_idealSheaf (TrivSubscheme.LocTrivOver (snd A T).left F)
    TrivSubscheme.LocTrivOver.comp TrivSubscheme.locTrivOver_of_affine (fun U => by
      haveI := IsLocallyNoetherian.component_noetherian U
      let t : Spec (CommRingCat.of Γ(T.left, U)) ⟶ S := U.2.fromSpec ≫ T.hom
      have h₁ : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom (U.2.fromSpec ≫ T.hom) :=
        IsPullback.of_hasPullback _ _
      let φ := h₀.lift _ _ (h₁.w.trans (Category.assoc _ _ _).symm)
      have h₂ : IsPullback φ (pullback.snd A.hom t) (snd A T).left U.2.fromSpec :=
        IsPullback.of_right (by rw [h₀.lift_fst]; exact h₁) (h₀.lift_snd _ _ _) h₀
      obtain ⟨I, hI⟩ := exists_ideal_locTriv_noeth hG Γ(T.left, U) ((Over.pullback t).obj A)
        (CubeGen.isAb_baseChange hA t) (F.pull φ) (LB.isLB_pull hF φ)
      refine ⟨I, fun R g => ?_⟩
      have h₃ := IsPullback.of_hasPullback (pullback.snd A.hom t) (Spec.map g)
      rw [← hI R g.hom _ _ _ h₃, TrivSubscheme.locTrivOver_iff (h₃.paste_horiz h₂)]
      refine forall_congr' fun y => exists_congr fun V => and_congr_right fun _ => ?_
      rw [← Category.assoc]
      exact ((TrivSubscheme.triv_pull_iff _ _ _).trans (TrivSubscheme.triv_pull_iff _ _ _)).symm)
  refine ⟨Over.mk (I.subschemeι ≫ T.hom), Over.homMk I.subschemeι rfl,
    inferInstanceAs (IsClosedImmersion I.subschemeι), fun Y y => ?_⟩
  rw [hI]
  constructor
  · intro h
    have h' : I.subschemeι.ker ≤ y.left.ker := by rwa [Scheme.IdealSheafData.ker_subschemeι]
    refine ⟨Over.homMk (IsClosedImmersion.lift I.subschemeι y.left h') ?_, ?_⟩
    · exact (IsClosedImmersion.lift_fac_assoc _ _ _ _).trans (Over.w y)
    · exact Over.OverMorphism.ext (IsClosedImmersion.lift_fac _ _ _)
  · rintro ⟨z, rfl⟩
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp z.left I.subschemeι)

variable {A} [GrpObj A]

theorem same_iff_locTriv (hG : GlobalFnsSt) (hA : IsAbelianScheme A) {T : Over S} {N N' : LB (A ⊗ T).left}
    (hN : Fam A N) (hN' : Fam A N') {F : LB (A ⊗ T).left} (hF : F.IsLB)
    (hc : cls F hF = cls N hN.isLB - cls N' hN'.isLB) (Y : Over S) (y : Y ⟶ T) :
    Same A N N' y y ↔ TrivSubscheme.LocTrivOver (snd A T).left F Y.left y.left := by
  let ψ := (lift (fst A Y) (snd A Y ≫ y)).left
  let p := (snd A Y).left
  let e := (lift (1 : Y ⟶ A) (𝟙 Y)).left
  have he : e ≫ p = 𝟙 Y.left := by
    simp only [e, p]
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have hs : Same A N N' y y ↔ CechPic.pull ψ (cls F hF) = 0 := by
    rw [same_iff hN.isLB hN'.isLB, hc, map_sub, sub_eq_zero]
    rfl
  have key : ∀ {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ Y).left),
      Triv (F.pull (r ≫ ψ)) ↔ CechPic.pull r (CechPic.pull ψ (cls F hF)) = 0 := fun r => by
    rw [← pull_comp, ← cls_pull hF _ (pull_isLB hF _)]
    exact (cls_eq_zero_iff (pull_isLB hF _)).symm
  have z₀ : CechPic.pull (e ≫ ψ) (cls F hF) = 0 := by
    have ee : e ≫ ψ = (lift (1 : Y ⟶ A) y).left := by
      simp only [e, ψ]
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, Category.id_comp]
    rw [ee, hc, map_sub]
    have a := hN.add.evc_one hN.isLB y
    have b := hN'.add.evc_one hN'.isLB y
    simp only [evc] at a b
    rw [a, b, sub_zero]
  rw [TrivSubscheme.locTrivOver_iff (isPullback_lift A y), hs]
  constructor
  · intro h q
    exact ⟨⊤, trivial, (key _).2 (by rw [h, map_zero])⟩
  · intro h
    have cl : ∀ {Z : Scheme.{0}} (φ' : Fin 2 → (Z ⟶ (A ⊗ T).left)),
        Triv (LB.LinComb F φ' ![1, -1]) ↔
          CechPic.pull (φ' 0) (cls F hF) - CechPic.pull (φ' 1) (cls F hF) = 0 := fun φ' => by
      refine (cls_eq_zero_iff (LB.isLB_linComb hF _ _)).symm.trans ?_
      rw [cls_linComb hF, Fin.sum_univ_two]
      simp [sub_eq_add_neg]
    have sec : ∀ {Z : Scheme.{0}} (r : Z ⟶ (A ⊗ Y).left),
        CechPic.pull (r ≫ p ≫ e ≫ ψ) (cls F hF) = 0 := fun r => by
      rw [pull_comp, pull_comp, z₀, map_zero, map_zero]
    have T₀ : Triv (LB.LinComb F ![ψ, p ≫ e ≫ ψ] ![1, -1]) := by
      refine CubeGen.triv_of_local hF _ _ p e he (fun Z b U _ k => ?_) (fun V => ?_) (fun s => ?_)
      · have w : b ≫ e ≫ p ≫ e ≫ ψ = b ≫ e ≫ ψ := by
          rw [reassoc_of% he]
        simp [Fin.prod_univ_two, w]
      · let YV : Over S := Over.mk (V.ι ≫ Y.hom)
        let v : YV ⟶ Y := Over.homMk V.ι rfl
        exact ⟨_, _, (snd A YV).left, isPullback_lift A v, surj_snd hG hA YV⟩
      · obtain ⟨U, hU, ht⟩ := h s
        refine ⟨U, hU, ?_⟩
        unfold CubeGen.TrivAt
        rw [cl]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        rw [sec, sub_zero, pull_comp]
        exact (key _).1 ht
    have := (cl _).1 T₀
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at this
    have s₁ := sec (𝟙 _)
    rw [Category.id_comp] at s₁
    rwa [s₁, sub_zero] at this

theorem exists_closed_same : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A] [IsLocallyNoetherian T.left],
    IsAbelianScheme A → ∀ (N N' : LB (A ⊗ T).left), Fam A N → Fam A N' → ∃ (G : Over S) (i : G ⟶ T),
      IsClosedImmersion i.left ∧ ∀ (Y : Over S) (y : Y ⟶ T), Same A N N' y y ↔ ∃ z : Y ⟶ G, z ≫ i = y := by
  intro S A T _ _ hA N N' hN hN'
  obtain ⟨F, hF, hc⟩ := cls_surj (cls N hN.isLB - cls N' hN'.isLB)
  obtain ⟨G, i, hi, hG⟩ := exists_closed_locTriv_noeth A ExpansionTotal.globalFns hA F hF
  exact ⟨G, i, hi, fun Y y => (same_iff_locTriv ExpansionTotal.globalFns hA hN hN' hF hc Y y).trans (hG Y y)⟩

end GlobalTheory.DualLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CycLift

open Polynomial

theorem exists_injective_hom {n : ℕ} (hn : n ≠ 0) {V : Type} [CommRing V] [IsDomain V] [CharZero V]
    {u : V} (hu : IsPrimitiveRoot u n) (hnV : IsUnit (n : V)) :
    ∃ f : cycAway n →+* V, Function.Injective f ∧ f (zetaAway n) = u := by
  have hp := Nat.pos_of_ne_zero hn
  let L := FractionRing V
  have hinj : Function.Injective (algebraMap V L) := IsFractionRing.injective V L
  haveI : CharZero L := charZero_of_injective_algebraMap hinj
  have hz : IsPrimitiveRoot (zetaAway n : ℂ) n := Complex.isPrimitiveRoot_exp n hn
  have hi : IsIntegral ℚ (zetaAway n : ℂ) := (hz.isIntegral hp).tower_top
  let K := IntermediateField.adjoin ℚ {(zetaAway n : ℂ)}
  have hle : cycAway n ≤ K.toSubfield.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro x (rfl | rfl)
    · exact IntermediateField.mem_adjoin_simple_self ℚ _
    · exact K.inv_mem (natCast_mem K n)
  have huL : IsPrimitiveRoot (algebraMap V L u) n := hu.map_of_injective hinj
  have hr : algebraMap V L u ∈ (minpoly ℚ (zetaAway n : ℂ)).aroots L := by
    rw [← cyclotomic_eq_minpoly_rat hz hp, mem_aroots]
    refine ⟨cyclotomic_ne_zero n ℚ, ?_⟩
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact huL.isRoot_cyclotomic hp
  let g : K →ₐ[ℚ] L := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hi).symm ⟨_, hr⟩
  have hg : g (IntermediateField.AdjoinSimple.gen ℚ (zetaAway n : ℂ)) = algebraMap V L u :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hi ⟨_, hr⟩
  let f₀ : cycAway n →+* L := g.toRingHom.comp (Subring.inclusion hle)
  have hf₀ : Function.Injective f₀ := g.toRingHom.injective.comp (Subring.inclusion_injective hle)
  have hζ : f₀ (zetaAway n) = algebraMap V L u := hg
  have hmem : ∀ x, f₀ x ∈ (algebraMap V L).range := by
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨u, hζ.symm⟩
      · refine ⟨↑hnV.unit⁻¹, ?_⟩
        have e : (n : cycAway n) * ⟨(n : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩ = 1 :=
          Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn : (n : ℂ) ≠ 0))
        have e₁ := congrArg f₀ e
        rw [map_mul, map_natCast, map_one] at e₁
        have e₂ : (n : L) * algebraMap V L ↑hnV.unit⁻¹ = 1 := by
          rw [← map_natCast (algebraMap V L) n, ← map_mul, hnV.mul_val_inv, map_one]
        exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one e₂) (e₂.trans e₁.symm)
    | zero => exact Set.mem_of_eq_of_mem (map_zero f₀) (zero_mem _)
    | one => exact Set.mem_of_eq_of_mem (map_one f₀) (one_mem _)
    | add x y hx hy ihx ihy => exact (map_add f₀ ⟨x, hx⟩ ⟨y, hy⟩) ▸ add_mem ihx ihy
    | neg x hx ih => exact (map_neg f₀ ⟨x, hx⟩) ▸ neg_mem ih
    | mul x y hx hy ihx ihy => exact (map_mul f₀ ⟨x, hx⟩ ⟨y, hy⟩) ▸ mul_mem ihx ihy
  let e := RingEquiv.ofBijective (algebraMap V L).rangeRestrict
    ⟨fun a b h => hinj (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  have he : ∀ y, algebraMap V L (e.symm y) = y := fun y => congrArg Subtype.val (e.apply_symm_apply y)
  refine ⟨e.symm.toRingHom.comp (f₀.codRestrict _ hmem),
    e.symm.injective.comp (fun a b h => hf₀ (congrArg Subtype.val h)), hinj ?_⟩
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, he]
  exact hζ

end GlobalTheory.CycLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentStalkDerivationOfFunctionFieldExt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

namespace GlobalTheory.LogKSDiv.LocalExt

theorem exists_restrict_der {k A K R : Type} [CommRing k] [CommRing A] [CommRing K] [CommRing R]
    [Algebra k A] [Algebra k K] (φ : A →+* K) (hφ : Function.Injective φ)
    (hk : ∀ c : k, φ (algebraMap k A c) = algebraMap k K c)
    (h : R →+* A) (hfr : ∀ a : A, ∃ r s : R, IsUnit (h s) ∧ a * h s = h r)
    (d : Derivation ℤ R R) (D : Derivation k K K)
    (hD : ∀ r, D (φ (h r)) = φ (h (d r))) :
    ∃ δ : Derivation k A A, (∀ a, D (φ a) = φ (δ a)) ∧ ∀ r, δ (h r) = h (d r) := by
  have hmem : ∀ a, ∃ b, φ b = D (φ a) := by
    intro a
    obtain ⟨r, s, ⟨u, hu⟩, hrs⟩ := hfr a
    refine ⟨(h (d r) - a * h (d s)) * ((u⁻¹ : Aˣ) : A), ?_⟩
    have e1 : D (φ a * φ (h s)) = φ (h (d r)) := by rw [← map_mul, hrs, hD]
    rw [Derivation.leibniz, hD, smul_eq_mul, smul_eq_mul] at e1
    have hinv : φ (h s) * φ ((u⁻¹ : Aˣ) : A) = 1 := by rw [← map_mul, ← hu, Units.mul_inv, map_one]
    rw [map_mul, map_sub, map_mul, ← e1]
    linear_combination (D (φ a)) * hinv
  choose δ0 hδ0 using hmem
  let δ : Derivation k A A :=
    { toFun := δ0
      map_add' := fun a b => hφ (by simp only [hδ0, map_add (f := _)])
      map_smul' := fun c a => hφ (by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, hk, hδ0]
        rw [← Algebra.smul_def, D.map_smul, Algebra.smul_def])
      map_one_eq_zero' := hφ (by show φ (δ0 1) = φ 0; rw [hδ0, map_one, Derivation.map_one_eq_zero, map_zero])
      leibniz' := fun a b => hφ (by
        show φ (δ0 (a * b)) = φ (a • δ0 b + b • δ0 a)
        simp only [hδ0, map_mul, map_add (f := _), smul_eq_mul, Derivation.leibniz]) }
  refine ⟨δ, fun a => (hδ0 a).symm, fun r => hφ ?_⟩
  show φ (δ0 (h r)) = _
  rw [hδ0, hD]

end GlobalTheory.LogKSDiv.LocalExt

namespace GlobalTheory.LogKSDiv.LocalExt

theorem exists_frac_germ {X : Scheme.{0}} (B : X.Opens) (y : B.toScheme) (U : X.affineOpens) (hy : B.ι y ∈ U.1)
    (a : B.toScheme.presheaf.stalk y) :
    ∃ r s : Γ(X, U.1), IsUnit ((B.ι.stalkMap y).hom (X.presheaf.germ U.1 (B.ι y) hy s)) ∧
      a * (B.ι.stalkMap y).hom (X.presheaf.germ U.1 (B.ι y) hy s) =
        (B.ι.stalkMap y).hom (X.presheaf.germ U.1 (B.ι y) hy r) := by
  letI := X.presheaf.algebra_section_stalk (⟨B.ι y, hy⟩ : U.1)
  haveI := U.2.isLocalization_stalk ⟨B.ι y, hy⟩
  let e := asIso (B.ι.stalkMap y)
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (U.2.primeIdealOf ⟨B.ι y, hy⟩).asIdeal.primeCompl (e.inv.hom a)
  refine ⟨r, s, (IsLocalization.map_units (X.presheaf.stalk (B.ι y)) s).map (B.ι.stalkMap y).hom, ?_⟩
  have h2 := congrArg (B.ι.stalkMap y).hom hrs
  rw [map_mul] at h2
  have h3 : (B.ι.stalkMap y).hom (e.inv.hom a) = a := by
    change (e.inv ≫ e.hom).hom a = a
    rw [Iso.inv_hom_id]
    rfl
  rw [h3] at h2
  exact h2

end GlobalTheory.LogKSDiv.LocalExt

namespace GlobalTheory.LogKSDiv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem stalkHom_eq_stalkMap (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) (r : Γ(TF.Y.X, U.1)) :
    stalkHom TF Z x U hx r = ((barComp TF.Y Z).ι.stalkMap x).hom (TF.Y.X.presheaf.germ U.1 _ hx r) :=
  (Scheme.Hom.germ_stalkMap_apply _ _ _ _ _).symm

theorem stalkHom_frac (TF : TorFlag Xo c) (Z : Comp Xo c) (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens)
    (hx : (barComp TF.Y Z).ι x ∈ U.1) (a : (X₀ TF.Y Z).presheaf.stalk x) :
    ∃ r s : Γ(TF.Y.X, U.1), IsUnit (stalkHom TF Z x U hx s) ∧ a * stalkHom TF Z x U hx s = stalkHom TF Z x U hx r := by
  obtain ⟨r, s, hu, e⟩ := LocalExt.exists_frac_germ (barComp TF.Y Z) x U hx a
  exact ⟨r, s, by rw [stalkHom_eq_stalkMap]; exact hu, by rw [stalkHom_eq_stalkMap, stalkHom_eq_stalkMap]; exact e⟩

end GlobalTheory.LogKSDiv

theorem GlobalTheory.LogKSDiv.exists_stalkDer_extend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), (∀ r, ρ r = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r)) → ∀ (d : Fin Dw.dim → Derivation ℤ Γ(TF.Y.X, U.1) Γ(TF.Y.X, U.1)) (D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ (d j r)) → letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∃ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j a, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField a) = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (δ j a)) ∧ ∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx (d j r) := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ x U _ hx ρ hρ d D hD
  letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra
  letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra
  have key := fun j => GlobalTheory.LogKSDiv.LocalExt.exists_restrict_der (k := c.F)
    (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField)
    (IsFractionRing.injective _ _)
    (fun c => RingHom.congr_fun (GlobalTheory.LogKSDiv.algebraMap_comp_stalkAlg TF Z x) c)
    (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx) (GlobalTheory.LogKSDiv.stalkHom_frac TF Z x U hx) (d j) (D j)
    (fun r => by rw [← hρ, ← hρ]; exact hD j r)
  choose δ h1 h2 using key
  exact ⟨δ, h1, h2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesExtendingRegularParameters
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

open scoped TensorProduct

namespace GlobalTheory.CoordExt

theorem formallySmooth_of_charZero (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] :
    Algebra.FormallySmooth F K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  haveI := hs.isAlgebraic_field
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : CharZero (IntermediateField.adjoin F (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap F _).injective
  haveI : Algebra.IsSeparable (IntermediateField.adjoin F (Set.range ((↑) : s → K))) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

theorem span_D_algebraMap_eq_top (F A R : Type) [Field F] [CommRing A] [CommRing R]
    [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime]
    [IsLocalization.AtPrime R P] :
    Submodule.span R (Set.range fun y : A => KaehlerDifferential.D F R (algebraMap A R y)) = ⊤ := by
  set S := Submodule.span R (Set.range fun y : A => KaehlerDifferential.D F R (algebraMap A R y))
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl r
  have hu : IsUnit (algebraMap A R s) := IsLocalization.map_units R s
  obtain ⟨v, hv⟩ := hu.exists_left_inv
  have key : algebraMap A R s • KaehlerDifferential.D F R (IsLocalization.mk' R y s) =
      KaehlerDifferential.D F R (algebraMap A R y) -
        IsLocalization.mk' R y s • KaehlerDifferential.D F R (algebraMap A R s) := by
    rw [eq_sub_iff_add_eq, add_comm, ← Derivation.leibniz, IsLocalization.mk'_spec]
  have hmem : algebraMap A R s • KaehlerDifferential.D F R (IsLocalization.mk' R y s) ∈ S := by
    rw [key]
    exact sub_mem (Submodule.subset_span ⟨y, rfl⟩)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩))
  have : KaehlerDifferential.D F R (IsLocalization.mk' R y s) =
      v • (algebraMap A R s • KaehlerDifferential.D F R (IsLocalization.mk' R y s)) := by
    rw [smul_smul, hv, one_smul]
  change _ ∈ S
  rw [this]
  exact Submodule.smul_mem _ _ hmem

theorem span_tmul_eq_top {R M : Type} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    {ι : Type} (f : ι → M) (hf : Submodule.span R (Set.range f) = ⊤) :
    Submodule.span (IsLocalRing.ResidueField R)
      (Set.range fun i => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f i) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.TensorUnitSpanTop.main
  | exact _root_.GlobalTheory.TensorUnitSpanTop.main
  | (apply _root_.GlobalTheory.TensorUnitSpanTop.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.TensorUnitSpanTop.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TensorUnitSpanTop.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TensorUnitSpanTop.main ..)

end GlobalTheory.CoordExt


open GlobalTheory.CoordExt in
theorem GlobalTheory.exists_coords_extending_regularParams : ∀ (F A R : Type) [Field F] [CharZero F] [CommRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (n : ℕ) [Module.Free R Ω[R⁄F]] [Module.Finite R Ω[R⁄F]], Module.finrank R Ω[R⁄F] = n → ∀ (m : ℕ) (a : Fin m → A), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m (fun i => algebraMap A R (a i)) → ∃ (x : Fin n → A) (e : Fin m ↪ Fin n), (∀ j, x (e j) = a j) ∧ ∃ bs : Module.Basis (Fin n) R Ω[R⁄F], ∀ i, bs i = KaehlerDifferential.D F R (algebraMap A R (x i)) := by
  classical
  intro F A R _ _ _ _ _ _ _ _ _ _ _ P _ _ n _ _ hn m a hrsp
  haveI : Algebra.FormallySmooth F (IsLocalRing.ResidueField R) := formallySmooth_of_charZero F _
  set r : Fin m → R := fun i => algebraMap A R (a i) with hr_def
  have hr : ∀ i, r i ∈ IsLocalRing.maximalIdeal R := fun i => hrsp.1 ▸ Ideal.subset_span ⟨i, rfl⟩

  have hcot : LinearIndependent (IsLocalRing.ResidueField R) (fun i =>
      ((IsLocalRing.maximalIdeal R).toCotangent ⟨r i, hr i⟩ : IsLocalRing.CotangentSpace R)) := by
    have hfr : Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.CotangentSpace R) = m := by
      have := (IsRegularLocalRing.iff_finrank_cotangentSpace R).1 inferInstance
      rw [← hrsp.2] at this
      exact_mod_cast this
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by simp [hfr])
    have hsp : Submodule.span R (Set.range fun i => (⟨r i, hr i⟩ : IsLocalRing.maximalIdeal R)) = ⊤ := by
      apply Submodule.map_injective_of_injective (IsLocalRing.maximalIdeal R).injective_subtype
      rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
      exact hrsp.1
    rw [← IsLocalRing.CotangentSpace.span_image_eq_top_iff] at hsp
    rw [← Set.range_comp] at hsp
    exact hsp.ge
  have hw := GlobalTheory.AdaptedFrame.linearIndependent_tmul_D (k := F) r hr hcot
  let φ : A → IsLocalRing.ResidueField R ⊗[R] Ω[R⁄F] :=
    fun y => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] KaehlerDifferential.D F R (algebraMap A R y)
  have hw' : LinearIndependent (IsLocalRing.ResidueField R) (φ ∘ a) := hw
  have ha : Function.Injective a := fun i j h => hw'.injective (by simp only [Function.comp_apply, h])
  have hli : LinearIndepOn (IsLocalRing.ResidueField R) φ (Set.range a) :=
    (linearIndepOn_range_iff ha φ).2 hw'
  obtain ⟨b, -, hab, hbsp, hbli⟩ := exists_linearIndepOn_extension hli (Set.subset_univ _)
  have hVsp : Submodule.span (IsLocalRing.ResidueField R) (Set.range φ) = ⊤ :=
    span_tmul_eq_top _ (span_D_algebraMap_eq_top F A R P)
  have hbtop : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField R) (Set.range fun y : b => φ y) := by
    rw [← Set.image_eq_range, ← hVsp, ← Set.image_univ]
    exact Submodule.span_le.2 hbsp
  let bV := Module.Basis.mk hbli hbtop
  haveI : Finite b := Module.Finite.finite_basis bV
  letI : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = n := by
    rw [← Module.finrank_eq_card_basis bV, Module.finrank_baseChange, hn]
  let σ := Fintype.equivFinOfCardEq hcard
  let e0 : Fin m ↪ b := ⟨fun j => ⟨a j, hab ⟨j, rfl⟩⟩, fun i j h => ha (congrArg Subtype.val h)⟩
  refine ⟨fun i => ((σ.symm i : b) : A), e0.trans σ.toEmbedding, fun j => by
    simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
    rfl, ?_⟩
  let ω : Fin n → Ω[R⁄F] := fun i => KaehlerDifferential.D F R (algebraMap A R (σ.symm i : b))
  have hb' : ∀ i, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] ω i = bV.reindex σ i := by
    intro i
    rw [Module.Basis.reindex_apply]
    exact (Module.Basis.mk_apply hbli hbtop _).symm
  have hspan := IsLocalRing.span_eq_top_of_tmul_eq_basis ω (bV.reindex σ) hb'
  have hli2 : LinearIndependent R ω :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge (by simp [hn])
  exact ⟨Module.Basis.mk hli2 hspan.ge, fun i => by rw [Module.Basis.mk_apply]⟩
end

