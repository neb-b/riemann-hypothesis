module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfBijectiveAffinePts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2696
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2444
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2759
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2501
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2462
public import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.SigmaMonoInConstant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0210
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussPropertyCodimOneChartHeightOnePrime
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionTowerAndHeightEqTwoDim
section
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi (mulN)

namespace GlobalTheory.AVTower

theorem finrank_torsion {k : Type} [Field k] (A : AbVar k) {N : ℕ} (hN : N ≠ 0)
    {S : Type} [CommRing S] [Algebra k S] [Module.Finite k S] (y : SpAlg k S ⟶ A.X)
    (h : IsPullback y.left (spMap (algebraMap k S)) (mulN A.X N).left η[A.X].left) :
    Module.finrank k S = N ^ (2 * A.dim) := by
  obtain ⟨hi, hd⟩ := GlobalTheory.MulIsogeny.mul_isogeny k A (N : ℤ) (by exact_mod_cast hN)
  obtain ⟨-, hfl, -, hrk⟩ := GlobalTheory.AV.AbVar.isogeny_flat_finrank k A A _ hi
  have hf : IsFinite ((N : ℤ) • 𝟙 A).hom.left := hi.1
  have e : ((N : ℤ) • 𝟙 A).hom = mulN A.X N := by
    rw [zsmul_hom, id_hom, GrpTangent.mulN_eq_pow, zpow_natCast]
  rw [e] at hf hfl hrk
  have h2 := Scheme.Hom.finrank_of_isPullback _ _ _ _ h (⊥ : PrimeSpectrum k)
  rw [hrk, hd, Int.natAbs_natCast] at h2
  rw [← h2, spMap, Scheme.Hom.finrank_SpecMap_algebraMap, Module.rankAtStalk_eq_finrank_of_free]
  rfl

theorem exists_tower (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] (A : AbVar k) :
    ∃ G : PDivGroup p k, G.height = 2 * A.dim ∧ Nonempty (G.TorsionTower A.X) := by
  have := A.ab.comm
  have hN : ∀ n : ℕ, 1 ≤ p ^ n := fun n => Nat.one_le_pow _ _ hp.out.pos
  choose R _ _ y h1 h2 H using fun n : ℕ => AbelianPDiv.exists_isPullback (A := A.X) A.ab (hN n)
  have h : ∀ n, AbelianPDiv.IsUnivTorsion (p ^ n) (y n) :=
    fun n => AbelianPDiv.isUnivTorsion_of_isPullback (y n) (H n)
  have hr : ∀ n (q : PrimeSpectrum k), Module.rankAtStalk (R n) q = (p ^ n) ^ (2 * A.dim) := fun n q => by
    rw [Module.rankAtStalk_eq_finrank_of_free]
    exact finrank_torsion A (pow_ne_zero _ hp.out.ne_zero) (y n) (H n)
  have hex : ∀ n : ℕ, letI := (h n).hopfAlgebra
      letI := (h (n + 1)).hopfAlgebra
      haveI := (h (n + 1)).isCocomm
      ∃ r : R (n + 1) →ₐc[k] R n, Function.Surjective r ∧
        RingHom.ker r = torsionIdeal (R := k) (A := R (n + 1)) (p ^ n) ∧
        DeRham.spOver (r : R (n + 1) →ₐ[k] R n) ≫ y (n + 1) = y n := fun n => by
    let O := k
    let S := R (n + 1)
    let R₀ := R n
    let x := y (n + 1)
    let y₀ := y n
    let N := p ^ n
    have h₀ : AbelianPDiv.IsUnivTorsion N y₀ := h n
    have h' : AbelianPDiv.IsUnivTorsion (p ^ (n + 1)) x := h (n + 1)
    have hy : y₀ ^ (p ^ (n + 1)) = 1 := by rw [pow_succ, pow_mul, h₀.1, one_pow]
    let _ := h₀.hopfAlgebra
    let _ := h'.hopfAlgebra
    have := h'.isCocomm
    let r := h'.lift y₀ hy
    have hr : DeRham.spOver r ≫ x = y₀ := h'.lift_y _ _
    have hc : ∀ {C : Type} [CommRing C] [Algebra O C] (f : R₀ →ₐ[O] C), DeRham.spOver (f.comp r) ≫ x = DeRham.spOver f ≫ y₀ :=
      fun f => h'.comp_lift_y f _ _
    have ht : ∀ {C : Type} [CommRing C] [Algebra O C] (f : S →ₐ[O] C),
        torsionIdeal (R := O) (A := S) N ≤ RingHom.ker f ↔ (DeRham.spOver f ≫ x) ^ N = 1 := fun {C} _ _ f => by
      rw [torsionIdeal_le_ker_iff, ← WithConv.ofConv_toConv f, ← h'.pow_y, WithConv.ofConv_toConv,
        ← h'.counitMap_y (Algebra.ofId O C)]
      exact ⟨fun e => by rw [e]; rfl, fun e => WithConv.ofConv_injective (h'.inj e)⟩
    let π := Ideal.Quotient.mkₐ O (torsionIdeal (R := O) (A := S) N)
    have hπ := (ht π).1 fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
    let s := h₀.lift _ hπ
    have hs : s.comp r = π := h'.inj ((hc s).trans (h₀.lift_y _ _))
    have hk : torsionIdeal (R := O) (A := S) N ≤ RingHom.ker r := (ht r).2 (by rw [hr, h₀.1])
    let r' : (S ⧸ torsionIdeal (R := O) (A := S) N) →ₐ[O] R₀ := Ideal.Quotient.liftₐ _ r hk
    have hr' : r'.comp π = r := Ideal.Quotient.liftₐ_comp _ _ _
    have hs' : r'.comp s = AlgHom.id O R₀ := h₀.inj (by
      rw [h₀.comp_lift_y, ← Category.assoc, DeRham.spOver_comp, hr', hr, PDiv.spOver_id, Category.id_comp])
    refine ⟨.ofAlgHom r (h'.inj ?_) (h'.inj ?_), fun b => ?_, le_antisymm (fun a ha => ?_) hk, hr⟩
    · exact (hc _).trans ((h₀.counitMap_y (AlgHom.id O O)).trans (h'.counitMap_y (AlgHom.id O O)).symm)
    · refine (h'.comulMap_y' _ (Algebra.TensorProduct.includeLeft.comp r)
        (Algebra.TensorProduct.includeRight.comp r) (fun a => by simp) (fun a => by simp)).trans ?_
      rw [hc, hc, hc]
      exact (h₀.comulMap_y (AlgHom.id O _)).symm
    · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (s b)
      refine ⟨a, (DFunLike.congr_fun hr' a).symm.trans ?_⟩
      exact (congrArg r' ha).trans (DFunLike.congr_fun hs' b)
    · have ha' : r a = 0 := ha
      have : π a = 0 := by rw [← hs, AlgHom.comp_apply, ha', map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
  choose r r1 r2 r3 using hex
  let G : PDivGroup p k :=
    { height := 2 * A.dim
      A := R
      hopf := fun n => (h n).hopfAlgebra
      cocomm := fun n => (h n).isCocomm
      finite := h1
      projective := h2
      rank_eq := fun n q => (hr n q).trans (pow_mul _ _ _).symm
      res := r
      res_surjective := r1
      ker_res := r2 }
  exact ⟨G, rfl, ⟨{
    y := y
    mul := fun n B _ _ => (h n).mul_y
    inj := fun n B _ _ _ _ => (h n).inj
    surj := fun n B _ _ z hz => ((h n).2 B z hz).exists
    res := r3 }⟩⟩

theorem height_eq {p : ℕ} [hp : Fact p.Prime] {k : Type} [Field k] (A : AbVar k) (G : PDivGroup p k)
    (t : G.TorsionTower A.X) : G.height = 2 * A.dim := by
  have P := (TorsionTower.isPullback_y p k G A.X t 1).map (Over.forget _)
  have e : (toUnit (SpAlg k (G.A 1))).left = spMap (algebraMap k (G.A 1)) := by
    simpa using Over.w (toUnit (SpAlg k (G.A 1)))
  simp only [Over.forget_map] at P
  rw [e] at P
  have hf := finrank_torsion A (pow_ne_zero 1 hp.out.ne_zero) (t.y 1) P
  have hr := G.rank_eq 1 ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  change Module.finrank k (G.A 1) = _ at hr
  rw [hf, pow_one, Nat.one_mul] at hr
  exact (Nat.pow_right_injective hp.out.two_le hr).symm

theorem exists_tower_and_height_eq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A : AbVar k),
    (∃ G : PDivGroup p k, Nonempty (G.TorsionTower A.X)) ∧
      ∀ (G : PDivGroup p k) (t : G.TorsionTower A.X), G.height = 2 * A.dim := by
  intro p _ k _ A
  obtain ⟨G, -, hG⟩ := exists_tower p k A
  exact ⟨⟨G, hG⟩, fun G t => height_eq A G t⟩

end GlobalTheory.AVTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedTestModelBaseChangeCompletedLoc
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
namespace GlobalTheory.Poinc.TestAtPt


set_option maxHeartbeats 1600000 in
theorem exists_uTest_isBC : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (ev : R →+* OO p), M.Cen U₀ x y → spMap ev ≫ (spMap j ≫ M.Z.fromSpecStalk x) = y → ∀ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ → ∃ (u : ρ.UTest p y₀) (ε : D.toPre.X ≃+ u.D.toPre.X), GlobalTheory.Poinc.TestAtPt.IsBC FinalForm gm U ev u ε := by
  intro o' Ω _ _ _ _ S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R _ _ _ j hBase hcpl G _ _ gm hgm D A U hLB hpsi p _ y ev hCen hev y₀ hAt
  obtain ⟨V, _, _, _, ev₀, i, hVc, hev₀, hi, hiinj, -, huniq⟩ :=
    GlobalTheory.ClassicalPt.extend_completion o' Ω M x R j hcpl p y hCen.1
  have hevi : ev = i.comp ev₀ := huniq ev hev
  have hinj : Function.Injective ((OO p).subtype.comp i) := Subtype.val_injective.comp hiinj
  letI alg : Algebra (FractionRing V) (PadicAlgCl p) := (IsFractionRing.lift (K := FractionRing V) hinj).toAlgebra
  haveI := ArithBase.ded (o := o') (Ω := Ω)
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  let Wab : M.Z.Opens := ⟨abLocus FinalForm.G, GlobalTheory.AbLocusOpenGlobal.isOpen_abLocus_of_locallyNoetherian FinalForm.G FinalForm.semi⟩
  let W : (Sp R).Opens := (spMap j ≫ M.Z.fromSpecStalk x) ⁻¹ᵁ Wab
  have hgenU : (spMap j ≫ M.Z.fromSpecStalk x) (spMap ev₀ (genericPoint (Sp V))) ∈ U₀ := by
    have hw := hCen.2 ⟨genericPoint (Sp (PadicAlgCl p)), rfl⟩
    have e2 : (spMap ((OO p).subtype.comp i)).base (genericPoint (Sp (PadicAlgCl p))) = genericPoint (Sp V) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap ((OO p).subtype.comp i) ⊥ = ⊥
      exact Ideal.comap_bot_of_injective _ hinj
    have e3 : gPt p ≫ y = spMap ((OO p).subtype.comp i) ≫ spMap ev₀ ≫ spMap j ≫ M.Z.fromSpecStalk x := by
      rw [← hev, hevi]
      simp only [gPt, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [e3] at hw
    rw [← e2]; exact hw
  have hU₀ab : (U₀ : Set M.Z) ⊆ abLocus FinalForm.G := _root_.GlobalTheory.ZH.abLocus_of_over₀ o' Ω S ρ M U₀ EE FinalForm hAdm.1
  have hgenW : spMap ev₀ (genericPoint (Sp V)) ∈ W := hU₀ab hgenU
  have hsemi : IsSemiAbelian G := by
    obtain ⟨e, he, -⟩ := grpPullback_iso hgm (isGrpPullback_pullback FinalForm.G _)
    haveI := he
    exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback _ FinalForm.G FinalForm.semi)
  have hadm : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hVc⟩
  obtain ⟨D', A', hD, U', hU'⟩ := _root_.GlobalTheory.Mum.unif_baseChange_of_psiUnitOn R hBase D A G hsemi U V hadm ev₀ hev₀ W hpsi hgenW
    ((Over.pullback (specOf ev₀)).obj G) (Iso.refl _) (show IsMonHom (𝟙 _) from ⟨by simp, by simp⟩)
  have hgenV : (jK V).base (genericPoint (Sp (FractionRing V))) = genericPoint (Sp V) := by
    rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap V (FractionRing V)) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective V (FractionRing V))
  have hrange : Set.range (jK V ≫ spMap ev₀ ≫ spMap j ≫ M.Z.fromSpecStalk x).base ⊆ Set.range U₀.ι.base := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hw : w = genericPoint (Sp (FractionRing V)) := Subsingleton.elim _ _
    subst hw
    show (spMap j ≫ M.Z.fromSpecStalk x).base ((spMap ev₀).base ((jK V).base _)) ∈ U₀
    rw [hgenV]; exact hgenU
  obtain ⟨m, hm⟩ : ∃ m : Sp (FractionRing V) ⟶ U₀.toScheme,
      m ≫ U₀.ι = jK V ≫ spMap ev₀ ≫ spMap j ≫ M.Z.fromSpecStalk x :=
    ⟨IsOpenImmersion.lift U₀.ι _ hrange, IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨yK, hyK⟩ : ∃ yK : S.R →+* FractionRing V, spMap yK = m ≫ FinalForm.u₀ :=
    ⟨(Spec.preimage (m ≫ FinalForm.u₀)).hom, Spec.map_preimage _⟩
  have hval : ∀ (K : Type) [Field K] (q : Sp K ⟶ U₀.toScheme) (f : S.R →+* K), spMap f = q ≫ FinalForm.u₀ →
      ∀ a : S.R, M.val (q ≫ U₀.ι) (a : Ω) = f a :=
    fun K _ q f hf a => _root_.GlobalTheory.Poinc.TestAtPt.val_eq_of_spMap o' Ω M U₀ S.R FinalForm.u₀ hAdm.1.ne FinalForm.u₀_gen K q f hf a
  have hlift : ∀ v : V, algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) v) = (i v : PadicAlgCl p) :=
    fun v => IsFractionRing.lift_algebraMap (K := FractionRing V) hinj v
  have e1 : gPt p ≫ spMap (i.comp ev₀) = spMap (algebraMap (FractionRing V) (PadicAlgCl p)) ≫ jK V ≫ spMap ev₀ := by
    simp only [gPt, spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext v
    exact (hlift (ev₀ v)).symm
  have hgy : gPt p ≫ y = (spMap (algebraMap (FractionRing V) (PadicAlgCl p)) ≫ m) ≫ U₀.ι := by
    rw [Category.assoc, hm, ← hev, hevi, ← Category.assoc, e1]
    simp only [Category.assoc]
  have hfac : (algebraMap (FractionRing V) (PadicAlgCl p)).comp yK = y₀ := by
    ext a
    rw [hAt a, hgy, hval (PadicAlgCl p) _ ((algebraMap (FractionRing V) (PadicAlgCl p)).comp yK)]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    rw [← hyK]
  have hid : IsMonHom (Iso.refl ((Over.pullback (specOf ev₀)).obj G)).hom := show IsMonHom (𝟙 _) from ⟨by simp, by simp⟩
  have hβ : (genMap U' ≫ pullback.fst G.hom (specOf ev₀) ≫ gm) ≫ FinalForm.G.hom = A'.A.hom ≫ m ≫ U₀.ι := by
    rw [hm]
    simp only [genMap, Category.assoc]
    rw [hgm.1.w, pullback.condition_assoc]
    have h1 : pullback.fst ((Over.pullback (specOf ev₀)).obj G).hom (jK V) ≫ pullback.snd G.hom (specOf ev₀) =
        pullback.snd ((Over.pullback (specOf ev₀)).obj G).hom (jK V) ≫ jK V :=
      pullback.condition
    rw [reassoc_of% h1]
    have h2 : U'.gen.inv.left ≫ pullback.snd ((Over.pullback (specOf ev₀)).obj G).hom (jK V) = A'.A.hom := Over.w U'.gen.inv
    rw [reassoc_of% h2]
  obtain ⟨t, ht₁, ht₂⟩ : ∃ t : A'.A.left ⟶ pullback ρ.P.A.hom FinalForm.u₀,
      t ≫ FinalForm.φ = genMap U' ≫ pullback.fst G.hom (specOf ev₀) ≫ gm ∧ t ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = A'.A.hom ≫ m :=
    ⟨FinalForm.cart.1.lift _ _ hβ, FinalForm.cart.1.lift_fst _ _ _, FinalForm.cart.1.lift_snd _ _ _⟩
  have hcart : IsGrpPullback A'.A ρ.P.A (spMap yK) (t ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) := by
    haveI := U'.gen_hom
    haveI : IsMonHom U'.gen.symm.hom := by show IsMonHom U'.gen.inv; infer_instance
    have c1 : IsGrpPullback A'.A ((Over.pullback (jK V)).obj ((Over.pullback (specOf ev₀)).obj G)) (𝟙 _)
        U'.gen.symm.hom.left := isGrpPullback_of_iso U'.gen.symm
    have c := ((c1.comp (isGrpPullback_pullback _ (jK V))).comp (isGrpPullback_pullback G (specOf ev₀))).comp hgm
    have n : IsGrpPullback A'.A FinalForm.G (m ≫ U₀.ι) (t ≫ FinalForm.φ) := by
      refine c.congr ?_ ?_
      · rw [hm]; simp [specOf, jK, spMap]
      · rw [ht₁]; simp only [genMap, Category.assoc]; rfl
    have c4 := IsGrpPullback.cancel FinalForm.cart n ht₂
    exact (c4.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)).congr hyK.symm rfl
  have hlb : LBIso A'.L (ρ.P.L.pull (t ≫ pullback.fst ρ.P.A.hom FinalForm.u₀)) := by
    obtain ⟨wE, hwE⟩ := U'.ext
    obtain ⟨wL, hwL, -⟩ := hU'.lg
    refine _root_.GlobalTheory.LbChain.lbIso_chain A'.L U'.LG.L U.LG.L FinalForm.L.L ρ.P.L U'.gen.hom.left U'.gen.inv.left
      (pullback.fst _ (jK V)) ((Iso.refl ((Over.pullback (specOf ev₀)).obj G)).hom.left ≫ pullback.fst G.hom (specOf ev₀)) gm
      FinalForm.φ (pullback.fst ρ.P.A.hom FinalForm.u₀) t A'.isLB U'.LG.isLB U.LG.isLB FinalForm.L.isLB ρ.P.isLB ?_ ⟨wE, hwE⟩ ⟨wL, hwL⟩ hLB
      ⟨FinalForm.w, FinalForm.w_gen⟩ ?_
    · rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
    · rw [ht₁]; simp only [genMap, Iso.refl_hom, Over.id_left, Category.assoc]; erw [Category.id_comp]
  refine ⟨⟨V, hVc, ?_, yK, hfac, A', t ≫ pullback.fst ρ.P.A.hom FinalForm.u₀, hcart, hlb, (Over.pullback (specOf ev₀)).obj G,
    IsSemiAbelian.pullback _ G hsemi, D', U'⟩, hD.xe.symm, ?_⟩
  · exact fun x => GlobalTheory.T.dvr_fractionLift_padicAlgClosure_norm_le_one_iff p V i hi hinj x
  · refine ⟨ev₀, hev₀, hD, Iso.refl _, hid, hU', fun χ => hD.xe.apply_symm_apply χ, fun r => ?_, t, rfl, ?_⟩
    · rw [hlift, hevi]; rfl
    · exact ht₁.trans (by simp only [Iso.refl_hom, Over.id_left]; erw [Category.id_comp])

end GlobalTheory.Poinc.TestAtPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAndAwayFormula
section
namespace LeafFixedPointPairing
section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw matLat)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.IndefR.Datum Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta

namespace GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_localization_of_smul_mem₂ {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ} (w : HeightOneSpectrum (𝓞 K))
    (M : Submodule (𝓞 K) (Fin n → K)) (y : Fin n → K) (s : K) (hs : s ≠ 0) (δ : ℤ) (hv : vw w s ≤ δ) (h : s • y ∈ M) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul
      (((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-δ) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M) := by
  obtain ⟨t, ht, hc⟩ := unit_at_val w s hs
  have h1 : s • y ∈ Formalism.HermitianLatticesTheory.idealSmul
      (((1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) : Submodule (𝓞 K) K) M := by
    refine Submodule.subset_span ⟨1, ?_, s • y, h, (one_smul _ _).symm⟩
    exact FractionalIdeal.mem_coe.mpr (FractionalIdeal.one_mem_one _)
  have hm := smulK_mem_idealSmul _ _ M _ hc h1
  rw [one_mul] at hm
  have e : (algebraMap (𝓞 K) K t * s⁻¹) • s • y = t • y := by
    rw [smul_smul, mul_assoc, inv_mul_cancel₀ hs, mul_one, algebraMap_smul]
  rw [e] at hm
  exact GlobalTheory.FinitePlacesCompare.scaledAt_anti w M (neg_le_neg hv)
    ((PI.LocGlobInclWork.mem_localization_iff _ _ _).mpr ⟨t, ht, hm⟩)

variable {D : D7}

theorem absNorm_splitAuxiliaryPlace_eq_prime {T : Type} {Lc : LevCh D T} (P : GlobalTheory.ChiGrid.Places Lc) :
    Ideal.absNorm P.v0.asIdeal = GlobalTheory.ChiGrid.q0 D := by
  have hp := (GlobalTheory.ChiGrid.leastSplitAuxiliaryPrimeThetaChain_spec D).1
  have h : (Ideal.primesOver (Ideal.span {((GlobalTheory.ChiGrid.q0 D : ℕ) : ℤ)}) (𝓞 D.host.E)).ncard =
      Module.finrank ℚ D.host.E := by
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp]
    exact Formalism.L2.Host.split_prime_splits_completely D
  have := P.v0.isPrime
  have := (GlobalTheory.ColClassCompare.unram_card_of_split (F := D.host.F) (E := D.host.E) hp h P.v0.asIdeal P.basePlace_over_qZero).2
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact this

theorem one_le_b (s : Formalism.BasicNotions.Scale) : 1 ≤ s.b := by
  have h : 0 ≤ s.L := Real.rpow_nonneg (by linarith [s.one_lt_alt]) _
  exact Real.one_le_exp h

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem sig_le {p : PtAt ex Csz} {CF C : ℝ} (d : FunIn p CF) (Tf : Finset (GlobalTheory.SumSize.PlL D)) (dF : GlobalTheory.SumSize.PlL D → ℤ) (hC : CF ≤ C) :
    sig d.G ≤ (d.data (fun _ => 1) Tf dF).Sig0 C p.Z.b := by
  have hb : 1 ≤ p.Z.b := one_le_b L.sc
  refine le_trans (le_of_eq ?_) (GlobalTheory.FinitePlacesProbe.sigma_mono_in_constant _ hC hb)
  show _ = ∑ q ∈ d.G.pl.S0, ((d.O.ee CF p.Z.b q : ℕ) : ℝ) * Real.log (Ideal.absNorm q.asIdeal)
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [GlobalTheory.BigTop.Fun.Model.ee_eq d (absNorm_splitAuxiliaryPlace_eq_prime d.G.pl) v]

theorem local_clause {p : PtAt ex Csz} {CF : ℝ} {d : FunIn p CF} {a : SlopeTestRemainingChoices p d.G d.W d.n} (hT : TieAt d a)
    {dl : GlobalTheory.SumSize.PlL D → ℝ} (hloc : ∀ X' M, IsTestLat a.ch.G a.ch.rp a.ch.n a.ch.e X' M →
      ∀ t w, Away a.ch.G t w → ∀ x ∈ (p.P.A3.A.fam.R t).Mt (p.P.A3.A.fam.lvl p.F.lv2.P0 p.F.lv2.ψ0), ∀ y : Fin a.ch.n → D.what₂.LL,
        (∀ i, D.what₂.embLL (y i) = vK a.ch t (formOf p.F.lv2 t x) i) → ∃ s : D.what₂.LL, s ≠ 0 ∧ (vw w s : ℝ) ≤ dl w ∧ s • y ∈ M)
    (hAw : AwayAt (R := p.R.toRealDat) a.ch) (Tf : Finset (GlobalTheory.SumSize.PlL D)) (dF : GlobalTheory.SumSize.PlL D → ℤ) (hF : ∀ w, dF w = ⌊dl w⌋) (w : GlobalTheory.SumSize.PlL D) :
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat ((d.data (fun _ => 1) Tf dF).vmu ((p.S false).μ w)) ((Df p).Mt ((p.S false).μ w))) ≤
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (Formalism.HermitianLatticesTheory.idealSmul
        (((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) ^ (-((d.data (fun _ => 1) Tf dF).dF w)) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.what₂.LL)) D.what₂.LL) : Submodule (𝓞 D.what₂.LL) D.what₂.LL) (d.data (fun _ => 1) Tf dF).M) := by
  intro z hz
  obtain ⟨s0, hs0, hz0⟩ := (PI.LocGlobInclWork.mem_localization_iff _ _ _).mp hz
  obtain ⟨x, hx, hxz⟩ := Submodule.mem_map.mp hz0
  have e0 : (d.data (fun _ => 1) Tf dF).vmu ((p.S false).μ w) = d.V ((p.S false).μ w) := by
    show (1 : D.what₂.LL)⁻¹ • d.V _ = _
    simp
  simp only [LinearMap.coe_restrictScalars, e0] at hxz
  obtain ⟨s, hs, hv, hsM⟩ := hloc d.X' d.M hT.test ((p.S false).μ w) w (hAw w) x hx (d.V _ |>.mulVec x)
    (fun i => hT.sums _ (Or.inr ⟨w, rfl⟩) x i)
  have hy := mem_localization_of_smul_mem₂ w d.M _ s hs (dF w) (by rw [hF]; exact Int.le_floor.mpr hv) hsM
  obtain ⟨s1, hs1, h1⟩ := (PI.LocGlobInclWork.mem_localization_iff _ _ _).mp hy
  refine (PI.LocGlobInclWork.mem_localization_iff _ _ _).mpr ⟨s1 * s0, w.asIdeal.primeCompl.mul_mem hs1 hs0, ?_⟩
  rw [mul_smul, ← hxz]
  exact h1

theorem sum_clause {p : PtAt ex Csz} {CF C : ℝ} (d : FunIn p CF) (hC0 : 0 ≤ C) (hC : CF ≤ C) {dl : GlobalTheory.SumSize.PlL D → ℝ}
    (hsum : ∀ s : Finset (GlobalTheory.SumSize.PlL D), ∑ w ∈ s, lw w * dl w ≤ D.R.m * bOne d.G C p.Z.b / 2)
    (Tf : Finset (GlobalTheory.SumSize.PlL D)) (dF : GlobalTheory.SumSize.PlL D → ℤ) (hF : ∀ w, dF w = ⌊dl w⌋) :
    2 * ∑ w ∈ Tf, lw w * (dF w : ℝ) ≤ (d.data (fun _ => 1) Tf dF).bFP C p.Z.b := by
  have hb : 1 ≤ p.Z.b := one_le_b L.sc
  have hb0 : 0 ≤ p.Z.b := by linarith
  have hL : 0 ≤ Real.log p.Z.b := Real.log_nonneg hb
  have h1 : ∑ w ∈ Tf, lw w * (dF w : ℝ) ≤ ∑ w ∈ Tf, lw w * dl w := by
    refine Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left ?_ (GlobalTheory.FinitePlacesCompare.lw_nonneg w)
    rw [hF]
    exact Int.floor_le _
  have h2 := hsum Tf
  have hS := sig_le d Tf dF hC
  have hS0 := Sig0_nonneg (d.data (fun _ => 1) Tf dF) C p.Z.b
  have hN : (d.data (fun _ => 1) Tf dF).N = bigN D := GlobalTheory.BigTop.Fun.Model.N_eq d
  unfold FunData.bFP
  rw [hN]
  show _ ≤ C * (D.R.f : ℝ) * p.Z.b * (bigN D : ℝ) * (D.R.m : ℝ) * ((D.R.m : ℝ) * Real.log p.Z.b + (D.R.m : ℝ) * _) +
    C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (Real.log p.Z.b + _) * p.Z.b
  set S := (d.data (fun _ => 1) Tf dF).Sig0 C p.Z.b
  have h3 : 0 ≤ C * (D.R.f : ℝ) * p.Z.b * (bigN D : ℝ) * (D.R.m : ℝ) * ((D.R.m : ℝ) * Real.log p.Z.b + (D.R.m : ℝ) * S) := by
    positivity
  have h4 : (D.R.m : ℝ) * bOne d.G C p.Z.b ≤ C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (Real.log p.Z.b + S) * p.Z.b := by
    unfold bOne
    have : (D.R.m : ℝ) * (C * D.R.f * D.R.m * (bigN D : ℝ) ^ 2 * (Real.log p.Z.b + sig d.G) * p.Z.b) =
        C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (Real.log p.Z.b + sig d.G) * p.Z.b := by ring
    rw [this]
    gcongr
  linarith

theorem leaf_at {p : PtAt ex Csz} {CF C : ℝ} {d : FunIn p CF} {a : SlopeTestRemainingChoices p d.G d.W d.n} (hT : TieAt d a) (hC0 : 0 ≤ C) (hC : CF ≤ C)
    (hFin : FinAt p.F.lv2 a.ch C p.Z.b) (hAw : AwayAt (R := p.R.toRealDat) a.ch) :
    ∃ Tf dF, LeafFP (d.data (fun _ => 1) Tf dF) (p.S false).μ C p.Z.b := by
  classical
  obtain ⟨dl, ⟨-, hfin, hsum⟩, hloc⟩ := hFin
  refine ⟨hfin.toFinset, fun w => ⌊dl w⌋, ?_, fun w hw => ?_, ?_⟩
  · exact local_clause hT hloc hAw _ _ (fun _ => rfl)
  · have hw' : w ∉ hfin.toFinset := hw
    have : dl w = 0 := by simpa using hw'
    show ⌊dl w⌋ = 0
    simp [this]
  · exact sum_clause d hC0 hC hsum _ _ (fun _ => rfl)

end GlobalTheory.CompanionTheory.LeafFixedPointPlaceNorm

end

end

end LeafFixedPointPairing
section
open GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SumSize

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallMemRegularChartIffHeightOnePrimes
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem ringKrullDim_stalk_le_of_flat {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] (z : X) :
    ringKrullDim (Y.presheaf.stalk (f z)) ≤ ringKrullDim (X.presheaf.stalk z) := by
  letI : Algebra (Y.presheaf.stalk (f z)) (X.presheaf.stalk z) := (f.stalkMap z).hom.toAlgebra
  haveI : Module.Flat (Y.presheaf.stalk (f z)) (X.presheaf.stalk z) := Flat.stalkMap f z
  haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f z)) (X.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap z).hom)
  haveI : Algebra.HasGoingDown (Y.presheaf.stalk (f z)) (X.presheaf.stalk z) := Algebra.HasGoingDown.of_flat
  exact GroundTheory.Arith.SchemeCoh.ringKrullDim_le_of_hasGoingDown

theorem Setup.height_under_vert (σ : Setup) (x : Sp σ.R) (z : (σ.C x).G.left)
    (hz : Vert (σ.C x).G.hom (σ.ρ x σ.f) z) :
    (spMap (σ.ρ x) ((σ.C x).G.hom z)).asIdeal.height = 1 := by
  haveI := (σ.C x).semi.smooth
  haveI : Flat (spMap (σ.ρ x)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact σ.flat x
  have h1 := (ringKrullDim_stalk_le_of_flat (spMap (σ.ρ x)) ((σ.C x).G.hom z)).trans
    (ringKrullDim_stalk_le_of_flat (σ.C x).G.hom z)
  rw [hz.1] at h1
  have hf : σ.f ∈ (spMap (σ.ρ x) ((σ.C x).G.hom z)).asIdeal := hz.2
  generalize spMap (σ.ρ x) ((σ.C x).G.hom z) = p at h1 hf ⊢
  letI : Algebra σ.R ((Sp σ.R).presheaf.stalk p) := StructureSheaf.stalkAlgebra σ.R p
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := σ.R) p
  haveI : IsLocalization.AtPrime ((Sp σ.R).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk σ.R p
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal] at h1
  refine le_antisymm (by exact_mod_cast h1) ?_
  have hlt : (⊥ : Ideal σ.R) < p.asIdeal := bot_lt_iff_ne_bot.2 fun h => σ.hf (by rwa [h, Ideal.mem_bot] at hf)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  exact le_add_self.trans h2

theorem Setup.forall_mem_W_iff : ∀ (σ : Setup) (u : σ.A.left.functionField),
    (∀ x : Sp σ.R, u ∈ σ.W x) ↔ ∀ p : Sp σ.R, p.asIdeal.height = 1 → σ.f ∈ p.asIdeal → u ∈ σ.W p := by
  intro σ u
  refine ⟨fun h p _ _ => h p, fun h x z hz => ?_⟩
  have h1 := h _ (σ.height_under_vert x z hz) hz.2
  rw [← (_root_.GlobalTheory.Desc.GaussPt.gaussAt_vert σ x z hz).2] at h1
  exact h1

end GlobalTheory.Desc
end

