module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0004
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0017
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0059
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgIsoPts
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private lemma etale_specMap (D E : Type) [CommRing D] [CommRing E] [Algebra D E] [Algebra.Etale D E] :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap D E))) := by
  apply HasRingHomProperty.Spec_iff.mpr
  exact RingHom.etale_algebraMap.mpr ‹_›

theorem UpperTheory.Gal.G3.pAlgIsoPts :
    IsoPts → AlgIsoPts := by
  intro hI D E _ _ _ _ hpts
  let φ : CommRingCat.of D ⟶ CommRingCat.of E := CommRingCat.ofHom (algebraMap D E)
  have : Etale (Spec.map φ) := etale_specMap D E
  have hiso : IsIso (Spec.map φ) := by
    refine hI (Spec.map φ) ?_
    intro Ω _ _ z
    obtain ⟨y, hy, hyu⟩ := hpts Ω (Spec.preimage z).hom
    refine ⟨Spec.map (CommRingCat.ofHom y), ?_, ?_⟩
    · show Spec.map (CommRingCat.ofHom y) ≫ Spec.map φ = z
      rw [← Spec.map_comp]
      conv_rhs => rw [← Spec.map_preimage z]
      congr 1
      ext d
      exact congrArg (fun f : D →+* Ω => f d) hy
    · intro w hw
      rw [← Spec.map_preimage w]
      congr 1
      ext e
      have hx : (Spec.preimage w).hom.comp (algebraMap D E) = (Spec.preimage z).hom := by
        have h2 : Spec.map (φ ≫ Spec.preimage w) = Spec.map (Spec.preimage z) := by
          rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
          exact hw
        have h3 := Spec.map_injective h2
        ext d
        exact congrArg (fun f => (CommRingCat.Hom.hom f) d) h3
      exact congrArg (fun f : E →+* Ω => f e) (hyu _ hx)
  have hφ : IsIso φ := by
    refine ⟨⟨Spec.preimage (inv (Spec.map φ)), ?_, ?_⟩⟩
    · apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_id, IsIso.inv_hom_id]
    · apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage, Spec.map_id, IsIso.hom_inv_id]
  exact ConcreteCategory.bijective_of_isIso φ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgSplit
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

namespace UpperTheory.Gal.G3.AlgebraSplitting

private noncomputable def sec {A A' C J : Type} [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C]
    (τ : J → (A' →ₐ[A] C)) : C ⊗[A] A' →ₐ[C] (J → C) :=
  Pi.algHom C (fun _ => C) fun j =>
    Algebra.TensorProduct.lift (AlgHom.id C C) (τ j) fun _ _ => Commute.all _ _

private lemma sec_tmul {A A' C J : Type} [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C]
    (τ : J → (A' →ₐ[A] C)) (c : C) (b : A') (j : J) : sec τ (c ⊗ₜ b) j = c * τ j b := by
  simp [sec]

private lemma tensor_hom_ext {A A' C Ω : Type} [CommRing A] [CommRing A'] [CommRing C] [Algebra A A'] [Algebra A C]
    [CommRing Ω] {u v : C ⊗[A] A' →+* Ω} (h₁ : ∀ c : C, u (c ⊗ₜ 1) = v (c ⊗ₜ 1))
    (h₂ : ∀ b : A', u (1 ⊗ₜ b) = v (1 ⊗ₜ b)) : u = v :=
  _root_.UpperTheory.Reformulated.B.Qk54.tensor_hom_ext h₁ h₂

private lemma exists_eval {C Ω J : Type} [CommRing C] [Field Ω] [Fintype J] (f : (J → C) →+* Ω) :
    ∃ j, ∀ v : J → C, f v = f (algebraMap C (J → C) (v j)) :=
  _root_.UpperTheory.Reformulated.B.ExistsEvaluation.exists_eval f

private lemma bij_of_pts (hiso : AlgIsoPts) {C D E : Type} [CommRing C] [CommRing D] [CommRing E] [Algebra C D]
    [Algebra C E] [Algebra.Etale C D] [Algebra.Etale C E] (φ : D →ₐ[C] E)
    (pts : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : D →+* Ω), ∃! y : E →+* Ω, y.comp (φ : D →+* E) = x) :
    Function.Bijective φ := by
  letI : Algebra D E := (φ : D →+* E).toAlgebra
  haveI : IsScalarTower C D E := IsScalarTower.of_algebraMap_eq' (φ.comp_algebraMap).symm
  haveI : Algebra.Etale D E := Algebra.Etale.of_restrictScalars C D E
  exact hiso D E pts

end UpperTheory.Gal.G3.AlgebraSplitting

open UpperTheory.Gal.G3.AlgebraSplitting in
theorem UpperTheory.Gal.G3.pAlgSplit :
    AlgIsoPts → AlgSplit := by
  intro hiso A A' C _ _ _ _ _ _ J _ τ h
  refine ⟨AlgEquiv.ofBijective (sec τ) (bij_of_pts hiso (sec τ) ?_), fun b j => ?_⟩
  swap
  · simp [sec_tmul]
  intro Ω _ _ x
  let x₀ : C →+* Ω := x.comp (Algebra.TensorProduct.includeLeftRingHom)
  let y₀ : A' →+* Ω := x.comp (Algebra.TensorProduct.includeRight : A' →ₐ[A] C ⊗[A] A').toRingHom
  have hx₀ : ∀ c, x₀ c = x (c ⊗ₜ 1) := fun _ => rfl
  have hy₀ : ∀ b, y₀ b = x (1 ⊗ₜ b) := fun _ => rfl
  have compat : y₀.comp (algebraMap A A') = x₀.comp (algebraMap A C) := by
    ext a
    simp only [RingHom.comp_apply, hx₀, hy₀]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  obtain ⟨j, hj, huniq⟩ := h Ω x₀ y₀ compat
  have hτ : ∀ b, x₀ (τ j b) = y₀ b := fun b => congrArg (fun f : A' →+* Ω => f b) hj
  refine ⟨x₀.comp (Pi.evalRingHom (fun _ => C) j), ?_, ?_⟩
  · apply tensor_hom_ext
    · intro c
      simp [sec_tmul, hx₀]
    · intro b
      have := hτ b
      simp only [RingHom.comp_apply, RingHom.coe_coe, Pi.evalRingHom_apply, sec_tmul, one_mul]
      rw [this, hy₀]
  · intro y' hy'
    have hy'd : ∀ d, y' (sec τ d) = x d := fun d => congrArg (fun f : C ⊗[A] A' →+* Ω => f d) hy'
    obtain ⟨j', hj'⟩ := exists_eval y'
    have hal : ∀ c : C, y' (algebraMap C (J → C) c) = x₀ c := by
      intro c
      rw [hx₀, ← hy'd]
      congr 1
      funext i
      simp [sec_tmul]
    have hy'e : ∀ v : J → C, y' v = x₀ (v j') := fun v => by rw [hj', hal]
    have hjj : j' = j := by
      apply huniq
      ext b
      have := hy'e (sec τ (1 ⊗ₜ b))
      rw [hy'd, sec_tmul, one_mul] at this
      simpa [hy₀] using this.symm
    subst hjj
    ext v
    simp [hy'e]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgTr
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem trace_pi_eq_sum {C J : Type} [CommRing C] [Fintype J] (a : J → C) :
    Algebra.trace C (J → C) a = ∑ j, a j := by
  classical
  rw [Algebra.trace_apply, LinearMap.trace_eq_matrix_trace C (Pi.basisFun C J), Matrix.trace]
  apply Finset.sum_congr rfl
  intro j _
  simp [LinearMap.toMatrix_apply, Pi.single_apply]

theorem UpperTheory.Gal.G3.pAlgTr :
    AlgTr := by
  intro A A' C _ _ _ _ _ _ _ J _ τ e he b
  letI : Algebra A' (C ⊗[A] A') := Algebra.TensorProduct.rightAlgebra
  haveI : Module.Projective A A' := projective_of_etale A A'
  haveI : Module.Free C (C ⊗[A] A') := Module.Free.of_equiv e.symm.toLinearEquiv
  haveI : Module.Finite C (C ⊗[A] A') := Module.Finite.equiv e.symm.toLinearEquiv
  have h1 := algTrace_of_isPushout (B := A) (B' := A') (C := C) (C' := C ⊗[A] A') b
  have h2 : (etTrace A A') b = (algTrace A A') b := rfl
  rw [h2, ← h1, algTrace_eq_trace]
  have h3 : algebraMap A' (C ⊗[A] A') b = e.symm (e (1 ⊗ₜ[A] b)) := by
    rw [AlgEquiv.symm_apply_apply]
    rfl
  rw [h3, Algebra.trace_eq_of_algEquiv e.symm, trace_pi_eq_sum]
  exact Finset.sum_congr rfl fun j _ => he b j
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGal
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem bcMap_isPullback {B B' X Y : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} (f : Y ⟶ X)
    (h : f ≫ p = q) : IsPullback (pullback.fst q g) (bcMap g f h) f (pullback.fst p g) := by
  subst h
  refine IsPullback.of_bot ?_ (bcMap_fst g f rfl).symm (IsPullback.of_hasPullback p g)
  rw [bcMap_snd]
  exact IsPullback.of_hasPullback (f ≫ p) g

theorem UpperTheory.Gal.G3.pBcGal :
    BcSplits → BcGal := by
  intro hB B B' Z W g p r c hc G _ _ a ha hG
  obtain ⟨hfin, het, hsur, h1, hmul, hsp⟩ := hG
  obtain ⟨f1, f2, f3⟩ := @hB B B' Z W W g p r r c hc c hc G _ a ha hfin het
  refine ⟨f1, f2, ?_, ?_, ?_, f3 hsp⟩
  · exact MorphismProperty.of_isPullback (P := @Surjective) (bcMap_isPullback g c hc) hsur
  · apply pullback.hom_ext
    · rw [bcMap_fst, h1, Category.comp_id, Category.id_comp]
    · rw [bcMap_snd, Category.id_comp]
  · intro x y
    apply pullback.hom_ext
    · rw [bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc, bcMap_fst, Category.assoc, hmul]
    · rw [bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGood
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pBcGood :
    BcSplits → BcGal → BcGood.{u} := by
  intro hS hG B B' R _ T g hT
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a hgal
    have ha : ∀ x, a x ≫ r = r := fun x => by
      rw [← hc, ← Category.assoc, hgal.2.2.2.2.2.1 x]
    exact hT.inj (pullback.snd p g) (pullback.snd r g) (bcMap g c hc) (bcMap_snd g c hc) G
      (fun x => bcMap g (a x) (ha x)) (hG g p r c hc G a ha hgal)
  · intro Z Y p q s _ _ hs
    obtain ⟨hfin, het, -⟩ := hS g p q q s hs s hs Empty Empty.elim (fun j => j.elim)
    obtain ⟨tr, htr⟩ := hT.tr (pullback.snd p g) (pullback.snd q g) (bcMap g s hs) (bcMap_snd g s hs)
    refine ⟨tr, ?_⟩
    intro W r c hc J _ σ hσ hspl x
    exact htr (pullback r g) (pullback.snd r g) (bcMap g c hc) (bcMap_snd g c hc) J
      (fun j => bcMap g (σ j) (hσ j)) (fun j => bcMap_snd g (σ j) (hσ j))
      ((hS g p q r s hs c hc J σ hσ).2.2 hspl) x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcSplits
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem bc_isPullback {B B' Z Y : Scheme.{0}} (g : B ⟶ B') (p : Z ⟶ B') (s : Y ⟶ Z) :
    IsPullback (pullback.fst (s ≫ p) g) (bcMap g s rfl) s (pullback.fst p g) := by
  refine IsPullback.of_bot ?_ (bcMap_fst g s rfl).symm (IsPullback.of_hasPullback p g)
  rw [bcMap_snd]
  exact IsPullback.of_hasPullback (s ≫ p) g

theorem UpperTheory.Gal.G3.pBcSplits :
    SplitsBasic → BcSplits := by
  intro hb B B' Z Y W g p q r s hs c hc J _ σ hσ _ _
  subst hs
  subst hc
  have sq := bc_isPullback g p s
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) sq ‹_›,
    MorphismProperty.of_isPullback (P := @Etale) sq ‹_›, fun h => ?_⟩
  obtain ⟨h0, -⟩ := id h
  have hcomp : ∀ j, bcMap g (σ j) (hσ j) ≫ bcMap g s rfl = bcMap g c rfl := by
    intro j
    apply pullback.hom_ext
    · rw [Category.assoc, bcMap_fst g s rfl, ← Category.assoc, bcMap_fst g (σ j) (hσ j), Category.assoc, h0 j,
        bcMap_fst g c rfl]
    · rw [Category.assoc, bcMap_snd g s rfl, bcMap_snd g (σ j) (hσ j), bcMap_snd g c rfl]
  have e1 : bcMap g c rfl ≫ pullback.fst p g = pullback.fst (c ≫ p) g ≫ c := bcMap_fst g c rfl
  have e2 : (fun j => bcMap g (σ j) (hσ j) ≫ pullback.fst (s ≫ p) g) = fun j => pullback.fst (c ≫ p) g ≫ σ j :=
    funext fun j => bcMap_fst g (σ j) (hσ j)
  have h2 : Splits s (bcMap g c rfl ≫ pullback.fst p g)
      (fun j => bcMap g (σ j) (hσ j) ≫ pullback.fst (s ≫ p) g) := by
    rw [e1, e2]
    exact hb.1 s c J σ (pullback.fst (c ≫ p) g) h
  exact (hb.2 (pullback.fst (s ≫ p) g) (bcMap g s rfl) s (pullback.fst p g) sq (bcMap g c rfl) J
    (fun j => bcMap g (σ j) (hσ j)) hcomp).2 h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PCoverInv
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem pull_eq_of_eq {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {X Y : Scheme.{0}}
    {p : X ⟶ B} {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) (x : T.H p) :
    T.pull f h x = T.pull f' h' x := by
  subst e; rfl

private theorem splits_inv (hSP : SplitsPts) {Z Y : Scheme.{0}} (s : Y ⟶ Z) [IsIso s] :
    Splits s (𝟙 Z) (fun _ : Unit => inv s) := by
  refine hSP s (𝟙 Z) Unit _ (fun _ => by simp) ?_
  intro Ω _ _ x y hxy
  refine ⟨(), ?_, fun _ _ => rfl⟩
  rw [← cancel_mono s, hxy]
  simp

theorem UpperTheory.Gal.G3.pCoverInv :
    GalInv.{u} → SplitsPts → CoverInv.{u} := by
  intro hGal hSP k L O _ _ _ _ H θ C hC R _ _ T hT
  have hG := C.isGalois hC
  have ha : ∀ δ, C.a δ ≫ H.q = H.q := by
    intro δ
    obtain ⟨hspl, -⟩ := hG.2.2.2.2.2
    rw [← piK_snd C, ← Category.assoc]
    exact congrArg (· ≫ pullback.snd C.p (gen O k)) (hspl δ)
  refine ⟨hT.inj _ _ (piK C) (piK_snd C) C.Δ C.a hG, fun y hy => ?_⟩
  refine (hGal T hT _ _ (piK C) (piK_snd C) C.Δ C.a ha hG y).2 (fun δ => ?_)
  obtain ⟨g, hiso, hts, hθ⟩ := C.fix δ
  haveI := hiso
  obtain ⟨tr, htr, hfix⟩ := hy g hiso hθ
  have hq : inv (H.s g) ≫ (H.s g ≫ H.q) = H.q := by simp
  have key : ∀ z, tr z = T.pull (inv (H.s g)) hq z := by
    intro z
    have := htr H.Z H.q (𝟙 _) (by simp) Unit (fun _ => inv (H.s g)) (fun _ => hq)
      (splits_inv hSP (H.s g)) z
    rw [T.pull_id] at this
    simpa using this
  have h1 : (H.s g ≫ C.a δ) ≫ H.q = H.s g ≫ H.q := by rw [Category.assoc, ha]
  have h2 : (inv (H.s g) ≫ H.s g) ≫ H.q = H.q := by simp
  have h3 : 𝟙 H.Z ≫ H.q = H.q := by simp
  conv_rhs => rw [← hfix]
  rw [key]
  symm
  calc T.pull (inv (H.s g)) hq (T.pull (H.t g) (H.comm g) y)
      = T.pull (inv (H.s g)) hq (T.pull (H.s g ≫ C.a δ) h1 y) :=
        congrArg _ (pull_eq_of_eq T hts _ h1 y)
    _ = T.pull (inv (H.s g)) hq (T.pull (H.s g) rfl (T.pull (C.a δ) (ha δ) y)) := by
        rw [T.pull_comp (H.s g) (C.a δ) rfl (ha δ) h1]
    _ = T.pull (inv (H.s g) ≫ H.s g) h2 (T.pull (C.a δ) (ha δ) y) :=
        (T.pull_comp _ _ _ _ _ _).symm
    _ = T.pull (𝟙 H.Z) h3 (T.pull (C.a δ) (ha δ) y) :=
        pull_eq_of_eq T (IsIso.inv_hom_id _) _ _ _
    _ = _ := T.pull_id _ _ _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtGood
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pEtGood :
    EtnGood → EtGood := by
  intro hE l _ B hl
  have hn := fun n => hE l B hl n 0
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a hgal x y hxy
    refine DFinsupp.ext fun n => ?_
    have h1 := congrArg (fun v : Htot l (sch.obj W) => v n) hxy
    exact (hn n).inj p r c hc G a hgal h1
  · intro Z Y p q s _ _ hs
    choose tr htr using fun n => (hn n).tr p q s hs
    let tr' : ∀ n, HQ l (sch.obj Y) n 0 →ₗ[ℚ_[l]] HQ l (sch.obj Z) n 0 := fun n => tr n
    refine ⟨DirectSum.lmap tr', ?_⟩
    intro W r c hc J _ σ hσ hsp
    refine fun (x : Htot l (sch.obj Y)) => DFinsupp.ext fun n => ?_
    have h1 := htr n W r c hc J σ hσ hsp (x n)
    exact h1.trans (DirectSum.sum_apply Finset.univ
      (fun j => ((et l B).pull (σ j) (hσ j)) x) n).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtTr
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pEtTr :
    EtTr := by
  intro l _ B hl n i Z Y p q s _ _ W r c hc J _ σ hσ hsp x
  obtain ⟨hsc, hiso⟩ := hsp
  have hT := UpperTheory.Gal.TranscendenceTraces.adic.2.2.2.2.2.2.2.2.2
  let e := Fintype.equivFin J
  have hiso' : IsIso (Sigma.desc fun k : Fin (Fintype.card J) =>
      pullback.lift (σ (e.symm k)) (𝟙 W) (by rw [hsc, Category.id_comp])) := by
    have hEq : (Sigma.desc fun k : Fin (Fintype.card J) =>
        pullback.lift (σ (e.symm k)) (𝟙 W) (by rw [hsc, Category.id_comp])) =
        (Sigma.reindex e.symm (fun _ : J => W)).hom ≫
          Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hsc, Category.id_comp]) := by
      refine Sigma.hom_ext _ _ (fun k => ?_)
      rw [Sigma.ι_desc]
      have h4 := Sigma.ι_reindex_hom_assoc (ε := e.symm) (f := fun _ : J => W) (b := k)
        (h := Sigma.desc fun j => pullback.lift (σ j) (𝟙 W) (by rw [hsc, Category.id_comp]))
      rw [Sigma.ι_desc] at h4
      exact h4.symm
    rw [hEq]
    infer_instance
  have hlZ : IsUnit ((l : Γ(Z, ⊤))) := by
    simpa using hl.map (Scheme.Hom.appTop p).hom
  have h1 := hT l n i s hlZ W c (Fintype.card J) (fun k => σ (e.symm k)) (fun k => hsc _) hiso'
  have h2 : ∀ y : HQ l (sch.obj Y) n i, pullHQ l (sch.map c) n i
      (TranscendenceTraces.trHQ l s (TranscendenceTraces.Wt.const Y 1) n i y) = ∑ j, pullHQ l (sch.map (σ j)) n i y := by
    intro y
    have h3 := LinearMap.congr_fun h1 y
    rw [LinearMap.comp_apply, LinearMap.sum_apply] at h3
    rw [h3]
    exact Equiv.sum_comp e.symm (fun j => pullHQ l (sch.map (σ j)) n i y)
  exact h2 x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtnGood
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem push_one_eq {W Z : Scheme.{0}} (c : W ⟶ Z) (d : ℕ) (hd : d ≠ 0) (h : FEt c d) :
    (UpperTheory.Gal.TranscendenceTraces.Wt.const W 1).push c = UpperTheory.Gal.TranscendenceTraces.Wt.const Z (d : ℤ) := by
  funext Ω _ _ x
  have hx := h.2.2 Ω x
  simp only [UpperTheory.Gal.TranscendenceTraces.Wt.push, UpperTheory.Gal.TranscendenceTraces.Wt.const]
  have hne : Nat.card {y // y ≫ c = x} ≠ 0 := by rw [hx]; exact hd
  have hfin : Finite {y // y ≫ c = x} := Nat.finite_of_card_ne_zero hne
  have hs : (UpperTheory.Gal.TranscendenceTraces.fib c x).Finite := Set.finite_coe_iff.mp hfin
  rw [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_const, nsmul_eq_mul, mul_one,
    ← Set.ncard_eq_toFinset_card _ hs, ← Nat.card_coe_set_eq]
  exact_mod_cast hx

theorem UpperTheory.Gal.G3.pEtnGood :
    FEtBasic → EtTr → EtnGood := by
  intro hF hT l _ B hl n i
  obtain ⟨hW, -, hA⟩ := UpperTheory.Gal.TranscendenceTraces.all_holds
  have hFlat : UpperTheory.Gal.TranscendenceTraces.WtFlat := hW.2.2.2.2.2.2.2.2.2.1
  have hMult : UpperTheory.Gal.TranscendenceTraces.MultBasic := hW.2.2.2.2.2.2.2.1
  have hDeg : UpperTheory.Gal.TranscendenceTraces.TrDegQ := hA.2.2.2.2.1
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a hG
    have hd : FEt c (Nat.card G) := hF.2.2 c G a hG
    have hpos : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have hpush := push_one_eq c _ hpos hd
    obtain ⟨hfin, het, -⟩ := hd
    have hwt : UpperTheory.Gal.TranscendenceTraces.IsWt c (UpperTheory.Gal.TranscendenceTraces.Wt.const W 1) := by
      have h1 := hFlat c
      rwa [hMult.2.2 c] at h1
    have hlZ : IsUnit ((l : ℕ) : Γ(Z, ⊤)) := by
      have := hl.map p.appTop.hom
      simpa using this
    have key := hDeg l n i c _ _ hwt hlZ hpush
    have hne : (((Nat.card G : ℕ) : ℤ) : ℚ_[l]) ≠ 0 := by
      exact_mod_cast hpos
    intro x y hxy
    have hxy' : pullHQ l (sch.map c) n i x = pullHQ l (sch.map c) n i y := hxy
    have e : ∀ t, UpperTheory.Gal.TranscendenceTraces.trHQ l c (UpperTheory.Gal.TranscendenceTraces.Wt.const W 1) n i (pullHQ l (sch.map c) n i t) =
        (((Nat.card G : ℕ) : ℤ) : ℚ_[l]) • t := fun t => LinearMap.congr_fun key t
    have ex := e x
    rw [hxy', e y] at ex
    exact smul_right_injective _ hne ex.symm
  · intro Z Y p q s _ _ _
    exact ⟨_, hT l B hl n i p q s⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PExtGood
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pExtGood :
    (∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (L : Type) [Field L] [Algebra R L] {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p), T.IsTr p q s tr → (T.ext L).IsTr p q s (tr.baseChange L)) → ExtGood.{u} := by
  intro htr B R _ T L _ _ hG
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a hgal
    have hinj := hG.inj p r c hc G a hgal
    show Function.Injective (LinearMap.baseChange L (T.pull c hc))
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hinj
  · intro Z Y p q s _ _ hs
    obtain ⟨tr, htr'⟩ := hG.tr p q s hs
    exact ⟨tr.baseChange L, htr T L p q s tr htr'⟩
end

