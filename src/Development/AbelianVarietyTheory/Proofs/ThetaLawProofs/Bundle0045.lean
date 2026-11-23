module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TopologicalKrullDimLeOfFiniteCommonZeros
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsThetaKeyFamilyUniversalFrames
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.KeyFam

theorem GeomInt.mvPolynomial {k S : Type} [Field k] [CommRing S] [Algebra k S] (σ : Type) [Finite σ]
    (h : GeomInt k S) : GeomInt k (MvPolynomial σ S) := by
  have h₀ := h.1
  have h₁ : Algebra.Smooth S (MvPolynomial σ S) := ⟨inferInstance, inferInstance⟩
  refine ⟨Algebra.Smooth.comp k S _, fun K _ _ => ?_⟩
  have := h.2 K
  let e₁ : K ⊗[k] MvPolynomial σ S ≃ₐ[k] K ⊗[k] (S ⊗[k] MvPolynomial σ k) :=
    Algebra.TensorProduct.congr AlgEquiv.refl ((MvPolynomial.algebraTensorAlgEquiv k S).symm.restrictScalars k)
  let e₂ : (K ⊗[k] S) ⊗[k] MvPolynomial σ k ≃ₐ[k] K ⊗[k] (S ⊗[k] MvPolynomial σ k) :=
    Algebra.TensorProduct.assoc k k k K S (MvPolynomial σ k)
  let e₃ := MvPolynomial.algebraTensorAlgEquiv (σ := σ) k (K ⊗[k] S)
  exact ((e₁.trans e₂.symm).toMulEquiv.trans e₃.toMulEquiv).isDomain _

theorem exists_univ_scalars {k S : Type} [Field k] [CommRing S] [Algebra k S] (h : GeomInt k S) (s : S →+* ℂ)
    (s₀ : S →ₐ[k] k) (n : ℕ) (a : ℂˣ) (N : Matrix (Fin n) (Fin n) ℂ) (hN : IsUnit N.det) :
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra k S') (j : S →ₐ[k] S') (s' : S' →+* ℂ) (s₀' : S' →ₐ[k] k)
      (b : S'ˣ) (M : Matrix (Fin n) (Fin n) S'), GeomInt k S' ∧ s'.comp j.toRingHom = s ∧ s₀'.comp j = s₀ ∧
      IsUnit M.det ∧ s' b = a ∧ ∀ i l, s' (M i l) = N i l := by
  let T := MvPolynomial (Option (Fin n × Fin n)) S
  let M₀ : Matrix (Fin n) (Fin n) T := fun i l => MvPolynomial.X (some (i, l))
  let r : T := MvPolynomial.X none * M₀.det
  have key : ∀ {L : Type} [CommRing L] (f : S →+* L) (c : L) (B : Matrix (Fin n) (Fin n) L),
      ∃ F : T →+* L, (∀ z, F (MvPolynomial.C z) = f z) ∧ F (MvPolynomial.X none) = c ∧
        (∀ i l, F (M₀ i l) = B i l) ∧ F r = c * B.det := by
    intro L _ f c B
    let F : T →+* L := MvPolynomial.eval₂Hom f (fun o => o.elim c fun p => B p.1 p.2)
    have h₁ : F (MvPolynomial.X none) = c := MvPolynomial.eval₂Hom_X' _ _ _
    have h₂ : ∀ i l, F (M₀ i l) = B i l := fun i l => MvPolynomial.eval₂Hom_X' _ _ _
    refine ⟨F, fun z => MvPolynomial.eval₂Hom_C _ _ _, h₁, h₂, ?_⟩
    rw [map_mul, h₁, RingHom.map_det]
    congr 2
    ext i l
    exact h₂ i l
  obtain ⟨F, hF₁, hF₂, hF₃, hF₄⟩ := key s a N
  obtain ⟨G, hG₁, -, -, hG₄⟩ := key s₀.toRingHom 1 1
  have uF : IsUnit (F r) := hF₄ ▸ a.isUnit.mul hN
  have uG : IsUnit (G r) := by rw [hG₄]; simp
  have hr : r ≠ 0 := fun e => uG.ne_zero (by rw [e, map_zero])
  let S' := Localization.Away r
  have ur : IsUnit (algebraMap T S' r) := IsLocalization.Away.algebraMap_isUnit r
  rw [map_mul, IsUnit.mul_iff] at ur
  obtain ⟨⟨b, hb⟩, uM⟩ := ur
  let j : S →ₐ[k] S' := (IsScalarTower.toAlgHom k T S').comp (IsScalarTower.toAlgHom k S T)
  have hj : ∀ z, j z = algebraMap T S' (MvPolynomial.C z) := fun _ => rfl
  let g₀ : S' →+* k := IsLocalization.Away.lift r uG
  have hg : ∀ z, g₀ (j z) = s₀ z := fun z => by
    rw [hj, IsLocalization.Away.lift_eq, hG₁]; rfl
  refine ⟨S', inferInstance, inferInstance, j, IsLocalization.Away.lift r uF,
    { g₀ with commutes' := fun c => ?_ }, b, (algebraMap T S').mapMatrix M₀,
    (GlobalTheory.KeyFam.geomInt_baseChange_and_away k k T (h.mvPolynomial _)).2 r hr, RingHom.ext fun z => ?_, AlgHom.ext hg, ?_, ?_, fun i l => ?_⟩
  · change g₀ _ = _
    rw [← j.commutes, hg, s₀.commutes]
  · change IsLocalization.Away.lift r uF (j z) = _
    rw [hj, IsLocalization.Away.lift_eq, hF₁]
  · rwa [← RingHom.map_det]
  · rw [hb, IsLocalization.Away.lift_eq, hF₂]
  · change IsLocalization.Away.lift r uF (algebraMap T S' (M₀ i l)) = _
    rw [IsLocalization.Away.lift_eq, hF₃]

theorem exists_polPB_of_keyPB {R R' : Type} [CommRing R] [CommRing R'] {x' : KeyIn R'} {x : KeyIn R} {f : R →+* R'}
    (h : KeyPB x' x f) : ∃ φ, PolPB x'.P x.P (spMap f) φ := by
  obtain ⟨φ, -, w, hg, -, hp, hw, -⟩ := h
  exact ⟨φ, hp, hg, w, hw⟩

theorem exists_univ_frames : Out.Laws → ∀ (k S : Type) [Field k] [CommRing S] [Algebra k S] (y : KeyIn S) (x : KeyIn ℂ) (s : S →+* ℂ) (φ : x.P.A.left ⟶ y.P.A.left) (s₀ : S →ₐ[k] k), GeomInt k S → PolPB x.P y.P (spMap s) φ → ∃ (S' : Type) (_ : CommRing S') (_ : Algebra k S') (j : S →ₐ[k] S') (y' : KeyIn S') (s' : S' →+* ℂ) (s₀' : S' →ₐ[k] k) (ψ : y'.P.A.left ⟶ y.P.A.left), GeomInt k S' ∧ KeyPB x y' s' ∧ PolPB y'.P y.P (spMap j.toRingHom) ψ ∧ s₀'.comp j = s₀ := by
  intro hL k S _ _ _ y x s φ s₀ hS hφ
  obtain ⟨Q, hg, rig', hr', th', hth', v', hv'⟩ := x
  dsimp only at φ hφ
  obtain ⟨rig, hr, th, hth, v, hv, H⟩ := KeyTf.exists_keyPB_on S ℂ s y Q φ hg hφ.2.1 hφ.1 hφ.2.2
  obtain ⟨a, t, ht, hat, Hid⟩ := (KeyOnPol.main hL ℂ).2 ⟨Q, hg, rig, hr, th, hth, v, hv⟩ rig' hr' th' hth' v' hv'
  choose N hN using fun i => (hv.2 _ (hv'.1 i)).exists
  have := Q.isAb.comm
  have uN : IsUnit (Matrix.det (N : Matrix _ _ ℂ)) :=
    ((LieComb.lieComb_algebra ℂ Q.A Q.g v hv.1).2.2.2.2 N v' hv hN).1 hv'
  obtain ⟨S', _, _, j, s', s₀', b, M, hS', hs, hs₀, uM, hb, hM⟩ := exists_univ_scalars hS s s₀ Q.g a N uN
  obtain ⟨y₁, H₁⟩ := exists_keyPB_ring y j.toRingHom
  have H₂ := KeyCancel.keyPB_cancel _ _ _ y y₁ _ _ s' H₁ (hs ▸ H)
  obtain ⟨ψ, hψ⟩ := exists_polPB_of_keyPB H₁
  have e : Q.g = y₁.P.g := KeyGalDesc.g_eq H₂
  have := y₁.P.isAb.comm
  let M' : Matrix (Fin y₁.P.g) (Fin y₁.P.g) S' := Matrix.reindex (finCongr e) (finCongr e) M
  have uM' : IsUnit M'.det := by rwa [Matrix.det_reindex_self]
  obtain ⟨ex, -, -, -, bas⟩ := LieComb.lieComb_algebra S' y₁.P.A y₁.P.g y₁.v y₁.basis.1
  choose v₁ hv₁ using fun i => (ex (M' i)).exists
  obtain ⟨t₁, ht₁, -, hle⟩ := exists_sec_div y₁.P.A.hom b.inv_mul y₁.th
  refine ⟨S', _, _, j, ⟨y₁.P, y₁.g_pos, y₁.rig, y₁.rig_gen, t₁,
    fun p => (y₁.th_ne p).imp fun z hz => ⟨hz.1, hle hz.2⟩, v₁, (bas M' v₁ y₁.basis hv₁).2 uM'⟩, s', s₀', ψ, hS', ?_, hψ, hs₀⟩
  rw [← RingHom.id_comp s']
  refine keyPB_trans _ _ _ _ _ _ _ _ ?_ Hid
  refine KeyPBScale.keyPB_scale S' ℂ s' y₁.P y₁.g_pos y₁.rig y₁.rig_gen y₁.th y₁.th_ne y₁.v y₁.basis t₁ _ v₁ _ b M' Q e
    hg rig hr th hth v hv t ht v' hv' ht₁ hv₁ (hb ▸ hat) (fun i => ?_) H₂
  convert hN i using 2 with l
  exact hM i l

end GlobalTheory.KeyFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GeomIntegralOfEtaleFaithfullyFlatCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem exists_point_over_of_idempotent {F A B : Type} [Field F] [IsAlgClosed F] [CommRing A]
    [CommRing B] [Algebra F A] [Algebra F B] [IsNoetherianRing A] (f : A →ₐ[F] B)
    (hfin : f.toRingHom.Finite) (hflat : f.toRingHom.Flat) (P : B →ₐ[F] F) (Q : A →ₐ[F] F)
    (h : ∀ e : A, IsIdempotentElem e → P (f e) = Q e) (E : B) (hE : IsIdempotentElem E)
    (hP : P E = 1) : ∃ Q' : B →ₐ[F] F, Q' E = 1 ∧ ∀ a, Q' (f a) = Q a := by
  algebraize [f.toRingHom]
  haveI : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have hcl : IsClopen (PrimeSpectrum.basicOpen E : Set (PrimeSpectrum B)) :=
    PrimeSpectrum.isClopen_iff.2 ⟨E, hE, rfl⟩
  have him : IsClopen (PrimeSpectrum.comap (algebraMap A B) ''
      (PrimeSpectrum.basicOpen E : Set (PrimeSpectrum B))) :=
    ⟨PrimeSpectrum.isClosedMap_comap_of_isIntegral _ (Algebra.IsIntegral.isIntegral) _ hcl.1,
      PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation _ hcl.2⟩
  obtain ⟨ε, hε, hεe⟩ := PrimeSpectrum.isClopen_iff.1 him
  have h1 : PrimeSpectrum.comap (algebraMap A B) ⟨RingHom.ker P, RingHom.ker_isPrime P⟩ ∈
      (PrimeSpectrum.basicOpen ε : Set (PrimeSpectrum A)) := by
    rw [← hεe]
    refine ⟨_, ?_, rfl⟩
    change ¬ (P E = 0)
    rw [hP]; exact one_ne_zero
  have h2 : (⟨RingHom.ker Q, RingHom.ker_isPrime Q⟩ : PrimeSpectrum A) ∈
      (PrimeSpectrum.basicOpen ε : Set (PrimeSpectrum A)) := by
    change ¬ (Q ε = 0)
    rw [← h ε hε]
    exact h1
  rw [← hεe] at h2
  obtain ⟨𝔮, h𝔮E, h𝔮⟩ := h2
  have hker : ∀ a : A, Q a = 0 → f a ∈ 𝔮.asIdeal := by
    intro a ha
    have : a ∈ (PrimeSpectrum.comap (algebraMap A B) 𝔮).asIdeal := by
      rw [h𝔮]; exact ha
    exact this
  have hcomp : ∀ a : A, Ideal.Quotient.mk 𝔮.asIdeal (f a) =
      algebraMap F (B ⧸ 𝔮.asIdeal) (Q a) := by
    intro a
    have := hker (a - algebraMap F A (Q a)) (by simp)
    rw [map_sub, AlgHom.commutes] at this
    exact Ideal.Quotient.eq.2 this
  have hint : (algebraMap F (B ⧸ 𝔮.asIdeal)).IsIntegral := by
    apply RingHom.IsIntegral.tower_top Q.toRingHom
    have : (algebraMap F (B ⧸ 𝔮.asIdeal)).comp Q.toRingHom =
        (Ideal.Quotient.mk 𝔮.asIdeal).comp f.toRingHom := by
      ext a; exact (hcomp a).symm
    rw [this]
    exact RingHom.IsIntegral.trans _ _ hfin.to_isIntegral
      (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)
  haveI : Algebra.IsIntegral F (B ⧸ 𝔮.asIdeal) := ⟨hint⟩
  have hbij : Function.Bijective (Algebra.ofId F (B ⧸ 𝔮.asIdeal)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let φ := (AlgEquiv.ofBijective _ hbij).symm
  refine ⟨φ.toAlgHom.comp (Ideal.Quotient.mkₐ F 𝔮.asIdeal), ?_, fun a => ?_⟩
  · rcases IsIdempotentElem.iff_eq_zero_or_one.1
      (hE.map (φ.toAlgHom.comp (Ideal.Quotient.mkₐ F 𝔮.asIdeal))) with h0 | h0
    · exfalso
      apply h𝔮E
      have : Ideal.Quotient.mk 𝔮.asIdeal E = 0 := φ.injective (by rw [map_zero]; exact h0)
      exact Ideal.Quotient.eq_zero_iff_mem.1 this
    · exact h0
  · change φ (Ideal.Quotient.mk 𝔮.asIdeal (f a)) = _
    rw [hcomp, AlgEquiv.commutes]; rfl

theorem exists_algHom_baseChange_away {k₀ k B L : Type} [Field k₀] [Field k] [Algebra k₀ k]
    [CommRing B] [Algebra k₀ B] [CommRing L] [Algebra k₀ L] [Algebra k L] [IsScalarTower k₀ k L]
    (e : B) (G : B →ₐ[k₀] L) (hG : G e = 1) :
    ∃ s : k ⊗[k₀] Localization.Away e →ₐ[k] L,
      ∀ b, s (1 ⊗ₜ algebraMap B (Localization.Away e) b) = G b := by
  have hu : ∀ y : Submonoid.powers e, IsUnit (G y) := by
    rintro ⟨_, n, rfl⟩
    simp [hG]
  refine ⟨Algebra.TensorProduct.lift (Algebra.ofId k L)
    (IsLocalization.liftAlgHom (S := Localization.Away e) hu) (fun _ _ => Commute.all _ _),
    fun b => ?_⟩
  simp

theorem exists_finset_integral_of_finiteType {K T L : Type} [Field K] [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] [CommRing L] [Algebra K L] (g : T →ₐ[K] L)
    (hg : ∀ x, IsIntegral K (g x)) :
    ∃ s : Set L, s.Finite ∧ (∀ y ∈ s, IsIntegral K y) ∧
      ∀ U : Subalgebra K L, s ⊆ U → ∀ x, g x ∈ U := by
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := K) (A := T)
  refine ⟨g '' t, t.finite_toSet.image _, ?_, fun U hU x => ?_⟩
  · rintro _ ⟨x, -, rfl⟩; exact hg x
  · have : Algebra.adjoin K (t : Set T) ≤ U.comap g :=
      Algebra.adjoin_le fun y hy => hU ⟨y, hy, rfl⟩
    rw [ht] at this
    exact this Algebra.mem_top

theorem finite_flat_tensor_map (K F R R₁ : Type) [CommRing K] [CommRing F] [Algebra K F]
    [CommRing R] [Algebra K R] [CommRing R₁] [Algebra R R₁] [Algebra K R₁] [IsScalarTower K R R₁]
    [Module.Finite R R₁] [Module.Flat R R₁] :
    (Algebra.TensorProduct.map (AlgHom.id F F) (IsScalarTower.toAlgHom K R R₁)).toRingHom.Finite ∧
    (Algebra.TensorProduct.map (AlgHom.id F F) (IsScalarTower.toAlgHom K R R₁)).toRingHom.Flat := by
  constructor
  · exact RingHom.Finite.tensorProductMap (f := AlgHom.id K F) (RingHom.Finite.id F)
      (g := IsScalarTower.toAlgHom K R R₁) (RingHom.finite_algebraMap.2 inferInstance)
  · exact RingHom.Flat.tensorProductMap (f := AlgHom.id F F)
      (g := IsScalarTower.toAlgHom K R R₁) (RingHom.Flat.id F)
      (RingHom.flat_algebraMap_iff.2 inferInstance)

theorem exists_geomInt_piece_of_finite_etale : ∀ (K : Type) [Field K] [NumberField K] [Algebra K ℂ] (R R₁ : Type) [CommRing R] [Algebra K R] [Algebra.Smooth K R] [CommRing R₁] [Algebra R R₁] [Algebra K R₁] [IsScalarTower K R R₁] (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (σ₁ : K₁ →ₐ[K] ℂ) (p : R₁ →ₐ[K] ℂ) (q : R →ₐ[K] K₁), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) → (∀ e : ℂ ⊗[K] R, IsIdempotentElem e → Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (p.comp (IsScalarTower.toAlgHom K R R₁)) (fun _ _ => Commute.all _ _) e = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (σ₁.comp q) (fun _ _ => Commute.all _ _) e) → ∃ (k : Type) (_ : Field k) (_ : NumberField k) (S : Type) (_ : CommRing S) (_ : Algebra k S) (j : R₁ →+* S) (s : S →+* ℂ) (s₀ : S →ₐ[k] k) (ii : K₁ →+* k), GeomInt k S ∧ s.comp j = p.toRingHom ∧ (s₀.toRingHom.comp j).comp (algebraMap R R₁) = ii.comp q.toRingHom := by
  intro K _ _ _ R R₁ _ _ _ _ _ _ _ K₁ _ _ _ σ₁ p q ⟨hfin, het, hff⟩ hidem
  haveI : Algebra.Smooth K R₁ := Algebra.Smooth.comp K R R₁
  obtain ⟨k₀, e, hk₀, he, hpe, hgi⟩ := _root_.GlobalTheory.GeomComp.exists_geomInt_component K R₁ p
  haveI : IsNoetherianRing (ℂ ⊗[K] R) := Algebra.FiniteType.isNoetherianRing ℂ _
  let f : ℂ ⊗[K] R →ₐ[ℂ] ℂ ⊗[K] R₁ :=
    Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (IsScalarTower.toAlgHom K R R₁)
  obtain ⟨hf1, hf2⟩ : f.toRingHom.Finite ∧ f.toRingHom.Flat := finite_flat_tensor_map K ℂ R R₁
  let emb : k₀ ⊗[K] R₁ →ₐ[K] ℂ ⊗[K] R₁ := Algebra.TensorProduct.map k₀.val (AlgHom.id K R₁)
  let P : ℂ ⊗[K] R₁ →ₐ[ℂ] ℂ :=
    Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) p (fun _ _ => Commute.all _ _)
  have hPemb : ∀ x, P (emb x) = Algebra.TensorProduct.lift k₀.val p (fun _ _ => Commute.all _ _) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [P, emb]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hPf : ∀ x, P (f x) = Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ)
      (p.comp (IsScalarTower.toAlgHom K R R₁)) (fun _ _ => Commute.all _ _) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [P, f]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  obtain ⟨Q', hQE, hQ⟩ := exists_point_over_of_idempotent f hf1 hf2 P
    (Algebra.TensorProduct.lift (AlgHom.id ℂ ℂ) (σ₁.comp q) (fun _ _ => Commute.all _ _))
    (fun x hx => (hPf x).trans (hidem x hx)) (emb e) (he.map emb) ((hPemb e).trans hpe)
  let q' : R₁ →ₐ[K] ℂ := (Q'.restrictScalars K).comp Algebra.TensorProduct.includeRight
  have hq' : ∀ r, q' (algebraMap R R₁ r) = σ₁ (q r) := by
    intro r
    have := hQ (1 ⊗ₜ r)
    simpa [f, q'] using this
  have hq'int : ∀ x, IsIntegral K (q' x) := by
    intro x
    letI : Algebra K₁ ℂ := σ₁.toRingHom.toAlgebra
    haveI : IsScalarTower K K₁ ℂ := IsScalarTower.of_algebraMap_eq fun a => (σ₁.commutes a).symm
    have h1 : IsIntegral K₁ (q' x) :=
      (Algebra.IsIntegral.isIntegral (R := R) x).map_of_comp_eq q.toRingHom q'.toRingHom
        (RingHom.ext fun r => (hq' r).symm)
    exact isIntegral_trans _ h1
  obtain ⟨s₁, hs₁, hs₁i, hs₁U⟩ := exists_finset_integral_of_finiteType q' hq'int
  obtain ⟨s₂, hs₂, hs₂i, hs₂U⟩ := exists_finset_integral_of_finiteType σ₁
    (fun x => (Algebra.IsIntegral.isIntegral (R := K) x).map σ₁)
  let k : IntermediateField k₀ ℂ := IntermediateField.adjoin k₀ (s₁ ∪ s₂)
  haveI : Finite ↥(s₁ ∪ s₂) := (hs₁.union hs₂).to_subtype
  haveI : FiniteDimensional k₀ k := IntermediateField.finiteDimensional_adjoin (by
    rintro x (hx | hx)
    · exact (hs₁i x hx).tower_top
    · exact (hs₂i x hx).tower_top)
  haveI : NumberField k₀ := NumberField.of_module_finite K k₀
  haveI : NumberField k := NumberField.of_module_finite k₀ k
  have hm₁ : ∀ x, q' x ∈ k := hs₁U (k.toSubalgebra.restrictScalars K)
    (fun y hy => IntermediateField.subset_adjoin k₀ (s₁ ∪ s₂) (Or.inl hy))
  have hm₂ : ∀ x, σ₁ x ∈ k := hs₂U (k.toSubalgebra.restrictScalars K)
    (fun y hy => IntermediateField.subset_adjoin k₀ (s₁ ∪ s₂) (Or.inr hy))
  let qk : R₁ →ₐ[K] k :=
    { toRingHom := q'.toRingHom.codRestrict k hm₁
      commutes' := fun a => Subtype.ext (q'.commutes a) }
  let G : k₀ ⊗[K] R₁ →ₐ[k₀] ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId k₀ ℂ) p (fun _ _ => Commute.all _ _)
  let G₀ : k₀ ⊗[K] R₁ →ₐ[k₀] k :=
    Algebra.TensorProduct.lift (Algebra.ofId k₀ k) qk (fun _ _ => Commute.all _ _)
  have hG : ∀ x, G x = Algebra.TensorProduct.lift k₀.val p (fun _ _ => Commute.all _ _) x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hG₀ : ∀ x, (G₀ x : ℂ) = Q' (emb x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have : emb (a ⊗ₜ b) = (a : ℂ) • ((1 : ℂ) ⊗ₜ[K] b) := by
        simp [emb, TensorProduct.smul_tmul']
      rw [this, map_smul, smul_eq_mul]
      rfl
    | add a b ha hb => simp only [map_add (f := _), ← ha, ← hb]; rfl
  obtain ⟨s, hs⟩ := exists_algHom_baseChange_away (k := k) e G ((hG e).trans hpe)
  obtain ⟨s₀, hs₀⟩ := exists_algHom_baseChange_away (k := k) e G₀
    (Subtype.ext ((hG₀ e).trans hQE))
  refine ⟨k, inferInstance, inferInstance, k ⊗[k₀] Localization.Away e, inferInstance,
    inferInstance,
    (Algebra.TensorProduct.includeRight (R := k₀) (A := k)).toRingHom.comp
      ((algebraMap (k₀ ⊗[K] R₁) (Localization.Away e)).comp
        (Algebra.TensorProduct.includeRight (R := K) (A := k₀)).toRingHom),
    s.toRingHom, s₀, σ₁.toRingHom.codRestrict k hm₂, (geomInt_baseChange_and_away k₀ k _ hgi).1, ?_, ?_⟩
  · ext x
    refine (hs (1 ⊗ₜ x)).trans ?_
    simp [G]
  · refine RingHom.ext fun x => ?_
    refine (hs₀ (1 ⊗ₜ algebraMap R R₁ x)).trans (Subtype.ext ?_)
    rw [hG₀]
    exact Eq.trans (by simp [emb, q']) (hq' x)

end GlobalTheory.KeyFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RingKrullDimLocalizationQuotientLe
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem ringKrullDim_localization_quotient_le {R : Type} [CommRing R] {k : ℕ} (f : Fin k → R) (m : Ideal R)
    [m.IsPrime] :
    ringKrullDim (Localization.AtPrime m ⧸
        Ideal.span (Set.range fun j => algebraMap R (Localization.AtPrime m) (f j))) ≤
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Set.range f) : Set (PrimeSpectrum R)) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have h₁ := (PrimeSpectrum.localization_comap_isInducing (R := R) (Localization.AtPrime m) m.primeCompl).comp
    (PrimeSpectrum.isEmbedding_comap_of_surjective _ (Ideal.Quotient.mk
      (Ideal.span (Set.range fun j => algebraMap R (Localization.AtPrime m) (f j))))
      Ideal.Quotient.mk_surjective).isInducing
  refine (h₁.codRestrict (s := PrimeSpectrum.zeroLocus (Set.range f)) fun p => ?_).topologicalKrullDim_le
  rintro _ ⟨j, rfl⟩
  change Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime m) (f j)) ∈ p.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self (f := fun j => algebraMap R (Localization.AtPrime m) (f j)) j))]
  exact p.asIdeal.zero_mem

theorem ofList_take_ofFn {R : Type} [CommRing R] {g : ℕ} (f : Fin g → R) (i : ℕ) :
    Ideal.ofList ((List.ofFn f).take i) = Ideal.span (f '' {j | j.val < i}) := by
  unfold Ideal.ofList
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, List.mem_take_iff_getElem, List.length_ofFn, List.getElem_ofFn, Set.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, by omega⟩, by simp only; omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by have := j.2; omega, rfl⟩

theorem isWeaklyRegular_of_dim_zeroLocus {R : Type} [CommRing R] {g : ℕ} (f : Fin g → R)
    (hreg : ∀ (m : Ideal R) [m.IsMaximal],
      IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = g)
    (hdim : ∀ (k : ℕ) (hk : k ≤ g),
      (PrimeSpectrum.zeroLocus (Set.range fun j => f (Fin.castLE hk j)) : Set (PrimeSpectrum R)).Nonempty →
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Set.range fun j => f (Fin.castLE hk j)) :
        Set (PrimeSpectrum R)) ≤ ((g - k : ℕ) : WithBot ℕ∞)) :
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f) := by
  refine ⟨fun i hi => ?_⟩
  have hi' : i < g := by simpa using hi
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem, ofList_take_ofFn, List.getElem_ofFn]
  simp only [smul_eq_mul, Ideal.mul_top]
  intro a ha
  refine Ideal.mem_of_localization_maximal fun m hm => ?_
  have ha' := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime m)) ha
  rw [map_mul] at ha'
  by_cases hall : ∀ j : Fin g, j.val ≤ i → f j ∈ m
  · obtain ⟨h₁, h₂⟩ := hreg m
    have hk : i + 1 ≤ g := hi'
    have hd := (ringKrullDim_localization_quotient_le (fun j => f (Fin.castLE hk j)) m).trans
      (hdim (i + 1) hk ⟨⟨m, hm.isPrime⟩, by
        rintro _ ⟨j, rfl⟩
        exact hall _ (by have := j.2; simp only [Fin.val_castLE]; omega)⟩)
    have hr := GlobalTheory.isRegular_ofFn_of_ringKrullDim_quotient_add_le (Localization.AtPrime m) g (i + 1)
      (fun j => algebraMap R (Localization.AtPrime m) (f (Fin.castLE hk j))) h₂
      (fun j => (IsLocalization.AtPrime.to_map_mem_maximal_iff _ m _).2
        (hall _ (by have := j.2; simp only [Fin.val_castLE]; omega)))
      ((add_le_add_left hd _).trans (by
        rw [← Nat.cast_add, Nat.sub_add_cancel hk]))
    have h₃ := hr.toIsWeaklyRegular.regular_mod_prev i (by simp)
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem, ofList_take_ofFn, List.getElem_ofFn] at h₃
    simp only [smul_eq_mul, Ideal.mul_top] at h₃
    have e : Ideal.map (algebraMap R (Localization.AtPrime m)) (Ideal.span (f '' {j | j.val < i})) =
        Ideal.span ((fun j : Fin (i + 1) => algebraMap R (Localization.AtPrime m) (f (Fin.castLE hk j))) ''
          {j | j.val < i}) := by
      rw [Ideal.map_span]
      congr 1
      ext b
      constructor
      · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact ⟨⟨j, Nat.lt_succ_of_lt hj⟩, hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨_, ⟨Fin.castLE hk j, hj, rfl⟩, rfl⟩
    rw [e] at ha' ⊢
    exact h₃ _ ha'
  · push Not at hall
    obtain ⟨j, hj, hjm⟩ := hall
    have hu : IsUnit (algebraMap R (Localization.AtPrime m) (f j)) :=
      IsLocalization.map_units _ (⟨f j, hjm⟩ : m.primeCompl)
    rcases hj.eq_or_lt with hj | hj
    · subst hj
      exact (Ideal.unit_mul_mem_iff_mem _ hu).1 ha'
    · rw [Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_image_of_mem f (show j ∈ {j : Fin g | j.val < i} from hj)))) hu]
      trivial

theorem isWeaklyRegular_of_finZ : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n : ℕ) (s : Fin x.P.g → RR x n) (V : x.P.A.left.Opens) (c : x.P.L.ι) (h : V ≤ x.P.L.U c), 1 ≤ n → FinZ x s → IsAffineOpen V → RingTheory.Sequence.IsWeaklyRegular Γ(x.P.A.left, V) (List.ofFn fun i => resG x.P.A.left h ((s i).f c)) := by
  intro hL K _ _ x n s V c h hn hZ hV
  refine isWeaklyRegular_of_dim_zeroLocus _ (fun m _ => ?_) fun k hk hne => ?_
  · exact GlobalTheory.isRegularLocalRing_and_ringKrullDim_eq_of_polAV K x.P Γ(x.P.A.left, V) hV.fromSpec m _ inferInstance
  · let W : Set x.P.A.left := {y | ∀ j : Fin k, y ∉ Out.nonzeroLocus (s (Fin.castLE hk j))}
    have hW : IsClosed W := by
      have : W = ⋂ j : Fin k, (Out.nonzeroLocus (s (Fin.castLE hk j)) : Set x.P.A.left)ᶜ := by
        ext y; simp [W]
      rw [this]
      exact isClosed_iInter fun j => (Out.nonzeroLocus _).isOpen.isClosed_compl
    have hmem : ∀ p : (PrimeSpectrum.zeroLocus (Set.range fun j => resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) :
        Set (PrimeSpectrum Γ(x.P.A.left, V))), hV.fromSpec p.1 ∈ W := by
      intro p j hj
      have hpV : hV.fromSpec p.1 ∈ V := by
        have : hV.fromSpec p.1 ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
        rwa [hV.range_fromSpec] at this
      have h₁ := (GlobalTheory.AmpleSpan.isUnit_gs_iff (𝟙 _) _ _ (h hpV) _).1
        ((GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (s (Fin.castLE hk j)) (𝟙 _) (hV.fromSpec p.1) (k := c) (h hpV)).1 hj)
      have h₂ : hV.fromSpec p.1 ∈ x.P.A.left.basicOpen (resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) := by
        have := x.P.A.left.basicOpen_res (show Γ(x.P.A.left, x.P.L.U c) from (s (Fin.castLE hk j)).f c) (homOfLE h).op
        exact this.ge ⟨hpV, h₁⟩
      have h₃ : p.1 ∈ hV.fromSpec ⁻¹ᵁ x.P.A.left.basicOpen (resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) := h₂
      rw [hV.fromSpec_preimage_basicOpen] at h₃
      exact h₃ (p.2 ⟨j, rfl⟩)
    have hind : Topology.IsInducing fun p : (PrimeSpectrum.zeroLocus
        (Set.range fun j => resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) :
        Set (PrimeSpectrum Γ(x.P.A.left, V))) => hV.fromSpec p.1 :=
      hV.fromSpec.isOpenEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
    refine (hind.codRestrict hmem).topologicalKrullDim_le.trans ?_
    obtain ⟨p, hp⟩ := hne
    refine _root_.GlobalTheory.KeyKa.topologicalKrullDim_le_of_finite_zeros hL K x n (x.P.g - k) (fun j => s ⟨k + j, by have := j.2; omega⟩) W hn hW
      ⟨_, hmem ⟨p, hp⟩⟩ (Set.Finite.subset hZ ?_)
    rintro y ⟨hy₁, hy₂⟩ i
    by_cases hi : i.val < k
    · exact hy₁ ⟨i, hi⟩
    · have := hy₂ ⟨i - k, by have := i.2; omega⟩
      simp only [show k + (i.val - k) = i.val by omega] at this
      exact this

end GlobalTheory.KeyKa
end

