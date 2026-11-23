module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3079
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2974
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2910
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3082
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongModOfSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1985
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3080
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystal
section
namespace GlobalTheory

theorem abelianDualCrystal : GlobalTheory.Published.AbelianDualCrystal :=
  GlobalTheory.abelianDualCrystal_of_dualAbelianScheme GlobalTheory.dualAbelianScheme

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
section
namespace GlobalTheory

theorem abelianDeRham : GlobalTheory.Published.AbelianDeRham :=
  GlobalTheory.abelianDeRham_of_hodge_dual_poincare _root_.GlobalTheory.AbCoh.abelianHodgeDeRham _root_.GlobalTheory.dualAbelianScheme
    (GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge _root_.GlobalTheory.AbCoh.abelianHodgeDeRham _root_.GlobalTheory.dualAbelianScheme)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomLiftingNilpotentDividedPowers
section
namespace GlobalTheory

theorem abelianScheme_hom_lifting_nilpotent_dividedPowers : GlobalTheory.Published.AbelianLifting :=
  GlobalTheory.LiftFour.abelianLifting_of_four _root_.GlobalTheory.AbCoh.abelianHodgeDeRham _root_.GlobalTheory.dualAbelianScheme
    (GlobalTheory.PoincareDeRhamDualityProof.poincareDeRhamDuality_of_hodge _root_.GlobalTheory.AbCoh.abelianHodgeDeRham _root_.GlobalTheory.dualAbelianScheme)
    GlobalTheory.UnobTop.abelianUnobstructed

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsDualPair
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem exists_dualPair : ∀ (K : Type) [Field K] (A : AbVar K),
    ∃ (B : AbVar K) (P : LB (A.X ⊗ B.X).left), IsDualPair A B P ∧ B.dim = A.dim := by
  intro K _ A
  obtain ⟨B, hg, P, hB, hdim, h1, h2⟩ := GlobalTheory.dualAbelianScheme (Sp K) A.X A.ab
  exact ⟨{ X := B, grp := hg, ab := hB, dim := A.dim, smooth := hdim A.dim A.smooth }, P, ⟨h1, h2⟩, rfl⟩

end GlobalTheory.AV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyAbelianVarietyCharP
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRhamCharpolyP

theorem charpoly_of_red {R K M V : Type} [CommRing R] [Field K] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [AddCommGroup V] [Module K V]
    (π : R →+* K) (hπ : Function.Surjective π) (c : ℕ) (hc : (c : K) = 0)
    (red : M →ₛₗ[π] V) (hs : Function.Surjective red) (hk : ∀ m, red m = 0 ↔ ∃ n, m = c • n)
    (φ : Module.End R M) (ψ : Module.End K V) (h : ∀ m, red (φ m) = ψ (red m)) :
    ∃ _ : Module.Finite K V, ψ.charpoly = φ.charpoly.map π := by
  classical
  let b := Module.Free.chooseBasis R M
  let v : Module.Free.ChooseBasisIndex R M → V := fun i => red (b i)
  have hred : ∀ m, red m = ∑ i, π (b.repr m i) • v i := fun m => by
    conv_lhs => rw [← b.sum_repr m]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smulₛₗ red _ _
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    let a : Module.Free.ChooseBasisIndex R M → R := fun j => Function.surjInv hπ (g j)
    have ha : ∀ j, π (a j) = g j := fun j => Function.surjInv_eq hπ (g j)
    have h0 : red (∑ j, a j • b j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp_rw [map_smulₛₗ, ha]
      exact hg
    obtain ⟨n, hn⟩ := (hk _).1 h0
    have hai : a i = (c : R) * b.repr n i := by
      have := congrArg (fun m => b.repr m i) hn
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
          Module.Basis.repr_self, smul_eq_mul, map_nsmul] at this
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj])
        (fun hi => absurd (Finset.mem_univ i) hi)] at this
      simpa [nsmul_eq_mul] using this
    rw [← ha i, hai, map_mul, map_natCast, hc, zero_mul]
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    intro x _
    obtain ⟨m, rfl⟩ := hs x
    rw [hred m]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let bV : Module.Basis (Module.Free.ChooseBasisIndex R M) K V := Module.Basis.mk hli hsp
  have hbV : ∀ i, bV i = red (b i) := fun i => Module.Basis.mk_apply hli hsp i
  have : Module.Finite K V := Module.Finite.of_basis bV
  refine ⟨this, ?_⟩
  have hmat : LinearMap.toMatrix bV bV ψ = (LinearMap.toMatrix b b φ).map π := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, hbV j, ← h, hred]
    have hv : ∀ i', v i' = bV i' := fun i' => (hbV i').symm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hv, map_sum, map_smul, Module.Basis.repr_self, Finsupp.finsetSum_apply,
        Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, mul_ite, _root_.mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← LinearMap.charpoly_toMatrix ψ bV, hmat, Matrix.charpoly_map, LinearMap.charpoly_toMatrix]

theorem charpoly_dualMap {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module.Finite K (Module.Dual K V)] (f : Module.End K V) : (f.dualMap).charpoly = f.charpoly := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis K V),
    ← LinearMap.charpoly_toMatrix f.dualMap (Module.finBasis K V).dualBasis, ← Matrix.charpoly_transpose,
    LinearMap.dualMap_def, LinearMap.toMatrix_transpose, Matrix.transpose_transpose]

end GlobalTheory.DeRhamCharpolyP

namespace GlobalTheory.DeRhamCharpolyP


open GlobalTheory.AV GlobalTheory.PDivGroup in
theorem charpoly_push : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B) [Module.Finite k (HdR B.X)],
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) =
      (GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom k) := by
  intro p _ k _ _ _ B f _
  obtain ⟨G, -, ⟨t⟩⟩ := GlobalTheory.AVTower.exists_tower p k B
  let T := GlobalTheory.Dieu.theory p
  have : Module.Free (WittVector p k) (T.M G) := T.base.free G trivial
  have : Module.Finite (WittVector p k) (T.M G) := T.base.finite G trivial
  have h1 := GlobalTheory.Dieu.CharpolyAV.charpoly_map_eq p T k B G t (End.of f)
  have hπ : Function.Surjective (WittVector.constantCoeff : WittVector p k →+* k) := fun x =>
    ⟨WittVector.teichmuller p x, by simp⟩
  obtain ⟨hfin, h2⟩ := charpoly_of_red (WittVector.constantCoeff : WittVector p k →+* k) hπ p
    (CharP.cast_eq_zero k p) (T.red G) (T.base.red_surjective G trivial) (T.base.red_eq_zero G trivial)
    (T.map (t.map t f.hom)) (rigExtMap (t.map t f.hom)) (fun m => by
      have := T.base.red_smap trivial trivial (SemiHom.ofHom (t.map t f.hom)) m
      rw [SemiHom.ofHom_rig] at this
      exact this)
  have : Module.Finite k G.RigExt := hfin
  obtain ⟨e, he, -, -⟩ := GlobalTheory.deRhamVectorExtension p
  have hR : IsNilpotent (p : k) := by rw [CharP.cast_eq_zero]; exact IsNilpotent.zero
  let E : primDR B.X ≃ₗ[k] G.RigExt := e hR B.ab t
  have : Module.Finite k (primDR B.X) := Module.Finite.equiv E.symm
  have hconj : primPull (dp0 k) (𝟙 _) f.hom = E.symm.conj (rigExtMap (t.map t f.hom)) := by
    refine LinearMap.ext fun c => ?_
    exact E.eq_symm_apply.mpr (he.primPull hR B.ab B.ab t t f.hom c)
  have h3 : (primPull (dp0 k) (𝟙 _) f.hom).charpoly = (rigExtMap (t.map t f.hom)).charpoly := by
    exact (congrArg LinearMap.charpoly hconj).trans (E.symm.charpoly_conj _)
  calc LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom)
      = ((primPull (dp0 k) (𝟙 _) f.hom).dualMap).charpoly := rfl
    _ = (primPull (dp0 k) (𝟙 _) f.hom).charpoly := charpoly_dualMap _
    _ = (rigExtMap (t.map t f.hom)).charpoly := h3
    _ = ((GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom (WittVector p k))).map WittVector.constantCoeff :=
      h2.trans (congrArg (Polynomial.map WittVector.constantCoeff) h1)
    _ = (GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom k) := by
        rw [Polynomial.map_map]; congr 1; exact RingHom.ext_int _ _

end GlobalTheory.DeRhamCharpolyP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTorsionPointPolarisedFibreImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.ConjFib

theorem isGrpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

end GlobalTheory.Poinc.Sep.ConjFib


open GlobalTheory.Poinc.Sep.ConjFib in
theorem GlobalTheory.Poinc.Sep.conj_fibre_iso : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (o' : Type) [CommRing o'] (ζ' : o') (g' n' : ℕ) (F' : SFam g' n' ζ') (lam : Sp V ⟶ F'.X) (β : Q.B.left ⟶ F'.univ.A.left) (β₂ : (G2 Q.B).left ⟶ (G2 F'.univ.A).left), 1 ≤ n' → DefOver k₀ (spMap (ev.comp ρ) ≫ lam ≫ F'.s) → IsGrpPullback Q.B F'.univ.A lam β → IsSquare β β₂ → LBIso (abelian₂ Q.B Q.M.L) (F'.univ.P.pull β₂) → ∀ (φ₀₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 F'.univ.A).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ)) ≫ β) φ₀₂ → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∀ (a : Q.X) (p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left → p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = 𝟙 _ → ∃ (x' : Sp K ⟶ F'.X) (φ : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ F'.univ.A.left) (φ₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 F'.univ.A).left), x' ≫ F'.s = spMap (ev.comp ρ) ≫ lam ≫ F'.s ∧ IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) F'.univ.A x' φ ∧ IsSquare φ φ₂ ∧ LBIso (F'.univ.P.pull φ₀₂) (F'.univ.P.pull φ₂) ∧ spMap σ.toRingHom ≫ p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) ≫ β = p ≫ φ := by
  intro g l hl hlo W hW
  obtain ⟨j₀, hj₀⟩ := _root_.GlobalTheory.Poinc.Sep.conj_fibre_core g l hl hlo W hW
  refine ⟨j₀, ?_⟩
  intro j hj V V₁ _ _ _ _ _ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K _ _ ev k₀ hk₀ hu o' _ ζ' g' n' F' lam β β₂ hn' hdef hpb hsq hLB φ₀₂ hsq0 σ hσ a p hpf hps
  obtain ⟨f, f₂, hf, hfs, hfL, hfp⟩ :=
    hj₀ j hj V V₁ hCN hlu Q hQg ρ hρ D e hSh C u mo hmo hTh K ev k₀ hk₀ hu σ hσ a p hpf hps
  obtain ⟨hpbσ, φσ₂, hsqσ⟩ := GlobalTheory.T.isGrpPullback_baseChange_with_square F'.univ.A Q.B lam β hpb (spMap (σ.toRingHom.comp (ev.comp ρ)))
  obtain ⟨-, ψ₀, hψ₀⟩ := GlobalTheory.T.isGrpPullback_baseChange_with_square Q.B Q.B (𝟙 _) (𝟙 _) (isGrpPullback_self Q.B) (spMap (ev.comp ρ))
  obtain ⟨-, ψσ, hψσ⟩ := GlobalTheory.T.isGrpPullback_baseChange_with_square Q.B Q.B (𝟙 _) (𝟙 _) (isGrpPullback_self Q.B)
    (spMap (σ.toRingHom.comp (ev.comp ρ)))
  rw [Category.comp_id] at hψ₀ hψσ
  refine ⟨spMap (σ.toRingHom.comp (ev.comp ρ)) ≫ lam, f ≫ pullback.fst Q.B.hom _ ≫ β, f₂ ≫ φσ₂, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨P₀, hP₀⟩ := hdef
    have hk : (σ.toRingHom).comp k₀.subtype = k₀.subtype := by
      ext r; exact hσ r r.2
    have hk' : spMap σ.toRingHom ≫ spMap k₀.subtype = spMap k₀.subtype := by
      rw [← spMap_comp', hk]
    rw [spMap_comp' (ev.comp ρ) σ.toRingHom]
    simp only [Category.assoc]
    rw [← hP₀, ← Category.assoc, hk']
  · simpa only [Category.id_comp] using hf.comp hpbσ
  · exact ⟨by rw [Category.assoc, hsqσ.1, ← Category.assoc, hfs.1, Category.assoc],
      by rw [Category.assoc, hsqσ.2, ← Category.assoc, hfs.2, Category.assoc]⟩
  · have e0 : φ₀₂ = ψ₀ ≫ β₂ := by
      apply pullback.hom_ext
      · change φ₀₂ ≫ (fst F'.univ.A F'.univ.A).left = (ψ₀ ≫ β₂) ≫ (fst F'.univ.A F'.univ.A).left
        rw [hsq0.1, Category.assoc, hsq.1, ← Category.assoc ψ₀, hψ₀.1, Category.assoc]
      · change φ₀₂ ≫ (snd F'.univ.A F'.univ.A).left = (ψ₀ ≫ β₂) ≫ (snd F'.univ.A F'.univ.A).left
        rw [hsq0.2, Category.assoc, hsq.2, ← Category.assoc ψ₀, hψ₀.2, Category.assoc]
    have eσ : φσ₂ = ψσ ≫ β₂ := by
      apply pullback.hom_ext
      · change φσ₂ ≫ (fst F'.univ.A F'.univ.A).left = (ψσ ≫ β₂) ≫ (fst F'.univ.A F'.univ.A).left
        rw [hsqσ.1, Category.assoc, hsq.1, ← Category.assoc ψσ, hψσ.1, Category.assoc]
      · change φσ₂ ≫ (snd F'.univ.A F'.univ.A).left = (ψσ ≫ β₂) ≫ (snd F'.univ.A F'.univ.A).left
        rw [hsqσ.2, Category.assoc, hsq.2, ← Category.assoc ψσ, hψσ.2, Category.assoc]
    have hP := F'.univ.isLB
    have hΛ : (abelian₂ Q.B Q.M.L).IsLB := LB.isLB_linComb (RigLB.isLB Q.M) _ _
    have hA := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hLB ψ₀ (a' := ψ₀ ≫ β₂) rfl
    have hB := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hLB (f₂ ≫ ψσ) (a' := f₂ ≫ φσ₂) (by rw [eσ, Category.assoc])
    rw [e0]
    exact LBIso.trans (pull_isLB hP _) (pull_isLB hΛ _) (pull_isLB hP _) (LBIso.symm hA)
      (LBIso.trans (pull_isLB hΛ _) (pull_isLB hΛ _) (pull_isLB hP _) (hfL ψ₀ ψσ hψ₀ hψσ) hB)
  · have h5 := congrArg (· ≫ β) hfp
    simp only [Category.assoc] at h5
    exact h5.symm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxPoincareSeriesAtThetaSetupPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.GApprox

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem sc_pos {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c : CTrait X₁ p z₁) : 0 < c.sc := by
  set u := algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ with hu
  have h0 : c.T.ϖ ≠ 0 := c.T.irr.ne_zero
  have hu0 : u ≠ 0 := by
    rw [hu]; exact (IsFractionRing.injective c.T.V (FractionRing c.T.V)).ne_iff' (map_zero _) |>.2 h0
  have hι0 : c.ι u ≠ 0 := (map_ne_zero c.ι).2 hu0
  have hle : ‖c.ι u‖ ≤ 1 := (c.int u).2 ⟨_, rfl⟩
  have hlt : ‖c.ι u‖ < 1 := by
    refine lt_of_le_of_ne hle fun h1 => ?_
    have : ‖c.ι u⁻¹‖ ≤ 1 := by rw [map_inv₀, norm_inv, h1, inv_one]
    obtain ⟨v, hv⟩ := (c.int _).1 this
    apply c.T.irr.not_isUnit
    refine IsUnit.of_mul_eq_one v ?_
    apply IsFractionRing.injective c.T.V (FractionRing c.T.V)
    rw [map_mul, hv, ← hu, mul_inv_cancel₀ hu0, map_one]
  have hpos : 0 < ‖c.ι u‖ := norm_pos_iff.2 hι0
  unfold CTrait.sc
  rw [← hu]
  linarith [Real.log_neg hpos hlt]

theorem sc_evalZ_eq_of_equiv {φ : InvFun ℤ} {X Y : Type} [AddCommGroup X] [AddCommGroup Y] [Module.Finite ℤ X]
    [Module.Finite ℤ Y] (hP : IsPolFanOn id φ X) {β : LinearMap.BilinForm ℤ X} (hs : ∀ a b, β a b = β b a)
    (hp : ∀ x, 0 ≤ β x x) {β' : LinearMap.BilinForm ℤ Y} {s s' : ℝ} (hs0 : 0 ≤ s) (hs' : 0 < s') (e : X ≃ₗ[ℤ] Y)
    (he : ∀ a b, s * β a b = s' * β' (e a) (e b)) : s * φ.evalZ β = s' * φ.evalZ β' := by
  have hmem : toReal β ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) :=
    StrictData.toReal_mem_psdCone (mem_balForms_int.2 hs) hp
  have hform : toReal (pull e.toLinearMap β') = (s / s') • toReal β := by
    refine LinearMap.ext₂ fun a b => ?_
    have := he a b
    simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul, LinearEquiv.coe_coe]
    field_simp
    linarith
  have h1 : φ.evalZ (pull e.toLinearMap β') = φ.evalZ β' := evalZ_pull φ e.surjective _
  rw [← h1, ← evalR_toReal φ (pull _ _), hform, hP.homog _ hmem _ (div_nonneg hs0 hs'.le), evalR_toReal]
  field_simp

theorem sc_evalZ_eq {X₁ : Setup F W i} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} {φ : InvFun ℤ} (hpol : IsPolFan id g φ)
    (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)) (y : Φ.Y) (c : CTrait X₁ p z₁)
    (e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X) (he : ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) :
    Φ.sc y * @InvFun.evalZ ℤ _ φ (Φ.X y) _ (Φ.mod y) (Φ.fin y) (Φ.β y) = c.sc * φ.evalZ c.T.β := by
  have hm : Φ.mod y = AddCommGroup.toIntModule _ := Subsingleton.elim _ _
  have hrk : Module.finrank ℤ (Φ.X y) ≤ g := by
    convert Φ.rank_le y <;> first | rfl | exact hm.symm
  have hP : IsPolFanOn id φ (Φ.X y) := hpol _ hrk
  convert sc_evalZ_eq_of_equiv hP (Φ.bal y).1 (fun x => by
      by_cases hx : x = 0
      · simp [hx]
      · exact (Φ.pos y x hx).le) (Φ.sc_pos y).le (sc_pos c) e he

end GlobalTheory.Poinc.GApprox

namespace GlobalTheory.Poinc.GApprox

theorem exists_hasSupports_int (q : ℕ) (φ : InvFun ℤ) (hpol : IsPolFan id q φ) :
    ∃ d, 1 ≤ d ∧ HasSupports (id : ℤ → ℤ) q φ d := by
  refine exists_hasSupports ℤ id q φ hpol fun X _ iM _ _ hX r γ hγ => ?_
  obtain rfl : iM = AddCommGroup.toIntModule X := Subsingleton.elim _ _
  have : Module.Free ℤ X := inferInstance
  exact exists_supports_int φ X (hpol X hX) r γ hγ

end GlobalTheory.Poinc.GApprox

open GlobalTheory.Poinc.GApprox in
theorem GlobalTheory.Poinc.exists_approxAt : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0})
    (i : F.X ⟶ Z) (X₁ : Setup F W i), IsE8 W → ThetaInt F W i → 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ →
    ∃ d : ℕ, 1 ≤ d ∧ ApproxAt X₁ φ d := by
  intro g n F W Z i X₁ hE hT hg φ hpol
  obtain ⟨d₀, hd₀, hsup⟩ := exists_hasSupports_int g φ hpol
  have hW : 0 < W 0 0 := by
    have := hE.1.diag_pos (i := 0)
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply] at this
    have h2 : (0 : ℤ) < W 0 0 + W 0 0 := by exact_mod_cast this
    omega
  have hN : 3 ≤ X₁.S.r * X₁.S.N := by
    have h1 := X₁.big.2.2
    have h2 : 1 ≤ X₁.S.N ^ X₁.S.g * X₁.S.g.factorial :=
      Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ (by have := X₁.S.N_ge; omega))
        (Nat.factorial_ne_zero _))
    omega
  refine ⟨(W 0 0).toNat * d₀, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  intro p _ z₁ c₀ e
  have hcl : IsClosed ({z₁} : Set X₁.M.Z) := c₀.cen ▸ isClosed_singleton_cPt c₀.y
  obtain ⟨Φ, hM, hL, hR⟩ := GlobalTheory.T.exists_classicalTrait_system_at_closedPoint g n F W Z i hE hT X₁ p z₁ hcl
  have hF := _root_.GlobalTheory.Poinc.four_of_classical g n F W Z i X₁ p z₁ Φ hE.1 hR
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  haveI : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  have hA := approx_of_fpre ℤ id bddAct_int_and_cm.1 g φ hpol d₀ hsup 7 W hE.1 (X₁.S.r * X₁.S.N) p hN _ Φ hL hF
  obtain ⟨y₀, hev₀, e₀, he₀⟩ := hM c₀
  obtain ⟨f, hf1, hf2⟩ := hA y₀ e
  have key : ∀ (y : Φ.Y) (c : CTrait X₁ p z₁) (e' : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X),
      (∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e' a) (e' b)) →
      Φ.sc y * (((W 0 0).toNat * d₀ : ℕ) * @InvFun.evalZ ℤ _ φ (Φ.X y) _ (Φ.mod y) (Φ.fin y) (Φ.β y)) = c.sc * (((W 0 0).toNat * d₀ : ℕ) * φ.evalZ c.T.β) := by
    intro y c e' h
    have := sc_evalZ_eq hpol Φ y c e' h
    calc Φ.sc y * (((W 0 0).toNat * d₀ : ℕ) * @InvFun.evalZ ℤ _ φ (Φ.X y) _ (Φ.mod y) (Φ.fin y) (Φ.β y))
        = ((W 0 0).toNat * d₀ : ℕ) * (Φ.sc y * @InvFun.evalZ ℤ _ φ (Φ.X y) _ (Φ.mod y) (Φ.fin y) (Φ.β y)) := by ring
      _ = c.sc * (((W 0 0).toNat * d₀ : ℕ) * φ.evalZ c.T.β) := by rw [this]; ring
  refine ⟨f, ?_, fun c => ?_⟩
  · rw [← hev₀ f, hf1, key y₀ c₀ e₀ he₀]
  · obtain ⟨y, hev, e', he'⟩ := hM c
    rcases hf2 y with h | ⟨h, hh, hle⟩
    · left; rw [← hev f, ← key y c e' he']; exact h
    · right; exact ⟨h, hh, by rw [← hev f, ← hev h]; exact hle⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorNonKltAtPointsNotContainingCentreStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divisor_nonKlt_at_points_not_containing_centre : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (P : Finset X) (z : X) (k : ℕ) (h : ℚ), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsQCart D → (∀ x ∈ P, IsClosed ({x} : Set X) ∧ z ⤳ x) → 1 ≤ k → topologicalKrullDim (closure ({z} : Set X)) = k → (z = genericPoint X ∨ IsNkltCentre p n (Δ + D) z) → 0 < h → (P.card : ℚ) * (k : ℚ) ^ k < h ^ k * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin k => N : ℤ) → ∃ (B : X → ℚ) (δ₀ : ℚ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧ QNum p N h B ∧ Off B z ∧ (∀ δ : ℚ, 0 ≤ δ → δ ≤ δ₀ → ∀ x ∈ P, ¬ KltAt p n (Δ + (1 - δ) • D + B) x) ∧ (∀ y, ¬ z ⤳ y → ∀ a : ℚ, 0 ≤ a → KltAt p n (Δ + a • D) y → KltAt p n (Δ + a • D + B) y) := by
  first | exact @GlobalTheory.PairStep.exists_step_divisor | exact GlobalTheory.PairStep.exists_step_divisor | (intros; apply GlobalTheory.PairStep.exists_step_divisor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRepRosatiOrderActionsSiegelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_rep_rosati_orderActions_siegel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (c : SiegPre h M ζ s₁), Out.RelAmple c.A c.diag → ∃ (H : Scheme.{0}) (πH : H ⟶ S) (AH : Over H) (_ : GrpObj AH) (_ : IsCommMonObj AH) (φH : AH.left ⟶ c.A.left) (φ₂H : (G2 AH).left ⟶ (G2 c.A).left) (actH : OActN D.O AH), IsFinite πH ∧ IsAbelianScheme AH ∧ IsGrpPullback AH c.A πH φH ∧ IsSquare φH φ₂H ∧ RosatiFor D actH (c.P.pull φ₂H) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ c.A.left) (φ₂ : (G2 AT).left ⟶ (G2 c.A).left) (act : OActN D.O AT), IsGrpPullback AT c.A g φ → IsSquare φ φ₂ → RosatiFor D act (c.P.pull φ₂) → ∃! z : T ⟶ H, z ≫ πH = g ∧ ∃ ψ : AT.left ⟶ AH.left, IsGrpPullback AT AH z ψ ∧ ψ ≫ φH = φ ∧ ∀ a : D.O, (act.act a).left ≫ ψ = ψ ≫ (actH.act a).left := by
  first | (exact @GlobalTheory.UPel.HT.exists_finite_rep_oActN_rosati) | (exact GlobalTheory.UPel.HT.exists_finite_rep_oActN_rosati) | (intros; apply GlobalTheory.UPel.HT.exists_finite_rep_oActN_rosati  <;> assumption)
end

